use std::{
    borrow::Borrow,
    cmp::{Ord, Ordering, min},
    fmt::{self, Debug, Formatter},
    cell::RefCell,
    collections::HashMap,
    iter, slice, mem,
};
use cached_arc::{self, Cacheable, Discriminant, Arc};

#[derive(PartialEq)]
pub(crate) enum Loc {
    InRight,
    InLeft,
    NotPresent(usize),
    Here(usize),
}

/*
elts is a sorted array of pairs, increasing the SIZE has several effects;
-- decreases the height of the tree for a given number of
elements, decreasing the amount of indirection necessary to
get to any given key.
-- decreases the number of objects allocated on the heap each
time a key is added or removed
-- increases the size of each allocation
-- icreases the overall amount of memory allocated for each change to the tree
 */
pub(crate) const SIZE: usize = 8124;

pub(crate) enum UpdateChunk<Q: Ord, K: Ord + Clone + Borrow<Q>, V: Clone, D> {
    UpdateLeft(Vec<(Q, D)>),
    UpdateRight(Vec<(Q, D)>),
    Updated {
        elts: Arc<Chunk<K, V>>,
        update_left: Vec<(Q, D)>,
        update_right: Vec<(Q, D)>,
        overflow_right: Vec<(K, V)>,
    },
    Removed {
        not_done: Vec<(Q, D)>,
        update_left: Vec<(Q, D)>,
        update_right: Vec<(Q, D)>,
    },
}

pub(crate) enum Update<Q: Ord, K: Ord + Clone + Borrow<Q>, V: Clone, D> {
    UpdateLeft(Q, D),
    UpdateRight(Q, D),
    Updated {
        elts: Arc<Chunk<K, V>>,
        overflow: Option<(K, V)>,
        previous: Option<V>,
    },
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Chunk<K, V> {
    keys: Vec<K>,
    vals: Vec<V>,
}

impl<K, V> Debug for Chunk<K, V>
where
    K: Debug + Ord + Clone,
    V: Debug + Clone,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_map().entries(self.into_iter()).finish()
    }
}

thread_local! {
    static DISCRIMINANT_TABLE:
    RefCell<HashMap<(usize, usize), Discriminant>> =
        RefCell::new(HashMap::new());
}

// Why This is Safe.
//
// 1. We clear the chunks when they are inserted into the cache.
//    a. so we drop all user supplied data exactly when it would
//       be dropped in the absence of caching.
//    b. and we don't hold onto any references which might become
//       invalid while the element is cached.
// 2. We use discriminants to guarantee that chunks we get from
//    the cache are isomorphic to the requested Chunk<K, V> type.
//    a. The key determinant of isomorphism between different Chunk
//       types is the size of the K and V types.
//       Any two Chunk<A, B> and Chunk<X, Y>
//       where size_of(A) == size_of(X) && size_of(B) == size_of(Y)
//       are isomorphic provided they are empty.
unsafe impl<K, V> Cacheable for Chunk<K, V>
where
    K: Ord + Clone,
    V: Clone
{
    fn type_id() -> Discriminant {
        DISCRIMINANT_TABLE.with(|dtbl| {
            let mut dtbl = dtbl.borrow_mut();
            *dtbl.entry((mem::size_of::<K>(), mem::size_of::<V>()))
                .or_insert_with(cached_arc::new_discriminant)
        })
    }

    // CR estokes: need to compute the hit rate
    fn limit() -> usize {
        1000
    }

    fn reinit(&mut self) -> bool {
        self.keys.clear();
        self.vals.clear();
        true
    }
}

impl<K, V> Chunk<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    pub(crate) fn empty() -> Arc<Self> {
        Arc::new(|| Chunk {
            keys: Vec::new(),
            vals: Vec::new(),
        })
    }

    pub(crate) fn with_empty<F: FnOnce(&mut Chunk<K, V>) -> ()>(f: F) -> Arc<Self> {
        let mut arc = Chunk::empty();
        let arc_ref = Arc::get_mut(&mut arc).unwrap();
        f(arc_ref);
        arc
    }

    pub(crate) fn singleton(k: K, v: V) -> Arc<Self> {
        Chunk::with_empty(move |t_ref| {
            t_ref.keys.push(k);
            t_ref.vals.push(v);
        })
    }

    pub(crate) fn create_with<Q, D, F>(chunk: Vec<(Q, D)>, f: &mut F) -> Arc<Self>
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        Chunk::with_empty(|elts| {
            for (k, v) in chunk.into_iter().filter_map(|(q, d)| f(q, d, None)) {
                elts.keys.push(k);
                elts.vals.push(v);
            }
        })
    }

    pub(crate) fn get_local<Q: ?Sized + Ord>(&self, k: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
    {
        match self.keys.binary_search_by_key(&k, |k| k.borrow()) {
            Ok(i) => Some(i),
            Err(_) => None,
        }
    }

    pub(crate) fn get<Q: ?Sized + Ord>(&self, k: &Q) -> Loc
    where
        K: Borrow<Q>,
    {
        let len = self.len();
        if len == 0 {
            Loc::NotPresent(0)
        } else {
            let first = k.cmp(&self.keys[0].borrow());
            let last = k.cmp(&self.keys[len - 1].borrow());
            match (first, last) {
                (Ordering::Equal, _) => Loc::Here(0),
                (_, Ordering::Equal) => Loc::Here(len - 1),
                (Ordering::Less, _) => Loc::InLeft,
                (_, Ordering::Greater) => Loc::InRight,
                (Ordering::Greater, Ordering::Less) => {
                    match self.keys.binary_search_by_key(&k, |k| k.borrow()) {
                        Result::Ok(i) => Loc::Here(i),
                        Result::Err(i) => Loc::NotPresent(i),
                    }
                }
            }
        }
    }

    fn overflow_to(&mut self, to: &mut Vec<(K, V)>) {
        if self.len() > SIZE {
            to.extend(
                self.keys.split_off(SIZE).into_iter().zip(
                    self.vals.split_off(SIZE).into_iter()
                )
            )
        }
    }
    
    // invariant: chunk is sorted and deduped
    pub(crate) fn update_chunk<Q, D, F>(
        &self,
        chunk: Vec<(Q, D)>,
        leaf: bool,
        f: &mut F,
    ) -> UpdateChunk<Q, K, V, D>
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        assert!(chunk.len() <= SIZE && chunk.len() > 0 && self.len() > 0);
        let full = !leaf || self.len() >= SIZE;
        let in_left = self.get(&chunk[chunk.len() - 1].0) == Loc::InLeft;
        let in_right = self.get(&chunk[0].0) == Loc::InRight;
        if full && in_left {
            UpdateChunk::UpdateLeft(chunk)
        } else if full && in_right {
            UpdateChunk::UpdateRight(chunk)
        } else if leaf && (in_left || in_right) {
            let (mut keys, mut vals): (Vec<K>, Vec<V>) =
                chunk.into_iter().filter_map(|(q, d)| f(q, d, None)).unzip();
            let mut overflow_right = Vec::new();
            let elts = {
                if in_right {
                    Chunk::with_empty(|elts| {
                        elts.keys.extend_from_slice(&self.keys);
                        elts.vals.extend_from_slice(&self.vals);
                        elts.keys.append(&mut keys);
                        elts.vals.append(&mut vals);
                        elts.overflow_to(&mut overflow_right);
                    })
                } else {
                    Chunk::with_empty(|elts| {
                        elts.keys.append(&mut keys);
                        elts.vals.append(&mut vals);
                        elts.keys.extend_from_slice(&self.keys);
                        elts.vals.extend_from_slice(&self.vals);
                        elts.overflow_to(&mut overflow_right);
                    })
                }
            };
            UpdateChunk::Updated {
                elts,
                update_left: Vec::new(),
                update_right: Vec::new(),
                overflow_right,
            }
        } else {
            #[inline(always)]
            fn copy_up_to<K, V>(
                t: &Chunk<K, V>,
                elts: &mut Chunk<K, V>,
                overflow_right: &mut Vec<(K, V)>,
                m: &mut usize,
                i: usize
            ) where K: Ord + Clone, V: Clone {
                let n = min(i - *m, SIZE - elts.len());
                if n > 0 {
                    elts.keys.extend_from_slice(&t.keys[*m..*m + n]);
                    elts.vals.extend_from_slice(&t.vals[*m..*m + n]);
                    *m += n;
                }
                if *m < i {
                    overflow_right.extend(
                        t.keys.as_slice()[*m..i].iter().cloned()
                            .zip(t.vals.as_slice()[*m..i].iter().cloned())
                    );
                    *m = i;
                }
            }
            // invariant: don't cross the streams.
            let mut not_done = Vec::new();
            let mut update_left = Vec::new();
            let mut update_right = Vec::new();
            let mut overflow_right = Vec::new();
            let mut m = 0;
            let elts = Chunk::with_empty(|elts| {
                let mut chunk = chunk.into_iter();
                loop {
                    if m == self.len() && elts.len() == 0 {
                        not_done.extend(chunk);
                        break;
                    }
                    match chunk.next() {
                        None => {
                            copy_up_to(
                                self, elts, &mut overflow_right, &mut m, self.len()
                            );
                            break;
                        }
                        Some((q, d)) => {
                            match self.get(&q) {
                                Loc::Here(i) => {
                                    copy_up_to(
                                        self, elts, &mut overflow_right, &mut m, i
                                    );
                                    let r = f(q, d, Some((&self.keys[i], &self.vals[i])));
                                    if let Some((k, v)) = r {
                                        if elts.len() < SIZE {
                                            elts.keys.push(k);
                                            elts.vals.push(v);
                                        } else {
                                            overflow_right.push((k, v))
                                        }
                                    }
                                    // self[i] was replaced or deleted, skip it
                                    m += 1;
                                }
                                Loc::NotPresent(i) => {
                                    copy_up_to(
                                        self, elts, &mut overflow_right, &mut m, i
                                    );
                                    if let Some((k, v)) = f(q, d, None) {
                                        if elts.len() < SIZE {
                                            elts.keys.push(k);
                                            elts.vals.push(v);
                                        } else {
                                            overflow_right.push((k, v));
                                        }
                                    }
                                }
                                Loc::InLeft => {
                                    if leaf && elts.len() < SIZE {
                                        if let Some((k, v)) = f(q, d, None) {
                                            elts.keys.push(k);
                                            elts.vals.push(v);
                                        }
                                    } else {
                                        update_left.push((q, d))
                                    }
                                }
                                Loc::InRight => {
                                    let len = self.len();
                                    copy_up_to(
                                        self, elts, &mut overflow_right, &mut m, len
                                    );
                                    if leaf && elts.len() < SIZE {
                                        let (mut keys, mut vals): (Vec<K>, Vec<V>) =
                                            iter::once((q, d)).chain(chunk)
                                            .filter_map(|(q, d)| f(q, d, None))
                                            .unzip();
                                        elts.keys.append(&mut keys);
                                        elts.vals.append(&mut vals);
                                        elts.overflow_to(&mut overflow_right);
                                    } else {
                                        update_right.push((q, d));
                                        update_right.extend(chunk);
                                    }
                                    break;
                                }
                            }
                        }
                    }
                }
            });
            if elts.len() > 0 {
                assert_eq!(not_done.len(), 0);
                UpdateChunk::Updated {
                    elts,
                    update_left,
                    update_right,
                    overflow_right,
                }
            } else {
                assert_eq!(overflow_right.len(), 0);
                UpdateChunk::Removed {
                    not_done,
                    update_left,
                    update_right,
                }
            }
        }
    }

    pub(crate) fn update<Q, D, F>(
        &self,
        q: Q,
        d: D,
        leaf: bool,
        f: &mut F,
    ) -> Update<Q, K, V, D>
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        match self.get(&q) {
            Loc::Here(i) => {
                let elts = Chunk::with_empty(|elts| {
                    elts.keys.extend_from_slice(&self.keys[0..i]);
                    elts.vals.extend_from_slice(&self.vals[0..i]);
                    if let Some((k, v)) = f(q, d, Some((&self.keys[i], &self.vals[i]))) {
                        elts.keys.push(k);
                        elts.vals.push(v);
                    }
                    if i + 1 < self.len() {
                        elts.keys.extend_from_slice(&self.keys[i + 1..self.len()]);
                        elts.vals.extend_from_slice(&self.vals[i + 1..self.len()]);
                    }
                });
                Update::Updated {
                    elts,
                    overflow: None,
                    previous: Some(self.vals[i].clone()),
                }
            }
            Loc::NotPresent(i) => {
                let mut overflow = None;
                let elts = Chunk::with_empty(|elts| {
                    elts.keys.extend_from_slice(&self.keys[0..i]);
                    elts.vals.extend_from_slice(&self.vals[0..i]);
                    if let Some((k, v)) = f(q, d, None) {
                        elts.keys.push(k);
                        elts.vals.push(v);
                    }
                    elts.keys.extend_from_slice(&self.keys[i..self.len()]);
                    elts.vals.extend_from_slice(&self.vals[i..self.len()]);
                    if elts.len() > SIZE {
                        overflow = elts.keys
                            .pop()
                            .and_then(|k| elts.vals.pop().map(move |v| (k, v)))
                    }
                });
                Update::Updated {
                    elts,
                    overflow,
                    previous: None,
                }
            }
            loc @ Loc::InLeft | loc @ Loc::InRight => {
                if !leaf || self.len() == SIZE {
                    match loc {
                        Loc::InLeft => Update::UpdateLeft(q, d),
                        Loc::InRight => Update::UpdateRight(q, d),
                        Loc::Here(..) | Loc::NotPresent(..) => unreachable!(),
                    }
                } else {
                    let elts = Chunk::with_empty(|elts| {
                        match loc {
                            Loc::InLeft => {
                                if let Some((k, v)) = f(q, d, None) {
                                    elts.keys.push(k);
                                    elts.vals.push(v);
                                }
                                elts.keys.extend_from_slice(&self.keys[0..self.len()]);
                                elts.vals.extend_from_slice(&self.vals[0..self.len()]);
                            }
                            Loc::InRight => {
                                elts.keys.extend_from_slice(&self.keys[0..self.len()]);
                                elts.vals.extend_from_slice(&self.vals[0..self.len()]);
                                if let Some((k, v)) = f(q, d, None) {
                                    elts.keys.push(k);
                                    elts.vals.push(v);
                                }
                            }
                            _ => unreachable!("bug"),
                        }
                    });
                    Update::Updated {
                        elts,
                        overflow: None,
                        previous: None,
                    }
                }
            }
        }
    }

    pub(crate) fn intersect<F>(
        c0: &Chunk<K, V>,
        c1: &Chunk<K, V>,
        r: &mut Vec<(K, V)>,
        f: &mut F,
    ) where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        if c0.len() > 0 && c1.len() > 0 {
            let (c0, c1) = if c0.len() < c1.len() {
                (c0, c1)
            } else {
                (c1, c0)
            };
            r.extend(c0.keys.iter().enumerate().filter_map(|(i, k)| {
                match c1.keys.binary_search(&k) {
                    Err(_) => None,
                    Ok(j) => f(k, &c0.vals[i], &c1.vals[j]).map(|v| (k.clone(), v)),
                }
            }))
        }
    }

    pub(crate) fn remove_elt_at(&self, i: usize) -> Arc<Self> {
        Chunk::with_empty(|elts| {
            let len = self.len();
            if len == 0 {
                panic!("can't remove from an empty chunk")
            } else if len == 1 {
                assert_eq!(i, 0);
            } else if i == 0 {
                elts.keys.extend_from_slice(&self.keys[1..len]);
                elts.vals.extend_from_slice(&self.vals[1..len]);
            } else if i == len - 1 {
                elts.keys.extend_from_slice(&self.keys[0..len - 1]);
                elts.vals.extend_from_slice(&self.vals[0..len - 1]);
            } else {
                elts.keys.extend_from_slice(&self.keys[0..i]);
                elts.keys.extend_from_slice(&self.keys[i + 1..len]);
                elts.vals.extend_from_slice(&self.vals[0..i]);
                elts.vals.extend_from_slice(&self.vals[i + 1..len]);
            }
        })
    }

    pub(crate) fn min_max_key(&self) -> Option<(K, K)> {
        if self.len() == 0 {
            None
        } else {
            Some((self.keys[0].clone(), self.keys[self.len() - 1].clone()))
        }
    }

    pub(crate) fn min_elt(&self) -> Option<(&K, &V)> {
        if self.len() == 0 {
            None
        } else {
            Some((&self.keys[0], &self.vals[0]))
        }
    }

    pub(crate) fn max_elt(&self) -> Option<(&K, &V)> {
        if self.len() == 0 {
            None
        } else {
            let last = self.len() - 1;
            Some((&self.keys[last], &self.vals[last]))
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.keys.len()
    }

    pub(crate) fn key(&self, i: usize) -> &K {
        &self.keys[i]
    }

    pub(crate) fn val(&self, i: usize) -> &V {
        &self.vals[i]
    }

    pub(crate) fn kv(&self, i: usize) -> (&K, &V) {
        (&self.keys[i], &self.vals[i])
    }

    pub(crate) fn to_vec(&self) -> Vec<(K, V)> {
        self.into_iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }
}

impl<'a, K, V> IntoIterator for &'a Chunk<K, V>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
{
    type Item = (&'a K, &'a V);
    type IntoIter = iter::Zip<slice::Iter<'a, K>, slice::Iter<'a, V>>;
    fn into_iter(self) -> Self::IntoIter {
        (&self.keys).into_iter().zip(&self.vals)
    }
}
