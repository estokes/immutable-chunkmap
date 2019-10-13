use std::{
    borrow::Borrow,
    cmp::{Ord, Ordering},
    fmt::{self, Debug, Formatter},
    iter, mem,
    collections::{vec_deque, VecDeque},
};

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
pub(crate) const SIZE: usize = 512;

pub(crate) enum UpdateChunk<Q: Ord, K: Ord + Clone + Borrow<Q>, V: Clone, D> {
    UpdateLeft(Vec<(Q, D)>),
    UpdateRight(Vec<(Q, D)>),
    Created(Chunk<K, V>),
    Updated {
        elts: Chunk<K, V>,
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
        elts: Chunk<K, V>,
        overflow: Option<(K, V)>,
        previous: Option<V>,
    },
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Chunk<K, V> {
    keys: VecDeque<K>,
    vals: VecDeque<V>,
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

impl<K, V> Chunk<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    pub(crate) fn singleton(k: K, v: V) -> Self {
        let mut t = Chunk::with_capacity(1);
        t.keys.push_back(k);
        t.vals.push_back(v);
        t
    }

    pub(crate) fn empty() -> Self {
        Chunk {
            keys: VecDeque::new(),
            vals: VecDeque::new(),
        }
    }

    fn with_capacity(n: usize) -> Self {
        Chunk {
            keys: VecDeque::with_capacity(n),
            vals: VecDeque::with_capacity(n),
        }
    }

    pub(crate) fn get_local<Q: ?Sized + Ord>(&self, k: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
    {
        let (f, b) = self.keys.as_slices();
        match f.binary_search_by_key(&k, |k| k.borrow()) {
            Ok(i) => Some(i),
            Err(i) => {
                if i < f.len() {
                    None
                } else {
                    match b.binary_search_by_key(&k, |k| k.borrow()) {
                        Ok(i) => Some(i + f.len()),
                        Err(_) => None
                    }
                }
            }
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
                    let (f, b) = self.keys.as_slices();
                    match f.binary_search_by_key(&k, |k| k.borrow()) {
                        Result::Ok(i) => Loc::Here(i),
                        Result::Err(i) => {
                            if i < f.len() {
                                Loc::NotPresent(i)
                            } else {
                                match b.binary_search_by_key(&k, |k| k.borrow()) {
                                    Result::Ok(i) => Loc::Here(i + f.len()),
                                    Result::Err(i) => Loc::NotPresent(i + f.len())
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // chunk must be sorted
    pub(crate) fn update_chunk<Q, D, F>(
        &self,
        mut chunk: Vec<(Q, D)>,
        leaf: bool,
        f: &mut F,
    ) -> UpdateChunk<Q, K, V, D>
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        assert!(chunk.len() <= SIZE && chunk.len() > 0);
        if self.len() == 0 {
            let mut elts = Chunk::empty();
            let (keys, vals): (VecDeque<_>, VecDeque<_>) =
                chunk.drain(0..).filter_map(|(q, d)| f(q, d, None)).unzip();
            elts.keys = keys;
            elts.vals = vals;
            UpdateChunk::Created(elts)
        } else {
            let full = !leaf || self.len() >= SIZE;
            let in_left = self.get(&chunk[chunk.len() - 1].0) == Loc::InLeft;
            let in_right = self.get(&chunk[0].0) == Loc::InRight;
            if full && in_left {
                UpdateChunk::UpdateLeft(chunk)
            } else if full && in_right {
                UpdateChunk::UpdateRight(chunk)
            } else if leaf && (in_left || in_right) {
                let mut elts = self.clone();
                if in_left {
                    while let Some((k, v)) = chunk.pop().and_then(|(q, d)| f(q, d, None)) {
                        elts.keys.push_front(k);
                        elts.vals.push_front(v);
                    }
                } else {
                    for (k, v) in chunk.drain(0..).filter_map(|(q, d)| f(q, d, None)) {
                        elts.keys.push_back(k);
                        elts.vals.push_back(v);
                    }
                }
                let overflow_right = {
                    if elts.len() <= SIZE {
                        Vec::new()
                    } else {
                        elts.keys
                            .split_off(SIZE)
                            .into_iter()
                            .zip(elts.vals.split_off(SIZE).into_iter())
                            .collect::<Vec<_>>()
                    }
                };
                elts.keys.shrink_to_fit();
                elts.vals.shrink_to_fit();
                UpdateChunk::Updated {
                    elts,
                    update_left: Vec::new(),
                    update_right: Vec::new(),
                    overflow_right,
                }
            } else {
                let mut elts = self.clone();
                let mut not_done = Vec::new();
                let mut update_left = Vec::new();
                let mut update_right = Vec::new();
                let mut overflow_right = Vec::new();
                for (q, d) in chunk.drain(0..) {
                    if elts.len() == 0 {
                        not_done.push((q, d));
                        continue;
                    }
                    match elts.get(&q) {
                        Loc::Here(i) => {
                            match f(q, d, Some((&elts.keys[i], &elts.vals[i]))) {
                                None => {
                                    elts.keys.remove(i);
                                    elts.vals.remove(i);
                                }
                                Some((k, v)) => {
                                    elts.keys[i] = k;
                                    elts.vals[i] = v;
                                }
                            }
                        }
                        Loc::NotPresent(i) => {
                            if elts.len() < SIZE {
                                if let Some((k, v)) = f(q, d, None) {
                                    elts.keys.insert(i, k);
                                    elts.vals.insert(i, v);
                                }
                            } else {
                                if let Some((k, v)) = f(q, d, None) {
                                    overflow_right.push((
                                        elts.keys.pop_back().unwrap(),
                                        elts.vals.pop_back().unwrap(),
                                    ));
                                    elts.keys.insert(i, k);
                                    elts.vals.insert(i, v);
                                }
                            }
                        }
                        Loc::InLeft => {
                            if leaf && elts.keys.len() < SIZE {
                                if let Some((k, v)) = f(q, d, None) {
                                    elts.keys.push_front(k);
                                    elts.vals.push_front(v);
                                }
                            } else {
                                update_left.push((q, d))
                            }
                        }
                        Loc::InRight => {
                            if leaf && elts.len() < SIZE {
                                if let Some((k, v)) = f(q, d, None) {
                                    elts.keys.push_back(k);
                                    elts.vals.push_back(v);
                                }
                            } else {
                                update_right.push((q, d))
                            }
                        }
                    }
                }
                overflow_right.reverse();
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
                let mut elts = self.clone();
                let previous = {
                    if let Some((k, v)) = f(q, d, Some((&self.keys[i], &self.vals[i]))) {
                        elts.keys[i] = k;
                        Some(mem::replace(&mut elts.vals[i], v))
                    } else {
                        elts.keys.remove(i);
                        elts.vals.remove(i)
                    }
                };
                Update::Updated { elts, previous, overflow: None }
            }
            Loc::NotPresent(i) => {
                let mut elts = self.clone();
                if let Some((k, v)) = f(q, d, None) {
                    elts.keys.insert(i, k);
                    elts.vals.insert(i, v);
                }
                let overflow = {
                    if elts.len() <= SIZE {
                        None
                    } else {
                        elts.keys
                            .pop_back()
                            .and_then(|k| elts.vals.pop_back().map(move |v| (k, v)))
                    }
                };
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
                    let mut elts = self.clone();
                    if let Some((k, v)) = f(q, d, None) {
                        match loc {
                            Loc::InLeft => {
                                elts.keys.push_front(k);
                                elts.vals.push_front(v);
                            }
                            Loc::InRight => {
                                elts.keys.push_back(k);
                                elts.vals.push_back(v);
                            }
                            _ => unreachable!("bug"),
                        }
                    };
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
                c1.get_local(&k).and_then(|j| {
                    f(k, &c0.vals[i], &c1.vals[j]).map(|v| (k.clone(), v))
                })
            }))
        }
    }

    pub(crate) fn remove_elt_at(&self, i: usize) -> Self {
        let mut elts = self.clone();
        elts.keys.remove(i);
        elts.vals.remove(i);
        elts
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

impl<K, V> IntoIterator for Chunk<K, V>
where
    K: Ord,
{
    type Item = (K, V);
    type IntoIter = iter::Zip<vec_deque::IntoIter<K>, vec_deque::IntoIter<V>>;
    fn into_iter(self) -> Self::IntoIter {
        self.keys.into_iter().zip(self.vals)
    }
}

impl<'a, K, V> IntoIterator for &'a Chunk<K, V>
where
    K: 'a + Ord,
    V: 'a,
{
    type Item = (&'a K, &'a V);
    type IntoIter = iter::Zip<vec_deque::Iter<'a, K>, vec_deque::Iter<'a, V>>;
    fn into_iter(self) -> Self::IntoIter {
        (&self.keys).into_iter().zip(&self.vals)
    }
}
