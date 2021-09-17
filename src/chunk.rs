use std::{
    borrow::Borrow,
    cmp::{min, Ord, Ordering},
    fmt::{self, Debug, Formatter},
    iter, mem, slice, vec,
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

-- decreases the height of the tree for a given number of elements,
   decreasing the amount of indirection necessary to get to any given
   key.

-- decreases the number of objects allocated on the heap each time a
   key is added or removed

-- increases the size of each allocation

-- icreases the overall amount of memory allocated for each change to
   the tree
*/
pub const DEFAULT_SIZE: usize = 512;

pub(crate) enum UpdateChunk<
    Q: Ord,
    K: Ord + Clone + Borrow<Q>,
    V: Clone,
    D,
    const SIZE: usize,
> {
    UpdateLeft(Vec<(Q, D)>),
    UpdateRight(Vec<(Q, D)>),
    Updated {
        elts: Chunk<K, V, SIZE>,
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

pub(crate) enum Update<Q: Ord, K: Ord + Clone + Borrow<Q>, V: Clone, D, const SIZE: usize>
{
    UpdateLeft(Q, D),
    UpdateRight(Q, D),
    Updated {
        elts: Chunk<K, V, SIZE>,
        overflow: Option<(K, V)>,
        previous: Option<V>,
    },
}

pub(crate) enum MutUpdate<Q: Ord, K: Ord + Clone + Borrow<Q>, V: Clone, D> {
    UpdateLeft(Q, D),
    UpdateRight(Q, D),
    Updated {
        overflow: Option<(K, V)>,
        previous: Option<V>,
    },
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Chunk<K, V, const SIZE: usize> {
    keys: Vec<K>,
    vals: Vec<V>,
}

impl<K, V, const SIZE: usize> Debug for Chunk<K, V, SIZE>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_map().entries(self.into_iter()).finish()
    }
}

impl<K, V, const SIZE: usize> Chunk<K, V, SIZE>
where
    K: Ord + Clone,
    V: Clone,
{
    pub(crate) fn singleton(k: K, v: V) -> Self {
        let mut t = Chunk::with_capacity(1);
        t.keys.push(k);
        t.vals.push(v);
        t
    }

    pub(crate) fn empty() -> Self {
        Chunk {
            keys: Vec::new(),
            vals: Vec::new(),
        }
    }

    pub(crate) fn create_with<Q, D, F>(mut chunk: Vec<(Q, D)>, f: &mut F) -> Self
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        let mut elts = Chunk::empty();
        let (keys, vals): (Vec<_>, Vec<_>) =
            chunk.drain(0..).filter_map(|(q, d)| f(q, d, None)).unzip();
        elts.keys = keys;
        elts.vals = vals;
        elts
    }

    fn with_capacity(n: usize) -> Self {
        Chunk {
            keys: Vec::with_capacity(n),
            vals: Vec::with_capacity(n),
        }
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
                self.keys
                    .split_off(SIZE)
                    .into_iter()
                    .zip(self.vals.split_off(SIZE).into_iter()),
            )
        }
    }

    // invariant: chunk is sorted and deduped
    pub(crate) fn update_chunk<Q, D, F>(
        &self,
        chunk: Vec<(Q, D)>,
        leaf: bool,
        f: &mut F,
    ) -> UpdateChunk<Q, K, V, D, SIZE>
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
            let mut elts = Chunk::with_capacity(self.len() + keys.len());
            if in_right {
                elts.keys.extend_from_slice(&self.keys);
                elts.vals.extend_from_slice(&self.vals);
                elts.keys.append(&mut keys);
                elts.vals.append(&mut vals);
                elts.overflow_to(&mut overflow_right);
            } else {
                elts.keys = keys;
                elts.vals = vals;
                elts.keys.extend_from_slice(&self.keys);
                elts.vals.extend_from_slice(&self.vals);
                elts.overflow_to(&mut overflow_right);
            }
            UpdateChunk::Updated {
                elts,
                update_left: Vec::new(),
                update_right: Vec::new(),
                overflow_right,
            }
        } else {
            #[inline(always)]
            fn copy_up_to<K, V, const SIZE: usize>(
                t: &Chunk<K, V, SIZE>,
                elts: &mut Chunk<K, V, SIZE>,
                overflow_right: &mut Vec<(K, V)>,
                m: &mut usize,
                i: usize,
            ) where
                K: Ord + Clone,
                V: Clone,
            {
                let n = min(i - *m, SIZE - elts.len());
                if n > 0 {
                    elts.keys.extend_from_slice(&t.keys[*m..*m + n]);
                    elts.vals.extend_from_slice(&t.vals[*m..*m + n]);
                    *m += n;
                }
                if *m < i {
                    overflow_right.extend(
                        t.keys.as_slice()[*m..i]
                            .iter()
                            .cloned()
                            .zip(t.vals.as_slice()[*m..i].iter().cloned()),
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
            let mut elts = Chunk::with_capacity(min(SIZE, self.len() + chunk.len()));
            let mut chunk = chunk.into_iter();
            loop {
                if m == self.len() && elts.len() == 0 {
                    not_done.extend(chunk);
                    break;
                }
                match chunk.next() {
                    None => {
                        copy_up_to(
                            self,
                            &mut elts,
                            &mut overflow_right,
                            &mut m,
                            self.len(),
                        );
                        break;
                    }
                    Some((q, d)) => {
                        match self.get(&q) {
                            Loc::Here(i) => {
                                copy_up_to(
                                    self,
                                    &mut elts,
                                    &mut overflow_right,
                                    &mut m,
                                    i,
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
                                    self,
                                    &mut elts,
                                    &mut overflow_right,
                                    &mut m,
                                    i,
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
                                    self,
                                    &mut elts,
                                    &mut overflow_right,
                                    &mut m,
                                    len,
                                );
                                if leaf && elts.len() < SIZE {
                                    let (mut keys, mut vals): (Vec<K>, Vec<V>) =
                                        iter::once((q, d))
                                            .chain(chunk)
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
    ) -> Update<Q, K, V, D, SIZE>
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        match self.get(&q) {
            Loc::Here(i) => {
                let mut elts = Chunk::with_capacity(self.len());
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
                Update::Updated {
                    elts,
                    overflow: None,
                    previous: Some(self.vals[i].clone()),
                }
            }
            Loc::NotPresent(i) => {
                let mut elts = Chunk::with_capacity(self.len() + 1);
                elts.keys.extend_from_slice(&self.keys[0..i]);
                elts.vals.extend_from_slice(&self.vals[0..i]);
                if let Some((k, v)) = f(q, d, None) {
                    elts.keys.push(k);
                    elts.vals.push(v);
                }
                elts.keys.extend_from_slice(&self.keys[i..self.len()]);
                elts.vals.extend_from_slice(&self.vals[i..self.len()]);
                let overflow = {
                    if elts.len() <= SIZE {
                        None
                    } else {
                        elts.keys
                            .pop()
                            .and_then(|k| elts.vals.pop().map(move |v| (k, v)))
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
                    let mut elts = Chunk::with_capacity(self.len() + 1);
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

    pub(crate) fn update_mut<Q, D, F>(
        &mut self,
        q: Q,
        d: D,
        leaf: bool,
        f: &mut F,
    ) -> MutUpdate<Q, K, V, D>
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        match self.get(&q) {
            Loc::Here(i) => match f(q, d, Some((&self.keys[i], &self.vals[i]))) {
                Some((k, v)) => {
                    self.keys[i] = k;
                    MutUpdate::Updated {
                        overflow: None,
                        previous: Some(mem::replace(&mut self.vals[i], v)),
                    }
                }
                None => {
                    self.keys.remove(i);
                    MutUpdate::Updated {
                        overflow: None,
                        previous: Some(self.vals.remove(i)),
                    }
                }
            },
            Loc::NotPresent(i) => match f(q, d, None) {
                Some((k, v)) => {
                    self.keys.insert(i, k);
                    self.vals.insert(i, v);
                    let overflow = {
                        if self.len() <= SIZE {
                            None
                        } else {
                            self.keys
                                .pop()
                                .and_then(|k| self.vals.pop().map(move |v| (k, v)))
                        }
                    };
                    MutUpdate::Updated {
                        overflow,
                        previous: None,
                    }
                }
                None => MutUpdate::Updated {
                    overflow: None,
                    previous: None,
                },
            },
            loc @ Loc::InLeft | loc @ Loc::InRight => {
                if !leaf || self.len() == SIZE {
                    match loc {
                        Loc::InLeft => MutUpdate::UpdateLeft(q, d),
                        Loc::InRight => MutUpdate::UpdateRight(q, d),
                        Loc::Here(..) | Loc::NotPresent(..) => unreachable!(),
                    }
                } else {
                    match loc {
                        Loc::InLeft => {
                            if let Some((k, v)) = f(q, d, None) {
                                self.keys.insert(0, k);
                                self.vals.insert(0, v);
                            }
                        }
                        Loc::InRight => {
                            if let Some((k, v)) = f(q, d, None) {
                                self.keys.push(k);
                                self.vals.push(v);
                            }
                        }
                        _ => unreachable!("bug"),
                    };
                    MutUpdate::Updated {
                        overflow: None,
                        previous: None,
                    }
                }
            }
        }
    }

    pub(crate) fn intersect<F>(
        c0: &Chunk<K, V, SIZE>,
        c1: &Chunk<K, V, SIZE>,
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

    pub(crate) fn remove_elt_at(&self, i: usize) -> Self {
        let mut elts = Chunk::with_capacity(self.len() - 1);
        if self.len() == 0 {
            panic!("can't remove from an empty chunk")
        } else if self.len() == 1 {
            assert_eq!(i, 0);
            elts
        } else if i == 0 {
            elts.keys.extend_from_slice(&self.keys[1..self.len()]);
            elts.vals.extend_from_slice(&self.vals[1..self.len()]);
            elts
        } else if i == self.len() - 1 {
            elts.keys.extend_from_slice(&self.keys[0..self.len() - 1]);
            elts.vals.extend_from_slice(&self.vals[0..self.len() - 1]);
            elts
        } else {
            elts.keys.extend_from_slice(&self.keys[0..i]);
            elts.keys.extend_from_slice(&self.keys[i + 1..self.len()]);
            elts.vals.extend_from_slice(&self.vals[0..i]);
            elts.vals.extend_from_slice(&self.vals[i + 1..self.len()]);
            elts
        }
    }

    pub(crate) fn remove_elt_at_mut(&mut self, i: usize) -> (K, V) {
        if self.len() == 0 {
            panic!("can't remove from an empty chunk")
        } else {
            let k = self.keys.remove(i);
            let v = self.vals.remove(i);
            (k, v)
        }
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

impl<K, V, const SIZE: usize> IntoIterator for Chunk<K, V, SIZE> {
    type Item = (K, V);
    type IntoIter = iter::Zip<vec::IntoIter<K>, vec::IntoIter<V>>;
    fn into_iter(self) -> Self::IntoIter {
        self.keys.into_iter().zip(self.vals)
    }
}

impl<'a, K, V, const SIZE: usize> IntoIterator for &'a Chunk<K, V, SIZE>{
    type Item = (&'a K, &'a V);
    type IntoIter = iter::Zip<slice::Iter<'a, K>, slice::Iter<'a, V>>;
    fn into_iter(self) -> Self::IntoIter {
        (&self.keys).into_iter().zip(&self.vals)
    }
}
