use crate::pool::{Arc, ChunkPool, Poolable};
use alloc::vec::Vec;
use arrayvec::ArrayVec;
use core::{
    borrow::Borrow,
    cmp::{min, Ord, Ordering},
    fmt::{self, Debug, Formatter},
    iter, mem,
    ops::{Deref, DerefMut},
    slice,
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
pub(crate) struct PVec<T, const SIZE: usize>(ArrayVec<T, SIZE>);

impl<T, const SIZE: usize> Deref for PVec<T, SIZE> {
    type Target = ArrayVec<T, SIZE>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T, const SIZE: usize> DerefMut for PVec<T, SIZE> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T, const SIZE: usize> Poolable for PVec<T, SIZE> {
    fn empty() -> Self {
        Self(ArrayVec::new())
    }

    fn capacity(&self) -> usize {
        1
    }

    fn reset(&mut self) {
        self.clear()
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Chunk<K, V, const SIZE: usize> {
    keys: Arc<PVec<K, SIZE>>,
    vals: Arc<PVec<V, SIZE>>,
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
    pub(crate) fn singleton(pool: &ChunkPool<K, V, SIZE>, k: K, v: V) -> Self {
        let mut t = Chunk::empty(pool);
        let keys = Arc::make_mut(&mut t.keys);
        let vals = Arc::make_mut(&mut t.vals);
        keys.push(k);
        vals.push(v);
        t
    }

    pub(crate) fn empty(pool: &ChunkPool<K, V, SIZE>) -> Self {
        Chunk {
            keys: pool.take_keys(),
            vals: pool.take_vals(),
        }
    }

    pub(crate) fn create_with<Q, D, F>(
        pool: &ChunkPool<K, V, SIZE>,
        chunk: Vec<(Q, D)>,
        f: &mut F,
    ) -> Self
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        let mut t = Chunk::empty(pool);
        let keys = Arc::make_mut(&mut t.keys);
        let vals = Arc::make_mut(&mut t.vals);
        for (k, v) in chunk.into_iter().filter_map(|(q, d)| f(q, d, None)) {
            keys.push(k);
            vals.push(v);
        }
        t
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

    // invariant: chunk is sorted and deduped
    pub(crate) fn update_chunk<Q, D, F>(
        &self,
        pool: &ChunkPool<K, V, SIZE>,
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
            let iter = chunk.into_iter().filter_map(|(q, d)| f(q, d, None));
            let mut overflow_right = Vec::new();
            let mut elts = Chunk::empty(pool);
            let inner_keys = Arc::make_mut(&mut elts.keys);
            let inner_vals = Arc::make_mut(&mut elts.vals);
            if in_right {
                inner_keys.clone_from(&self.keys);
                inner_vals.clone_from(&self.vals);
                for (k, v) in iter {
                    if inner_keys.len() < SIZE {
                        inner_keys.push(k);
                        inner_vals.push(v);
                    } else {
                        overflow_right.push((k, v));
                    }
                }
            } else {
                for (k, v) in iter {
                    if inner_keys.len() < SIZE {
                        inner_keys.push(k);
                        inner_vals.push(v);
                    } else {
                        overflow_right.push((k, v));
                    }
                }
                for (k, v) in self.keys.iter().cloned().zip(self.vals.iter().cloned()) {
                    if inner_keys.len() < SIZE {
                        inner_keys.push(k);
                        inner_vals.push(v);
                    } else {
                        overflow_right.push((k, v));
                    }
                }
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
                elts_keys: &mut PVec<K, SIZE>,
                elts_vals: &mut PVec<V, SIZE>,
                overflow_right: &mut Vec<(K, V)>,
                m: &mut usize,
                i: usize,
            ) where
                K: Ord + Clone,
                V: Clone,
            {
                let n = min(i.saturating_sub(*m), SIZE.saturating_sub(elts_keys.len()));
                if n > 0 {
                    elts_keys.extend(t.keys[*m..*m + n].iter().cloned());
                    elts_vals.extend(t.vals[*m..*m + n].iter().cloned());
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
            let mut elts = Chunk::empty(pool);
            let inner_keys = Arc::make_mut(&mut elts.keys);
            let inner_vals = Arc::make_mut(&mut elts.vals);
            let mut chunk = chunk.into_iter();
            loop {
                if m == self.len() && inner_keys.len() == 0 {
                    not_done.extend(chunk);
                    break;
                }
                match chunk.next() {
                    None => {
                        copy_up_to(
                            self,
                            inner_keys,
                            inner_vals,
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
                                    inner_keys,
                                    inner_vals,
                                    &mut overflow_right,
                                    &mut m,
                                    i,
                                );
                                let r = f(q, d, Some((&self.keys[i], &self.vals[i])));
                                if let Some((k, v)) = r {
                                    if inner_keys.len() < SIZE {
                                        inner_keys.push(k);
                                        inner_vals.push(v);
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
                                    inner_keys,
                                    inner_vals,
                                    &mut overflow_right,
                                    &mut m,
                                    i,
                                );
                                if let Some((k, v)) = f(q, d, None) {
                                    if inner_keys.len() < SIZE {
                                        inner_keys.push(k);
                                        inner_vals.push(v);
                                    } else {
                                        overflow_right.push((k, v));
                                    }
                                }
                            }
                            Loc::InLeft => {
                                if leaf && inner_keys.len() < SIZE {
                                    if let Some((k, v)) = f(q, d, None) {
                                        inner_keys.push(k);
                                        inner_vals.push(v);
                                    }
                                } else {
                                    update_left.push((q, d))
                                }
                            }
                            Loc::InRight => {
                                let len = self.len();
                                copy_up_to(
                                    self,
                                    inner_keys,
                                    inner_vals,
                                    &mut overflow_right,
                                    &mut m,
                                    len,
                                );
                                if leaf && inner_keys.len() < SIZE {
                                    let iter = iter::once((q, d))
                                        .chain(chunk)
                                        .filter_map(|(q, d)| f(q, d, None));
                                    for (k, v) in iter {
                                        if inner_keys.len() < SIZE {
                                            inner_keys.push(k);
                                            inner_vals.push(v);
                                        } else {
                                            overflow_right.push((k, v));
                                        }
                                    }
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
        pool: &ChunkPool<K, V, SIZE>,
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
                let mut elts = Chunk::empty(pool);
                let inner_keys = Arc::make_mut(&mut elts.keys);
                let inner_vals = Arc::make_mut(&mut elts.vals);
                inner_keys.extend(self.keys[0..i].iter().cloned());
                inner_vals.extend(self.vals[0..i].iter().cloned());
                if let Some((k, v)) = f(q, d, Some((&self.keys[i], &self.vals[i]))) {
                    inner_keys.push(k);
                    inner_vals.push(v);
                }
                if i + 1 < self.len() {
                    inner_keys.extend(self.keys[i + 1..self.len()].iter().cloned());
                    inner_vals.extend(self.vals[i + 1..self.len()].iter().cloned());
                }
                Update::Updated {
                    elts,
                    overflow: None,
                    previous: Some(self.vals[i].clone()),
                }
            }
            Loc::NotPresent(i) => {
                let mut elts = Chunk::empty(pool);
                let inner_keys = Arc::make_mut(&mut elts.keys);
                let inner_vals = Arc::make_mut(&mut elts.vals);
                inner_keys.extend(self.keys[0..i].iter().cloned());
                inner_vals.extend(self.vals[0..i].iter().cloned());
                let overflow = match f(q, d, None) {
                    None => None,
                    Some((k, v)) => {
                        if inner_keys.len() == SIZE {
                            let (ok, ov) =
                                (inner_keys.pop().unwrap(), inner_vals.pop().unwrap());
                            inner_keys.push(k);
                            inner_vals.push(v);
                            Some((ok, ov))
                        } else {
                            inner_keys.push(k);
                            inner_vals.push(v);
                            let mut iter = self.keys[i..self.len()]
                                .iter()
                                .cloned()
                                .zip(self.vals[i..self.len()].iter().cloned());
                            loop {
                                match iter.next() {
                                    None => break None,
                                    Some((k, v)) => {
                                        if inner_keys.len() < SIZE {
                                            inner_keys.push(k);
                                            inner_vals.push(v);
                                        } else {
                                            break Some((k, v));
                                        }
                                    }
                                }
                            }
                        }
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
                    let mut elts = Chunk::empty(pool);
                    let inner_keys = Arc::make_mut(&mut elts.keys);
                    let inner_vals = Arc::make_mut(&mut elts.vals);
                    match loc {
                        Loc::InLeft => {
                            if let Some((k, v)) = f(q, d, None) {
                                inner_keys.push(k);
                                inner_vals.push(v);
                            }
                            inner_keys.extend(self.keys[0..self.len()].iter().cloned());
                            inner_vals.extend(self.vals[0..self.len()].iter().cloned());
                        }
                        Loc::InRight => {
                            inner_keys.extend(self.keys[0..self.len()].iter().cloned());
                            inner_vals.extend(self.vals[0..self.len()].iter().cloned());
                            if let Some((k, v)) = f(q, d, None) {
                                inner_keys.push(k);
                                inner_vals.push(v);
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
                    let inner_keys = Arc::make_mut(&mut self.keys);
                    let inner_vals = Arc::make_mut(&mut self.vals);
                    inner_keys[i] = k;
                    MutUpdate::Updated {
                        overflow: None,
                        previous: Some(mem::replace(&mut inner_vals[i], v)),
                    }
                }
                None => {
                    let inner_keys = Arc::make_mut(&mut self.keys);
                    let inner_vals = Arc::make_mut(&mut self.vals);
                    inner_keys.remove(i);
                    MutUpdate::Updated {
                        overflow: None,
                        previous: Some(inner_vals.remove(i)),
                    }
                }
            },
            Loc::NotPresent(i) => match f(q, d, None) {
                Some((k, v)) => {
                    let inner_keys = Arc::make_mut(&mut self.keys);
                    let inner_vals = Arc::make_mut(&mut self.vals);
                    let overflow = if inner_keys.len() == SIZE {
                        let (ok, ov) =
                            (inner_keys.pop().unwrap(), inner_vals.pop().unwrap());
                        inner_keys.insert(i, k);
                        inner_vals.insert(i, v);
                        Some((ok, ov))
                    } else {
                        inner_keys.insert(i, k);
                        inner_vals.insert(i, v);
                        None
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
                    let inner_keys = Arc::make_mut(&mut self.keys);
                    let inner_vals = Arc::make_mut(&mut self.vals);
                    match loc {
                        Loc::InLeft => {
                            if let Some((k, v)) = f(q, d, None) {
                                inner_keys.insert(0, k);
                                inner_vals.insert(0, v);
                            }
                        }
                        Loc::InRight => {
                            if let Some((k, v)) = f(q, d, None) {
                                inner_keys.push(k);
                                inner_vals.push(v);
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

    pub(crate) fn remove_elt_at(&self, pool: &ChunkPool<K, V, SIZE>, i: usize) -> Self {
        let mut elts = Chunk::empty(pool);
        let t_keys = Arc::make_mut(&mut elts.keys);
        let t_vals = Arc::make_mut(&mut elts.vals);
        if i >= self.keys.len() {
            panic!("remove_elt_at: out of bounds")
        } else if self.len() == 1 {
            elts
        } else if i == 0 {
            t_keys.extend(self.keys[1..self.len()].iter().cloned());
            t_vals.extend(self.vals[1..self.len()].iter().cloned());
            elts
        } else if i == self.keys.len() - 1 {
            t_keys.extend(self.keys[0..self.len() - 1].iter().cloned());
            t_vals.extend(self.vals[0..self.len() - 1].iter().cloned());
            elts
        } else {
            t_keys.extend(self.keys[0..i].iter().cloned());
            t_keys.extend(self.keys[i + 1..self.len()].iter().cloned());
            t_vals.extend(self.vals[0..i].iter().cloned());
            t_vals.extend(self.vals[i + 1..self.len()].iter().cloned());
            elts
        }
    }

    pub(crate) fn remove_elt_at_mut(&mut self, i: usize) -> (K, V) {
        if i >= self.len() {
            panic!("remove_elt_at_mut: out of bounds")
        } else {
            let inner_keys = Arc::make_mut(&mut self.keys);
            let inner_vals = Arc::make_mut(&mut self.vals);
            let k = inner_keys.remove(i);
            let v = inner_vals.remove(i);
            (k, v)
        }
    }

    pub(crate) fn append<I: IntoIterator<Item = (K, V)>>(&self, other: I) -> Self {
        let mut elts = self.clone();
        let inner_keys = Arc::make_mut(&mut elts.keys);
        let inner_vals = Arc::make_mut(&mut elts.vals);
        for (k, v) in other {
            if inner_keys.len() < SIZE {
                inner_keys.push(k);
                inner_vals.push(v);
            }
        }
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

    pub(crate) fn val_mut(&mut self, i: usize) -> &mut V {
        &mut Arc::make_mut(&mut self.vals)[i]
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

/*
impl<K: Clone, V: Clone, const SIZE: usize> IntoIterator for Chunk<K, V, SIZE> {
    type Item = (K, V);
    type IntoIter = iter::Zip<alloc::vec::IntoIter<K>, alloc::vec::IntoIter<V>>;
    fn into_iter(mut self) -> Self::IntoIter {
        let inner = mem::replace(
            Arc::make_mut(&mut self.0),
            ChunkInner {
                keys: Vec::new(),
                vals: Vec::new(),
            },
        );
        inner.keys.into_iter().zip(inner.vals.into_iter())
    }
}
*/

impl<'a, K, V, const SIZE: usize> IntoIterator for &'a Chunk<K, V, SIZE> {
    type Item = (&'a K, &'a V);
    type IntoIter = iter::Zip<slice::Iter<'a, K>, slice::Iter<'a, V>>;
    fn into_iter(self) -> Self::IntoIter {
        (&self.keys[..]).into_iter().zip(&self.vals[..])
    }
}

impl<'a, K: Clone, V: Clone, const SIZE: usize> IntoIterator
    for &'a mut Chunk<K, V, SIZE>
{
    type Item = (&'a K, &'a mut V);
    type IntoIter = iter::Zip<slice::Iter<'a, K>, slice::IterMut<'a, V>>;
    fn into_iter(self) -> Self::IntoIter {
        let inner_keys = Arc::make_mut(&mut self.keys);
        let inner_vals = Arc::make_mut(&mut self.vals);
        (&inner_keys[..]).into_iter().zip(&mut inner_vals[..])
    }
}
