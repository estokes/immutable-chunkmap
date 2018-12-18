use std::{
    borrow::Borrow,
    cmp::{Ord, Ordering},
    collections::hash_map::DefaultHasher,
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
    slice, vec,
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
    vals: Vec<(K, V, Option<u64>)>,
    hashidx: Vec<u16>,
}

impl<K, V> Debug for Chunk<K, V>
where
    K: Debug + Ord + Clone,
    V: Debug + Clone,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_map()
            .entries(self.into_iter().map(|(k, v, _)| (k, v)))
            .finish()
    }
}

impl<K, V> Chunk<K, V>
where
    K: Ord + Hash + Clone,
    V: Clone,
{
    pub(crate) fn singleton(k: K, v: V) -> Self {
        let mut t = Chunk::with_capacity(1);
        t.vals.push((k, v, None));
        t.hashidx.push(0);
        t
    }

    pub(crate) fn empty() -> Self {
        Chunk {
            vals: Vec::new(),
            hashidx: Vec::new(),
        }
    }

    fn with_capacity(n: usize) -> Self {
        Chunk {
            vals: Vec::with_capacity(n),
            hashidx: Vec::with_capacity(n),
        }
    }

    pub(crate) fn get_local<Q: ?Sized + Ord + Hash>(&self, k: &Q) -> Result<usize, usize>
    where
        K: Borrow<Q>,
    {
        let len = self.len();
        if len == 0 {
            return Err(0);
        }
        let mut hasher = DefaultHasher::new();
        k.hash(&mut hasher);
        let idx = (hasher.finish() % len as u64) as usize;
        let i = self.hashidx[idx] as usize;
        match k.cmp(self.vals[i].0.borrow()) {
            Ordering::Equal => {
                //println!("hit");
                Ok(i)
            }
            Ordering::Less | Ordering::Greater => {
                //println!("miss");
                match self.vals.binary_search_by_key(&k, |(k, _, _)| k.borrow()) {
                    Result::Ok(i) => Ok(i),
                    Result::Err(i) => Err(i),
                }
            }
        }
    }

    pub(crate) fn get_local_nohash<Q: ?Sized + Ord + Hash>(
        &self,
        k: &Q,
    ) -> Result<usize, usize>
    where
        K: Borrow<Q>,
    {
        match self.vals.binary_search_by_key(&k, |(k, _, _)| k.borrow()) {
            Result::Ok(i) => Ok(i),
            Result::Err(i) => Err(i),
        }
    }

    pub(crate) fn get<Q: ?Sized + Ord + Hash>(&self, k: &Q, hash: bool) -> Loc
    where
        K: Borrow<Q>,
    {
        let len = self.len();
        if len == 0 {
            Loc::NotPresent(0)
        } else {
            let first = k.cmp(&self.vals[0].0.borrow());
            let last = k.cmp(&self.vals[len - 1].0.borrow());
            match (first, last) {
                (Ordering::Equal, _) => Loc::Here(0),
                (_, Ordering::Equal) => Loc::Here(len - 1),
                (Ordering::Less, _) => Loc::InLeft,
                (_, Ordering::Greater) => Loc::InRight,
                (Ordering::Greater, Ordering::Less) => match if hash {
                    self.get_local(k)
                } else {
                    self.get_local_nohash(k)
                } {
                    Result::Ok(i) => Loc::Here(i),
                    Result::Err(i) => Loc::NotPresent(i),
                },
            }
        }
    }

    fn rehash(&mut self) {
        let len = self.len();
        let len64 = len as u64;
        self.hashidx.resize(len, 0);
        for i in 0..self.hashidx.len() {
            self.hashidx[i] = 0;
        }
        for i in 0..len {
            match self.vals[i].2 {
                Some(h) => {
                    self.hashidx[(h % len64) as usize] = i as u16;
                }
                None => {
                    let mut hasher = DefaultHasher::new();
                    self.vals[i].0.hash(&mut hasher);
                    let h = hasher.finish();
                    self.vals[i].2 = Some(h);
                    self.hashidx[(h % len64) as usize] = i as u16;
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
        Q: Ord + Hash,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        assert!(chunk.len() <= SIZE && chunk.len() > 0);
        if self.len() == 0 {
            let mut elts = Chunk::empty();
            elts.vals = chunk
                .drain(0..)
                .filter_map(|(q, d)| f(q, d, None).map(|(k, v)| (k, v, None)))
                .collect();
            elts.rehash();
            UpdateChunk::Created(elts)
        } else {
            let full = !leaf || self.len() >= SIZE;
            let in_left = self.get(&chunk[chunk.len() - 1].0, false) == Loc::InLeft;
            let in_right = self.get(&chunk[0].0, false) == Loc::InRight;
            if full && in_left {
                UpdateChunk::UpdateLeft(chunk)
            } else if full && in_right {
                UpdateChunk::UpdateRight(chunk)
            } else if leaf && in_left {
                let mut elts = Chunk::empty();
                elts.vals = chunk
                    .drain(0..)
                    .filter_map(|(q, d)| f(q, d, None).map(|(k, v)| (k, v, None)))
                    .collect();
                elts.vals.extend_from_slice(&self.vals);
                let overflow_right = {
                    if elts.len() <= SIZE {
                        Vec::new()
                    } else {
                        elts.vals
                            .split_off(SIZE)
                            .into_iter()
                            .map(|(k, v, _)| (k, v))
                            .collect()
                    }
                };
                elts.vals.shrink_to_fit();
                elts.rehash();
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
                    match elts.get(&q, false) {
                        Loc::Here(i) => {
                            match f(q, d, Some((&elts.vals[i].0, &elts.vals[i].1))) {
                                None => {
                                    elts.vals.remove(i);
                                }
                                Some((k, v)) => {
                                    elts.vals[i] = (k, v, None);
                                }
                            }
                        }
                        Loc::NotPresent(i) => {
                            if elts.len() < SIZE {
                                if let Some((k, v)) = f(q, d, None) {
                                    elts.vals.insert(i, (k, v, None));
                                }
                            } else {
                                if let Some((k, v)) = f(q, d, None) {
                                    let (k0, v0, _) = elts.vals.pop().unwrap();
                                    overflow_right.push((k0, v0));
                                    elts.vals.insert(i, (k, v, None));
                                }
                            }
                        }
                        Loc::InLeft => {
                            if leaf && elts.len() < SIZE {
                                if let Some((k, v)) = f(q, d, None) {
                                    elts.vals.insert(0, (k, v, None));
                                }
                            } else {
                                update_left.push((q, d))
                            }
                        }
                        Loc::InRight => {
                            if leaf && elts.len() < SIZE {
                                if let Some((k, v)) = f(q, d, None) {
                                    elts.vals.push((k, v, None));
                                }
                            } else {
                                update_right.push((q, d))
                            }
                        }
                    }
                }
                overflow_right.reverse();
                if elts.len() > 0 {
                    elts.rehash();
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
        Q: Ord + Hash,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        match self.get(&q, false) {
            Loc::Here(i) => {
                let mut elts = Chunk::with_capacity(self.len());
                elts.vals.extend_from_slice(&self.vals[0..i]);
                if let Some((k, v)) = f(q, d, Some((&self.vals[i].0, &self.vals[i].1))) {
                    elts.vals.push((k, v, None));
                }
                if i + 1 < self.len() {
                    elts.vals.extend_from_slice(&self.vals[i + 1..self.len()]);
                }
                elts.rehash();
                Update::Updated {
                    elts,
                    overflow: None,
                    previous: Some(self.vals[i].1.clone()),
                }
            }
            Loc::NotPresent(i) => {
                let mut elts = Chunk::with_capacity(self.len() + 1);
                elts.vals.extend_from_slice(&self.vals[0..i]);
                if let Some((k, v)) = f(q, d, None) {
                    elts.vals.push((k, v, None));
                }
                elts.vals.extend_from_slice(&self.vals[i..self.len()]);
                let overflow = {
                    if elts.len() <= SIZE {
                        None
                    } else {
                        elts.vals.pop().map(|(k, v, _)| (k, v))
                    }
                };
                elts.rehash();
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
                                elts.vals.push((k, v, None));
                            }
                            elts.vals.extend_from_slice(&self.vals[0..self.len()]);
                        }
                        Loc::InRight => {
                            elts.vals.extend_from_slice(&self.vals[0..self.len()]);
                            if let Some((k, v)) = f(q, d, None) {
                                elts.vals.push((k, v, None));
                            }
                        }
                        _ => unreachable!("bug"),
                    };
                    elts.rehash();
                    Update::Updated {
                        elts,
                        overflow: None,
                        previous: None,
                    }
                }
            }
        }
    }

    pub(crate) fn remove_elt_at(&self, i: usize) -> Self {
        let mut elts = Chunk::with_capacity(self.len() - 1);
        if self.len() == 0 {
            panic!("can't remove from an empty chunk")
        } else if self.len() == 1 {
            assert_eq!(i, 0);
            elts.rehash();
            elts
        } else if i == 0 {
            elts.vals.extend_from_slice(&self.vals[1..self.len()]);
            elts.rehash();
            elts
        } else if i == self.len() - 1 {
            elts.vals.extend_from_slice(&self.vals[0..self.len() - 1]);
            elts.rehash();
            elts
        } else {
            elts.vals.extend_from_slice(&self.vals[0..i]);
            elts.vals.extend_from_slice(&self.vals[i + 1..self.len()]);
            elts.rehash();
            elts
        }
    }

    pub(crate) fn min_max_key(&self) -> Option<(K, K)> {
        if self.len() == 0 {
            None
        } else {
            Some((self.vals[0].0.clone(), self.vals[self.len() - 1].0.clone()))
        }
    }

    pub(crate) fn min_elt(&self) -> Option<(&K, &V)> {
        if self.len() == 0 {
            None
        } else {
            Some((&self.vals[0].0, &self.vals[0].1))
        }
    }

    pub(crate) fn max_elt(&self) -> Option<(&K, &V)> {
        if self.len() == 0 {
            None
        } else {
            let last = self.len() - 1;
            Some((&self.vals[last].0, &self.vals[last].1))
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.vals.len()
    }

    pub(crate) fn key(&self, i: usize) -> &K {
        &self.vals[i].0
    }

    pub(crate) fn val(&self, i: usize) -> &V {
        &self.vals[i].1
    }

    pub(crate) fn kv(&self, i: usize) -> (&K, &V) {
        (&self.vals[i].0, &self.vals[i].1)
    }

    pub(crate) fn to_vec(&self) -> Vec<(K, V)> {
        self.into_iter()
            .map(|(k, v, _)| (k.clone(), v.clone()))
            .collect()
    }
}

impl<K, V> IntoIterator for Chunk<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    type Item = (K, V, Option<u64>);
    type IntoIter = vec::IntoIter<(K, V, Option<u64>)>;
    fn into_iter(self) -> Self::IntoIter {
        self.vals.into_iter()
    }
}

impl<'a, K, V> IntoIterator for &'a Chunk<K, V>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
{
    type Item = &'a (K, V, Option<u64>);
    type IntoIter = slice::Iter<'a, (K, V, Option<u64>)>;
    fn into_iter(self) -> Self::IntoIter {
        (&self.vals).into_iter()
    }
}
