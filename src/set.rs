pub use crate::chunk::DEFAULT_SIZE;
use crate::{
    avl::{Iter, Tree, WeakTree},
    pool::{pool, ChunkPool},
};
use core::{
    borrow::Borrow,
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    default::Default,
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
    iter::FromIterator,
    ops::{RangeBounds, RangeFull},
};

#[cfg(feature = "serde")]
use serde::{
    de::{SeqAccess, Visitor},
    ser::SerializeSeq,
    Deserialize, Deserializer, Serialize, Serializer,
};

#[cfg(feature = "serde")]
use core::marker::PhantomData;

#[cfg(feature = "rayon")]
use rayon::{
    iter::{FromParallelIterator, IntoParallelIterator},
    prelude::*,
};

/// This set uses a similar strategy to BTreeSet to ensure cache
/// efficient performance on modern hardware while still providing
/// log(N) get, insert, and remove operations.
/// # Examples
/// ```
/// # extern crate alloc;
/// use alloc::string::String;
/// use self::immutable_chunkmap::set::SetM;
///
/// let m =
///    SetM::new()
///    .insert(String::from("1")).0
///    .insert(String::from("2")).0
///    .insert(String::from("3")).0;
///
/// assert_eq!(m.contains("1"), true);
/// assert_eq!(m.contains("2"), true);
/// assert_eq!(m.contains("3"), true);
/// assert_eq!(m.contains("4"), false);
///
/// for k in &m { println!("{}", k) }
/// ```
#[derive(Clone)]
pub struct Set<K: Ord + Clone, const SIZE: usize> {
    pool: ChunkPool<K, (), SIZE>,
    t: Tree<K, (), SIZE>,
}

/// set with a smaller chunk size, faster to update, slower to search
pub type SetS<K> = Set<K, { DEFAULT_SIZE / 2 }>;

/// set with the default chunk size, a good balance of search and update performance
pub type SetM<K> = Set<K, DEFAULT_SIZE>;

/// set with a larger chunk size, faster to search, slower to update
pub type SetL<K> = Set<K, { DEFAULT_SIZE * 2 }>;

#[derive(Clone)]
pub struct WeakSetRef<K: Ord + Clone, const SIZE: usize> {
    pool: ChunkPool<K, (), SIZE>,
    t: WeakTree<K, (), SIZE>,
}

pub type WeakSetRefS<K> = WeakSetRef<K, 32>;
pub type WeakSetRefM<K> = WeakSetRef<K, 128>;
pub type WeakSetRefL<K> = WeakSetRef<K, 512>;

impl<K, const SIZE: usize> WeakSetRef<K, SIZE>
where
    K: Ord + Clone,
{
    pub fn upgrade(&self) -> Option<Set<K, SIZE>> {
        self.t.upgrade().map(|t| Set {
            pool: self.pool.clone(),
            t,
        })
    }
}

impl<K, const SIZE: usize> Hash for Set<K, SIZE>
where
    K: Hash + Ord + Clone,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.t.hash(state)
    }
}

impl<K, const SIZE: usize> Default for Set<K, SIZE>
where
    K: Ord + Clone,
{
    fn default() -> Set<K, SIZE> {
        Set::new()
    }
}

impl<K, const SIZE: usize> PartialEq for Set<K, SIZE>
where
    K: Ord + Clone,
{
    fn eq(&self, other: &Set<K, SIZE>) -> bool {
        self.t == other.t
    }
}

impl<K, const SIZE: usize> Eq for Set<K, SIZE> where K: Eq + Ord + Clone {}

impl<K, const SIZE: usize> PartialOrd for Set<K, SIZE>
where
    K: Ord + Clone,
{
    fn partial_cmp(&self, other: &Set<K, SIZE>) -> Option<Ordering> {
        self.t.partial_cmp(&other.t)
    }
}

impl<K, const SIZE: usize> Ord for Set<K, SIZE>
where
    K: Ord + Clone,
{
    fn cmp(&self, other: &Set<K, SIZE>) -> Ordering {
        self.t.cmp(&other.t)
    }
}

impl<K, const SIZE: usize> Debug for Set<K, SIZE>
where
    K: Debug + Ord + Clone,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_set().entries(self.into_iter()).finish()
    }
}

impl<K, const SIZE: usize> FromIterator<K> for Set<K, SIZE>
where
    K: Ord + Clone,
{
    fn from_iter<T: IntoIterator<Item = K>>(iter: T) -> Self {
        Set::new().insert_many(iter)
    }
}

pub struct SetIter<
    'a,
    R: RangeBounds<Q> + 'a,
    Q: Ord + ?Sized,
    K: 'a + Clone + Ord + Borrow<Q>,
    const SIZE: usize,
>(Iter<'a, R, Q, K, (), SIZE>);

impl<'a, R, Q, K, const SIZE: usize> Iterator for SetIter<'a, R, Q, K, SIZE>
where
    Q: Ord + ?Sized,
    R: RangeBounds<Q> + 'a,
    K: 'a + Clone + Ord + Borrow<Q>,
{
    type Item = &'a K;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, ())| k)
    }
}

impl<'a, R, Q, K, const SIZE: usize> DoubleEndedIterator for SetIter<'a, R, Q, K, SIZE>
where
    Q: Ord + ?Sized,
    R: RangeBounds<Q> + 'a,
    K: 'a + Clone + Ord + Borrow<Q>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(k, ())| k)
    }
}

impl<'a, K, const SIZE: usize> IntoIterator for &'a Set<K, SIZE>
where
    K: 'a + Ord + Clone,
{
    type Item = &'a K;
    type IntoIter = SetIter<'a, RangeFull, K, K, SIZE>;
    fn into_iter(self) -> Self::IntoIter {
        SetIter(self.t.into_iter())
    }
}

#[cfg(feature = "serde")]
impl<V, const SIZE: usize> Serialize for Set<V, SIZE>
where
    V: Serialize + Clone + Ord,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for v in self {
            seq.serialize_element(v)?
        }
        seq.end()
    }
}

#[cfg(feature = "serde")]
struct SetVisitor<V: Clone + Ord, const SIZE: usize> {
    marker: PhantomData<fn() -> Set<V, SIZE>>,
}

#[cfg(feature = "serde")]
impl<'a, V, const SIZE: usize> Visitor<'a> for SetVisitor<V, SIZE>
where
    V: Deserialize<'a> + Clone + Ord,
{
    type Value = Set<V, SIZE>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("expecting an immutable_chunkmap::Set")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'a>,
    {
        let mut t = Set::<V, SIZE>::new();
        while let Some(v) = seq.next_element()? {
            t.insert_cow(v);
        }
        Ok(t)
    }
}

#[cfg(feature = "serde")]
impl<'a, V, const SIZE: usize> Deserialize<'a> for Set<V, SIZE>
where
    V: Deserialize<'a> + Clone + Ord,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'a>,
    {
        deserializer.deserialize_seq(SetVisitor {
            marker: PhantomData,
        })
    }
}

#[cfg(feature = "rayon")]
impl<'a, V, const SIZE: usize> IntoParallelIterator for &'a Set<V, SIZE>
where
    V: 'a + Ord + Clone + Send + Sync,
{
    type Item = &'a V;
    type Iter = rayon::vec::IntoIter<&'a V>;

    fn into_par_iter(self) -> Self::Iter {
        self.into_iter().collect::<Vec<_>>().into_par_iter()
    }
}

#[cfg(feature = "rayon")]
impl<V, const SIZE: usize> FromParallelIterator<V> for Set<V, SIZE>
where
    V: Ord + Clone + Send + Sync,
{
    fn from_par_iter<I>(i: I) -> Self
    where
        I: IntoParallelIterator<Item = V>,
    {
        i.into_par_iter()
            .fold_with(Set::new(), |mut m, v| {
                m.insert_cow(v);
                m
            })
            .reduce_with(|m0, m1| m0.union(&m1))
            .unwrap_or_else(Set::new)
    }
}

impl<K, const SIZE: usize> Set<K, SIZE>
where
    K: Ord + Clone,
{
    /// Create a new empty set
    pub fn new() -> Self {
        Set {
            pool: pool(1024),
            t: Tree::new(),
        }
    }

    /// Create a new empty set using the specified pool for allocation
    pub fn new_with_pool(pool: ChunkPool<K, (), SIZE>) -> Self {
        Set {
            pool,
            t: Tree::new(),
        }
    }

    /// Create a weak reference to this set
    pub fn downgrade(&self) -> WeakSetRef<K, SIZE> {
        WeakSetRef {
            pool: self.pool.clone(),
            t: self.t.downgrade(),
        }
    }

    /// Return the number of strong references to this set (see Arc)
    pub fn strong_count(&self) -> usize {
        self.t.strong_count()
    }

    /// Return the number of weak references to this set (see Arc)
    pub fn weak_count(&self) -> usize {
        self.t.weak_count()
    }

    /// This will insert many elements at once, and is
    /// potentially a lot faster than inserting one by one,
    /// especially if the data is sorted.
    ///
    /// #Examples
    ///```
    /// use self::immutable_chunkmap::set::SetM;
    ///
    /// let mut v = vec![1, 10, -12, 44, 50];
    /// v.sort_unstable();
    ///
    /// let m = SetM::new().insert_many(v.iter().map(|k| *k));
    ///
    /// for k in &v {
    ///   assert_eq!(m.contains(k), true)
    /// }
    /// ```
    pub fn insert_many<E: IntoIterator<Item = K>>(&self, elts: E) -> Self {
        let t = self
            .t
            .insert_many(&self.pool, elts.into_iter().map(|k| (k, ())));
        Set {
            pool: self.pool.clone(),
            t,
        }
    }

    /// Remove multiple elements in a single pass. Similar performance
    /// to insert_many.
    pub fn remove_many<Q, E>(&self, elts: E) -> Self
    where
        Q: Ord,
        K: Borrow<Q>,
        E: IntoIterator<Item = Q>,
    {
        let t = self.t.update_many(
            &self.pool,
            elts.into_iter().map(|k| (k, ())),
            &mut |_, _, _| None,
        );
        Set {
            pool: self.pool.clone(),
            t,
        }
    }

    /// This is just slightly wierd, however if you have a bunch of
    /// borrowed forms of members of the set, and you want to look at
    /// the real entries and possibly add/update/remove them, then
    /// this method is for you.
    pub fn update_many<Q, E, F>(&self, elts: E, mut f: F) -> Self
    where
        Q: Ord,
        K: Borrow<Q>,
        E: IntoIterator<Item = Q>,
        F: FnMut(Q, Option<&K>) -> Option<K>,
    {
        let t = self.t.update_many(
            &self.pool,
            elts.into_iter().map(|k| (k, ())),
            &mut |q, (), cur| {
                let cur = cur.map(|(k, ())| k);
                f(q, cur).map(|k| (k, ()))
            },
        );
        Set {
            pool: self.pool.clone(),
            t,
        }
    }

    /// return a new set with k inserted into it. If k already
    /// exists in the old set return true, else false. If the
    /// element already exists in the set memory will not be
    /// allocated.
    pub fn insert(&self, k: K) -> (Self, bool) {
        if self.contains(&k) {
            (self.clone(), true)
        } else {
            let t = self.t.insert(&self.pool, k, ()).0;
            let s = Set {
                pool: self.pool.clone(),
                t,
            };
            (s, false)
        }
    }

    /// insert `k` with copy on write semantics. if `self` is a unique
    /// reference to the set, then k will be inserted in
    /// place. Otherwise, only the parts of the set necessary to
    /// insert `k` will be copied, and then the copies will be
    /// mutated. self will share all the parts that weren't modfied
    /// with any previous clones.
    pub fn insert_cow(&mut self, k: K) -> bool {
        self.t.insert_cow(&self.pool.clone(), k, ()).is_some()
    }

    /// return true if the set contains k, else false. Runs in
    /// log(N) time and constant space. where N is the size of
    /// the set.
    pub fn contains<'a, Q>(&'a self, k: &Q) -> bool
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        self.t.get(k).is_some()
    }

    /// return a reference to the item in the set that is equal to the
    /// given value, or None if no such value exists.
    pub fn get<'a, Q>(&'a self, k: &Q) -> Option<&'a K>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        self.t.get_key(k)
    }

    /// return a new set with k removed. Runs in log(N) time
    /// and log(N) space, where N is the size of the set
    pub fn remove<Q: Sized + Ord>(&self, k: &Q) -> (Self, bool)
    where
        K: Borrow<Q>,
    {
        let (t, prev) = self.t.remove(&self.pool, k);
        let s = Set {
            pool: self.pool.clone(),
            t,
        };
        (s, prev.is_some())
    }

    /// remove `k` from the set in place with copy on write semantics
    /// (see `insert_cow`). return true if `k` was in the set.
    pub fn remove_cow<Q: Sized + Ord>(&mut self, k: &Q) -> bool
    where
        K: Borrow<Q>,
    {
        self.t.remove_cow(&self.pool, k).is_some()
    }

    /// return the union of 2 sets. Runs in O(log(N) + M) time and
    /// space, where N is the largest of the two sets, and M is the
    /// number of chunks that intersect, which is roughly proportional
    /// to the size of the intersection.
    ///
    /// # Examples
    /// ```
    /// use core::iter::FromIterator;
    /// use self::immutable_chunkmap::set::SetM;
    ///
    /// let s0 = SetM::from_iter(0..10);
    /// let s1 = SetM::from_iter(5..15);
    /// let s2 = s0.union(&s1);
    /// for i in 0..15 {
    ///     assert!(s2.contains(&i));
    /// }
    /// ```
    pub fn union(&self, other: &Set<K, SIZE>) -> Self {
        let t = Tree::union(&self.pool, &self.t, &other.t, &mut |_, (), ()| Some(()));
        Set {
            pool: self.pool.clone(),
            t,
        }
    }

    /// return the intersection of 2 sets. Runs in O(log(N) + M) time
    /// and space, where N is the smallest of the two sets, and M is
    /// the number of intersecting chunks.
    ///
    /// # Examples
    /// use core::iter::FromIterator;
    /// use self::immutable_chunkmap::set::SetM;
    ///
    /// let s0 = SetM::from_iter(0..100);
    /// let s1 = SetM::from_iter(20..50);
    /// let s2 = s0.intersect(&s1);
    ///
    /// assert!(s2.len() == 30);
    /// for i in 0..100 {
    ///     if i < 20 || i >= 50 {
    ///         assert!(!s2.contains(&i));
    ///     } else {
    ///         assert!(s2.contains(&i));
    ///     }
    /// }
    pub fn intersect(&self, other: &Set<K, SIZE>) -> Self {
        let t = Tree::intersect(&self.pool, &self.t, &other.t, &mut |_, (), ()| Some(()));
        Set {
            pool: self.pool.clone(),
            t,
        }
    }

    /// Return the difference of two sets. Runs in O(log(N) + M) time
    /// and space, where N is the smallest of the two sets, and M is
    /// the number of intersecting chunks.
    ///
    /// # Examples
    /// ```
    /// use core::iter::FromIterator;
    /// use self::immutable_chunkmap::set::SetM;
    ///
    /// let s0 = SetM::from_iter(0..100);
    /// let s1 = SetM::from_iter(0..50);
    /// let s2 = s0.diff(&s1);
    ///
    /// assert!(s2.len() == 50);
    /// for i in 0..50 {
    ///     assert!(!s2.contains(&i));
    /// }
    /// for i in 50..100 {
    ///     assert!(s2.contains(&i));
    /// }
    /// ```
    pub fn diff(&self, other: &Set<K, SIZE>) -> Self
    where
        K: Debug,
    {
        let t = Tree::diff(&self.pool, &self.t, &other.t, &mut |_, (), ()| None);
        Set {
            pool: self.pool.clone(),
            t,
        }
    }

    /// get the number of elements in the map O(1) time and space
    pub fn len(&self) -> usize {
        self.t.len()
    }

    /// return an iterator over the subset of elements in the
    /// set that are within the specified range.
    ///
    /// The returned iterator runs in O(log(N) + M) time, and
    /// constant space. N is the number of elements in the
    /// tree, and M is the number of elements you examine.
    ///
    /// if lbound >= ubound the returned iterator will be empty
    pub fn range<'a, Q, R>(&'a self, r: R) -> SetIter<'a, R, Q, K, SIZE>
    where
        Q: Ord + ?Sized + 'a,
        K: 'a + Clone + Ord + Borrow<Q>,
        R: RangeBounds<Q> + 'a,
    {
        SetIter(self.t.range(r))
    }
}

impl<K, const SIZE: usize> Set<K, SIZE>
where
    K: Ord + Clone + Debug,
{
    #[allow(dead_code)]
    pub(crate) fn invariant(&self) -> () {
        self.t.invariant()
    }
}
