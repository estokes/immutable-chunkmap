use crate::avl::{Iter, Tree, WeakTree};
pub use crate::chunk::DEFAULT_SIZE;
use std::{
    borrow::Borrow,
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    default::Default,
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
    iter::FromIterator,
    ops::{Index, RangeBounds, RangeFull, IndexMut},
};

#[cfg(feature = "serde")]
use serde::{
    de::{MapAccess, Visitor},
    ser::SerializeMap,
    Deserialize, Deserializer, Serialize, Serializer,
};

#[cfg(feature = "serde")]
use std::marker::PhantomData;

#[cfg(feature = "rayon")]
use rayon::{
    iter::{FromParallelIterator, IntoParallelIterator},
    prelude::*,
};

/// This Map uses a similar strategy to BTreeMap to ensure cache
/// efficient performance on modern hardware while still providing
/// log(N) get, insert, and remove operations.
///
/// For good performance, it is very important to understand
/// that clone is a fundamental operation, it needs to be fast
/// for your key and data types, because it's going to be
/// called a lot whenever you change the map.
///
/// # Why
///
/// 1. Multiple threads can read this structure even while one thread
/// is updating it. Using a library like arc_swap you can avoid ever
/// blocking readers.
///
/// 2. Snapshotting this structure is free.
///
/// # Examples
/// ```
/// use std::string::String;
/// use self::immutable_chunkmap::map::MapM;
///
/// let m =
///    MapM::new()
///    .insert(String::from("1"), 1).0
///    .insert(String::from("2"), 2).0
///    .insert(String::from("3"), 3).0;
///
/// assert_eq!(m.get("1"), Option::Some(&1));
/// assert_eq!(m.get("2"), Option::Some(&2));
/// assert_eq!(m.get("3"), Option::Some(&3));
/// assert_eq!(m.get("4"), Option::None);
///
/// for (k, v) in &m {
///   println!("key {}, val: {}", k, v)
/// }
/// ```
#[derive(Clone)]
pub struct Map<K: Ord + Clone, V: Clone, const SIZE: usize>(Tree<K, V, SIZE>);

/// Map using a smaller chunk size, faster to update, slower to search
pub type MapS<K, V> = Map<K, V, { DEFAULT_SIZE / 2 }>;

/// Map using the default chunk size, a good balance of update and search
pub type MapM<K, V> = Map<K, V, DEFAULT_SIZE>;

/// Map using a larger chunk size, faster to search, slower to update
pub type MapL<K, V> = Map<K, V, { DEFAULT_SIZE * 2 }>;

/// A weak reference to a map.
#[derive(Clone)]
pub struct WeakMapRef<K: Ord + Clone, V: Clone, const SIZE: usize>(WeakTree<K, V, SIZE>);

pub type WeakMapRefS<K, V> = WeakMapRef<K, V, { DEFAULT_SIZE / 2 }>;
pub type WeakMapRefM<K, V> = WeakMapRef<K, V, DEFAULT_SIZE>;
pub type WeakMapRefL<K, V> = WeakMapRef<K, V, { DEFAULT_SIZE * 2 }>;

impl<K, V, const SIZE: usize> WeakMapRef<K, V, SIZE>
where
    K: Ord + Clone,
    V: Clone,
{
    pub fn upgrade(&self) -> Option<Map<K, V, SIZE>> {
        self.0.upgrade().map(Map)
    }
}

impl<K, V, const SIZE: usize> Hash for Map<K, V, SIZE>
where
    K: Hash + Ord + Clone,
    V: Hash + Clone,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl<K, V, const SIZE: usize> Default for Map<K, V, SIZE>
where
    K: Ord + Clone,
    V: Clone,
{
    fn default() -> Map<K, V, SIZE> {
        Map::new()
    }
}

impl<K, V, const SIZE: usize> PartialEq for Map<K, V, SIZE>
where
    K: PartialEq + Ord + Clone,
    V: PartialEq + Clone,
{
    fn eq(&self, other: &Map<K, V, SIZE>) -> bool {
        self.0 == other.0
    }
}

impl<K, V, const SIZE: usize> Eq for Map<K, V, SIZE>
where
    K: Eq + Ord + Clone,
    V: Eq + Clone,
{
}

impl<K, V, const SIZE: usize> PartialOrd for Map<K, V, SIZE>
where
    K: Ord + Clone,
    V: PartialOrd + Clone,
{
    fn partial_cmp(&self, other: &Map<K, V, SIZE>) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<K, V, const SIZE: usize> Ord for Map<K, V, SIZE>
where
    K: Ord + Clone,
    V: Ord + Clone,
{
    fn cmp(&self, other: &Map<K, V, SIZE>) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<K, V, const SIZE: usize> Debug for Map<K, V, SIZE>
where
    K: Debug + Ord + Clone,
    V: Debug + Clone,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a, Q, K, V, const SIZE: usize> Index<&'a Q> for Map<K, V, SIZE>
where
    Q: Ord,
    K: Ord + Clone + Borrow<Q>,
    V: Clone,
{
    type Output = V;
    fn index(&self, k: &Q) -> &V {
        self.get(k).expect("element not found for key")
    }
}

impl<'a, Q, K, V, const SIZE: usize> IndexMut<&'a Q> for Map<K, V, SIZE>
where
    Q: Ord,
    K: Ord + Clone + Borrow<Q>,
    V: Clone,
{
    fn index_mut(&mut self, k: &'a Q) -> &mut Self::Output {
        self.get_mut_cow(k).expect("element not found for key")
    }
}

impl<K, V, const SIZE: usize> FromIterator<(K, V)> for Map<K, V, SIZE>
where
    K: Ord + Clone,
    V: Clone,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Map::new().insert_many(iter)
    }
}

impl<'a, K, V, const SIZE: usize> IntoIterator for &'a Map<K, V, SIZE>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, RangeFull, K, K, V, SIZE>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[cfg(feature = "serde")]
impl<K, V, const SIZE: usize> Serialize for Map<K, V, SIZE>
where
    K: Serialize + Clone + Ord,
    V: Serialize + Clone,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.len()))?;
        for (k, v) in self {
            map.serialize_entry(k, v)?
        }
        map.end()
    }
}

#[cfg(feature = "serde")]
struct MapVisitor<K: Clone + Ord, V: Clone, const SIZE: usize> {
    marker: PhantomData<fn() -> Map<K, V, SIZE>>,
}

#[cfg(feature = "serde")]
impl<'a, K, V, const SIZE: usize> Visitor<'a> for MapVisitor<K, V, SIZE>
where
    K: Deserialize<'a> + Clone + Ord,
    V: Deserialize<'a> + Clone,
{
    type Value = Map<K, V, SIZE>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("expected an immutable_chunkmap::Map")
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'a>,
    {
        let mut t = Map::<K, V, SIZE>::new();
        while let Some((k, v)) = map.next_entry()? {
            t.insert_cow(k, v);
        }
        Ok(t)
    }
}

#[cfg(feature = "serde")]
impl<'a, K, V, const SIZE: usize> Deserialize<'a> for Map<K, V, SIZE>
where
    K: Deserialize<'a> + Clone + Ord,
    V: Deserialize<'a> + Clone,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'a>,
    {
        deserializer.deserialize_map(MapVisitor {
            marker: PhantomData,
        })
    }
}

#[cfg(feature = "rayon")]
impl<'a, K, V, const SIZE: usize> IntoParallelIterator for &'a Map<K, V, SIZE>
where
    K: 'a + Ord + Clone + Send + Sync,
    V: Clone + Send + Sync,
{
    type Item = (&'a K, &'a V);
    type Iter = rayon::vec::IntoIter<(&'a K, &'a V)>;

    fn into_par_iter(self) -> Self::Iter {
        self.into_iter().collect::<Vec<_>>().into_par_iter()
    }
}

#[cfg(feature = "rayon")]
impl<K, V, const SIZE: usize> FromParallelIterator<(K, V)> for Map<K, V, SIZE>
where
    K: Ord + Clone + Send + Sync,
    V: Clone + Send + Sync,
{
    fn from_par_iter<I>(i: I) -> Self
    where
        I: IntoParallelIterator<Item = (K, V)>,
    {
        i.into_par_iter()
            .fold_with(Map::new(), |mut m, (k, v)| {
                m.insert_cow(k, v);
                m
            })
            .reduce_with(|m0, m1| m0.union(&m1, |_k, _v0, v1| Some(v1.clone())))
            .unwrap_or_else(Map::new)
    }
}

impl<K, V, const SIZE: usize> Map<K, V, SIZE>
where
    K: Ord + Clone,
    V: Clone,
{
    /// Create a new empty map
    pub fn new() -> Self {
        Map(Tree::new())
    }

    /// Create a weak reference to this map
    pub fn downgrade(&self) -> WeakMapRef<K, V, SIZE> {
        WeakMapRef(self.0.downgrade())
    }

    /// Return the number of strong references to this map (see Arc)
    pub fn strong_count(&self) -> usize {
        self.0.strong_count()
    }

    /// Return the number of weak references to this map (see Arc)
    pub fn weak_count(&self) -> usize {
        self.0.weak_count()
    }

    /// This will insert many elements at once, and is
    /// potentially a lot faster than inserting one by one,
    /// especially if the data is sorted. It is just a wrapper
    /// around the more general update_many method.
    ///
    /// #Examples
    ///```
    /// use self::immutable_chunkmap::map::MapM;
    ///
    /// let mut v = vec![(1, 3), (10, 1), (-12, 2), (44, 0), (50, -1)];
    /// v.sort_unstable_by_key(|&(k, _)| k);
    ///
    /// let m = MapM::new().insert_many(v.iter().map(|(k, v)| (*k, *v)));
    ///
    /// for (k, v) in &v {
    ///   assert_eq!(m.get(k), Option::Some(v))
    /// }
    /// ```
    pub fn insert_many<E: IntoIterator<Item = (K, V)>>(&self, elts: E) -> Self {
        Map(self.0.insert_many(elts))
    }

    /// This will remove many elements at once, and is potentially a
    /// lot faster than removing elements one by one, especially if
    /// the data is sorted. It is just a wrapper around the more
    /// general update_many method.
    pub fn remove_many<Q, E>(&self, elts: E) -> Self
    where
        E: IntoIterator<Item = Q>,
        Q: Ord,
        K: Borrow<Q>,
    {
        self.update_many(elts.into_iter().map(|q| (q, ())), |_, _, _| None)
    }

    /// This method updates multiple bindings in one call. Given an
    /// iterator of an arbitrary type (Q, D), where Q is any borrowed
    /// form of K, an update function taking Q, D, the current binding
    /// in the map, if any, and producing the new binding, if any,
    /// this method will produce a new map with updated bindings of
    /// many elements at once. It will skip intermediate node
    /// allocations where possible. If the data in elts is sorted, it
    /// will be able to skip many more intermediate allocations, and
    /// can produce a speedup of about 10x compared to
    /// inserting/updating one by one. In any case it should always be
    /// faster than inserting elements one by one, even with random
    /// unsorted keys.
    ///
    /// #Examples
    /// ```
    /// use std::iter::FromIterator;
    /// use self::immutable_chunkmap::map::MapM;
    ///
    /// let m = MapM::from_iter((0..4).map(|k| (k, k)));
    /// let m = m.update_many(
    ///     (0..4).map(|x| (x, ())),
    ///     |k, (), cur| cur.map(|(_, c)| (k, c + 1))
    /// );
    /// assert_eq!(
    ///     m.into_iter().map(|(k, v)| (*k, *v)).collect::<Vec<_>>(),
    ///     vec![(0, 1), (1, 2), (2, 3), (3, 4)]
    /// );
    /// ```
    pub fn update_many<Q, D, E, F>(&self, elts: E, mut f: F) -> Self
    where
        E: IntoIterator<Item = (Q, D)>,
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        Map(self.0.update_many(elts, &mut f))
    }

    /// return a new map with (k, v) inserted into it. If k
    /// already exists in the old map, the old binding will be
    /// returned, and the new map will contain the new
    /// binding. In fact this method is just a wrapper around
    /// update.
    pub fn insert(&self, k: K, v: V) -> (Self, Option<V>) {
        let (root, prev) = self.0.insert(k, v);
        (Map(root), prev)
    }

    /// insert in place using copy on write semantics if self is not a
    /// unique reference to the map. see `update_cow`.
    pub fn insert_cow(&mut self, k: K, v: V) -> Option<V> {
        self.0.insert_cow(k, v)
    }

    /// return a new map with the binding for q, which can be any
    /// borrowed form of k, updated to the result of f. If f returns
    /// None, the binding will be removed from the new map, otherwise
    /// it will be inserted. This function is more efficient than
    /// calling `get` and then `insert`, since it makes only one tree
    /// traversal instead of two. This method runs in log(N) time and
    /// space where N is the size of the map.
    ///
    /// # Examples
    /// ```
    /// use self::immutable_chunkmap::map::MapM;
    ///
    /// let (m, _) = MapM::new().update(0, 0, |k, d, _| Some((k, d)));
    /// let (m, _) = m.update(1, 1, |k, d, _| Some((k, d)));
    /// let (m, _) = m.update(2, 2, |k, d, _| Some((k, d)));
    /// assert_eq!(m.get(&0), Some(&0));
    /// assert_eq!(m.get(&1), Some(&1));
    /// assert_eq!(m.get(&2), Some(&2));
    ///
    /// let (m, _) = m.update(0, (), |k, (), v| v.map(move |(_, v)| (k, v + 1)));
    /// assert_eq!(m.get(&0), Some(&1));
    /// assert_eq!(m.get(&1), Some(&1));
    /// assert_eq!(m.get(&2), Some(&2));
    ///
    /// let (m, _) = m.update(1, (), |_, (), _| None);
    /// assert_eq!(m.get(&0), Some(&1));
    /// assert_eq!(m.get(&1), None);
    /// assert_eq!(m.get(&2), Some(&2));
    /// ```
    pub fn update<Q, D, F>(&self, q: Q, d: D, mut f: F) -> (Self, Option<V>)
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        let (root, prev) = self.0.update(q, d, &mut f);
        (Map(root), prev)
    }

    /// Perform a copy on write update to the map. In the case that
    /// self is a unique reference to the map, then the update will be
    /// performed completly in place. self will be mutated, and no
    /// previous version will be available. In the case that self has
    /// a clone, or clones, then only the parts of the map that need
    /// to be mutated will be copied before the update is
    /// performed. self will reference the mutated copy, and previous
    /// versions of the map will not be modified. self will still
    /// share all the parts of the map that did not need to be mutated
    /// with any pre existing clones.
    ///
    /// COW semantics are a flexible middle way between full
    /// peristance and full mutability. Needless to say in the case
    /// where you have a unique reference to the map, using update_cow
    /// is a lot faster than using update, and a lot more flexible
    /// than update_many.
    ///
    /// Other than copy on write the semanics of this method are
    /// identical to those of update.
    ///
    /// #Examples
    ///```
    /// use self::immutable_chunkmap::map::MapM;
    ///
    /// let mut m = MapM::new().update(0, 0, |k, d, _| Some((k, d))).0;
    /// let orig = m.clone();
    /// m.update_cow(1, 1, |k, d, _| Some((k, d))); // copies the original chunk
    /// m.update_cow(2, 2, |k, d, _| Some((k, d))); // doesn't copy anything
    /// assert_eq!(m.len(), 3);
    /// assert_eq!(orig.len(), 1);
    /// assert_eq!(m.get(&0), Some(&0));
    /// assert_eq!(m.get(&1), Some(&1));
    /// assert_eq!(m.get(&2), Some(&2));
    /// assert_eq!(orig.get(&0), Some(&0));
    /// assert_eq!(orig.get(&1), None);
    /// assert_eq!(orig.get(&2), None);
    ///```
    pub fn update_cow<Q, D, F>(&mut self, q: Q, d: D, mut f: F) -> Option<V>
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        self.0.update_cow(q, d, &mut f)
    }

    /// Merge two maps together. Bindings that exist in both maps will
    /// be passed to f, which may elect to remove the binding by
    /// returning None. This function runs in O(log(n) + m) time and
    /// space, where n is the size of the largest map, and m is the
    /// number of intersecting chunks. It will never be slower than
    /// calling update_many on the first map with an iterator over the
    /// second, and will be significantly faster if the intersection
    /// is minimal or empty.
    ///
    /// # Examples
    /// ```
    /// use std::iter::FromIterator;
    /// use self::immutable_chunkmap::map::MapM;
    ///
    /// let m0 = MapM::from_iter((0..10).map(|k| (k, 1)));
    /// let m1 = MapM::from_iter((10..20).map(|k| (k, 1)));
    /// let m2 = m0.union(&m1, |_k, _v0, _v1| panic!("no intersection expected"));
    ///
    /// for i in 0..20 {
    ///     assert!(m2.get(&i).is_some())
    /// }
    ///
    /// let m3 = MapM::from_iter((5..9).map(|k| (k, 1)));
    /// let m4 = m3.union(&m2, |_k, v0, v1| Some(v0 + v1));
    ///
    /// for i in 0..20 {
    ///    assert!(
    ///        *m4.get(&i).unwrap() ==
    ///        *m3.get(&i).unwrap_or(&0) + *m2.get(&i).unwrap_or(&0)
    ///    )
    /// }
    /// ```
    pub fn union<F>(&self, other: &Map<K, V, SIZE>, mut f: F) -> Self
    where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        Map(Tree::union(&self.0, &other.0, &mut f))
    }

    /// Produce a map containing the mapping over F of the
    /// intersection (by key) of two maps. The function f runs on each
    /// intersecting element, and has the option to omit elements from
    /// the intersection by returning None, or change the value any
    /// way it likes. Runs in O(log(N) + M) time and space where N is
    /// the size of the smallest map, and M is the number of
    /// intersecting chunks.
    ///
    /// # Examples
    ///```
    /// use std::iter::FromIterator;
    /// use self::immutable_chunkmap::map::MapM;
    ///
    /// let m0 = MapM::from_iter((0..100000).map(|k| (k, 1)));
    /// let m1 = MapM::from_iter((50..30000).map(|k| (k, 1)));
    /// let m2 = m0.intersect(&m1, |_k, v0, v1| Some(v0 + v1));
    ///
    /// for i in 0..100000 {
    ///     if i >= 30000 || i < 50 {
    ///         assert!(m2.get(&i).is_none());
    ///     } else {
    ///         assert!(*m2.get(&i).unwrap() == 2);
    ///     }
    /// }
    /// ```
    pub fn intersect<F>(&self, other: &Map<K, V, SIZE>, mut f: F) -> Self
    where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        Map(Tree::intersect(&self.0, &other.0, &mut f))
    }

    /// Produce a map containing the second map subtracted from the
    /// first. The function F is called for each intersecting element,
    /// and ultimately decides whether it appears in the result, for
    /// example, to compute a classical set diff, the function should
    /// always return None.
    ///
    /// # Examples
    ///```
    /// use std::iter::FromIterator;
    /// use self::immutable_chunkmap::map::MapM;
    ///
    /// let m0 = MapM::from_iter((0..10000).map(|k| (k, 1)));
    /// let m1 = MapM::from_iter((50..3000).map(|k| (k, 1)));
    /// let m2 = m0.diff(&m1, |_k, _v0, _v1| None);
    ///
    /// m2.invariant();
    /// dbg!(m2.len());
    /// assert!(m2.len() == 10000 - 2950);
    /// for i in 0..10000 {
    ///     if i >= 3000 || i < 50 {
    ///         assert!(*m2.get(&i).unwrap() == 1);
    ///     } else {
    ///         assert!(m2.get(&i).is_none());
    ///     }
    /// }
    /// ```
    pub fn diff<F>(&self, other: &Map<K, V, SIZE>, mut f: F) -> Self
    where
        F: FnMut(&K, &V, &V) -> Option<V>,
        K: Debug,
        V: Debug,
    {
        Map(Tree::diff(&self.0, &other.0, &mut f))
    }

    /// lookup the mapping for k. If it doesn't exist return
    /// None. Runs in log(N) time and constant space. where N
    /// is the size of the map.
    pub fn get<'a, Q: ?Sized + Ord>(&'a self, k: &Q) -> Option<&'a V>
    where
        K: Borrow<Q>,
    {
        self.0.get(k)
    }

    /// lookup the mapping for k. Return the key. If it doesn't exist
    /// return None. Runs in log(N) time and constant space. where N
    /// is the size of the map.
    pub fn get_key<'a, Q: ?Sized + Ord>(&'a self, k: &Q) -> Option<&'a K>
    where
        K: Borrow<Q>,
    {
        self.0.get_key(k)
    }

    /// lookup the mapping for k. Return both the key and the
    /// value. If it doesn't exist return None. Runs in log(N) time
    /// and constant space. where N is the size of the map.
    pub fn get_full<'a, Q: ?Sized + Ord>(&'a self, k: &Q) -> Option<(&'a K, &'a V)>
    where
        K: Borrow<Q>,
    {
        self.0.get_full(k)
    }

    /// Get a mutable reference to the value mapped to `k` using copy on write semantics. 
    /// This works as `Arc::make_mut`, it will only clone the parts of the tree that are,
    /// - required to reach `k`
    /// - have a strong count > 1
    ///
    /// This operation is also triggered by mut indexing on the map, e.g. `&mut m[k]` 
    /// calls `get_mut_cow` on `m`
    /// 
    /// # Example
    /// ```
    /// use self::immutable_chunkmap::map::MapM as Map;
    ///  
    /// let mut m = Map::from_iter((0..100).map(|k| (k, Map::from_iter(0..100).map(|k| (k, 1)))));
    /// let orig = m.clone();
    /// 
    /// if let Some(inner) = m.get_mut_cow(0) {
    ///     if let Some(v) = inner.get_mut_cow(0) {
    ///         *v += 1
    ///     }
    /// }
    /// 
    /// assert_eq!(m.get(0).and_then(|m| m.get(0)), Some(2));
    /// assert_eq!(orig.get(0).and_then(|m| m.get(0)), Some(1));
    /// ```
    pub fn get_mut_cow<'a, Q: ?Sized + Ord>(&'a mut self, k: &Q) -> Option<&'a mut V>
    where
        K: Borrow<Q>,
    {
        self.0.get_mut_cow(k)
    }

    /// return a new map with the mapping under k removed. If
    /// the binding existed in the old map return it. Runs in
    /// log(N) time and log(N) space, where N is the size of
    /// the map.
    pub fn remove<Q: Sized + Ord>(&self, k: &Q) -> (Self, Option<V>)
    where
        K: Borrow<Q>,
    {
        let (t, prev) = self.0.remove(k);
        (Map(t), prev)
    }

    /// remove in place using copy on write semantics if self is not a
    /// unique reference to the map. see `update_cow`.
    pub fn remove_cow<Q: Sized + Ord>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
    {
        self.0.remove_cow(k)
    }

    /// get the number of elements in the map O(1) time and space
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// return an iterator over the subset of elements in the
    /// map that are within the specified range.
    ///
    /// The returned iterator runs in O(log(N) + M) time, and
    /// constant space. N is the number of elements in the
    /// tree, and M is the number of elements you examine.
    ///
    /// if lbound >= ubound the returned iterator will be empty
    pub fn range<'a, Q, R>(&'a self, r: R) -> Iter<'a, R, Q, K, V, SIZE>
    where
        Q: Ord + ?Sized + 'a,
        K: Borrow<Q>,
        R: RangeBounds<Q> + 'a,
    {
        self.0.range(r)
    }
}

impl<K, V, const SIZE: usize> Map<K, V, SIZE>
where
    K: Ord + Clone + Debug,
    V: Clone + Debug,
{
    #[allow(dead_code)]
    pub fn invariant(&self) -> () {
        self.0.invariant()
    }
}
