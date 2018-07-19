use avl::{Tree, Iter};
use std::{
    cmp::{PartialEq, Eq, PartialOrd, Ord, Ordering},
    fmt::{self, Debug, Formatter}, borrow::Borrow,
    ops::{Bound, Index}, default::Default,
    hash::{Hash, Hasher}, iter::FromIterator
};

/// This Map uses a similar strategy to BTreeMap to ensure cache
/// efficient performance on modern hardware while still providing
/// log(N) get, insert, and remove operations.
///
/// For good performance, it is very important to understand
/// that clone is a fundamental operation, it needs to be fast
/// for your key and data types, because it's going to be
/// called a lot whenever you change the map. If your key and
/// data types are cheap to clone (like e.g. Arc), and you
/// perform your update operations in largish batches, then it
/// is possible to get very good performance, even approaching
/// that of a standard HashMap.
///
/// # Why
///
/// Which begs the question, why would anyone ever want to use
/// a data structure where very careful structuring of key and
/// data type, and careful batching, MIGHT APPROACH the
/// performance of a plain old HashMap, it seems a silly thing
/// to work on. I know of two cases.
///
/// 1. Multiple threads can read this structure even while one
/// thread is updating it.
///
/// 2. You can take a snapshot and e.g. write it to disk, or
/// replicate it to another process without stopping reads or
/// writes.
///
/// There is some nuance to #1, because HashMap is generally
/// faster to read than a BTree. In a pure read application
/// it's the obvious choice when you don't require sorted
/// data. In a mixed read/write scenario at 4 reads for every
/// write HashMap is already the same speed as chunkmap for
/// reading a 10M entry map. That's a pretty write heavy
/// application, and wouldn't be news by itself. The real
/// killer of the mutable strucures is large operations, any
/// kind of housekeeping operation that's going to touch a
/// large number of keys can be death for availability,
/// holding onto a write lock for multiple hundreds of
/// milliseconds, even seconds, even longer. Sure it's
/// possible to amortize this in some cases by doing your
/// housekeeping in small batches, but that can be complex,
/// and it isn't always possible, and readers still pay a
/// price even if it's amortized.
///
/// That brings us to #2, which is really the mother of all
/// housekeeping operations. There is no way to amortize
/// taking a consistent snapshot, the best you can possibly do
/// is hold the write lock long enough to make a complete copy
/// of the data, if you even have the memory for that. God
/// help you if you miscalculate and start swapping while
/// you're making that copy, holding the write lock while your
/// disk or if you're lucky SSD churns away moving pages back
/// and forth between main memory, you may be holding that
/// lock for a long long time. Chunkmap gives you free
/// snapshots in exchange for slower writes, which, carefully
/// considered don't even need to be that much slower.
///
/// # Examples
/// ```
/// use std::string::String;
/// use self::immutable_chunkmap::map::Map;
///
/// let m =
///    Map::new()
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
pub struct Map<K: Ord + Clone, V: Clone> {
    len: usize,
    root: Tree<K, V>
}

impl<K, V> Hash for Map<K, V>
where K: Hash + Ord + Clone, V: Hash + Clone {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.root.hash(state)
    }
}

impl<K, V> Default for Map<K, V>
where K: Ord + Clone, V: Clone {
    fn default() -> Map<K, V> { Map::new() }
}

impl<K, V> PartialEq for Map<K, V>
where K: PartialEq + Ord + Clone, V: PartialEq + Clone {
    fn eq(&self, other: &Map<K,V>) -> bool {
        self.len == other.len && self.root == other.root
    }
}

impl<K, V> Eq for Map<K, V>
where K: Eq + Ord + Clone, V: Eq + Clone {}

impl<K, V> PartialOrd for Map<K, V>
where K: Ord + Clone, V: PartialOrd + Clone {
    fn partial_cmp(&self, other: &Map<K, V>) -> Option<Ordering> {
        self.root.partial_cmp(&other.root)
    }
}

impl<K, V> Ord for Map<K, V>
where K: Ord + Clone, V: Ord + Clone {
    fn cmp(&self, other: &Map<K, V>) -> Ordering {
        self.root.cmp(&other.root)
    }
}

impl<K, V> Debug for Map<K, V>
where K: Debug + Ord + Clone, V: Debug + Clone {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result { self.root.fmt(f) }
}

impl<'a, Q, K, V> Index<&'a Q> for Map<K, V>
where Q: Ord, K: Ord + Clone + Borrow<Q>, V: Clone {
    type Output = V;
    fn index(&self, k: &Q) -> &V {
        self.get(k).expect("element not found for key")
    }
}

impl<K, V> FromIterator<(K, V)> for Map<K, V>
where K: Ord + Clone, V: Clone {
    fn from_iter<T: IntoIterator<Item=(K, V)>>(iter: T) -> Self {
        Map::new().insert_many(iter)
    }
}

impl<'a, K, V> IntoIterator for &'a Map<K, V>
where
    K: 'a + Borrow<K> + Ord + Clone,
    V: 'a + Clone
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, K, V>;
    fn into_iter(self) -> Self::IntoIter { self.root.into_iter() }
}

impl<K, V> Map<K, V> where K: Ord + Clone, V: Clone {
    /// Create a new empty map
    pub fn new() -> Self { Map { len: 0, root: Tree::new() } }

    /// This will insert many elements at once, and is
    /// potentially a lot faster than inserting one by one,
    /// especially if the data is sorted. It is just a wrapper
    /// around the more general update_many method.
    ///
    /// #Examples
    ///```
    /// use self::immutable_chunkmap::map::Map;
    ///
    /// let mut v = vec![(1, 3), (10, 1), (-12, 2), (44, 0), (50, -1)];
    /// v.sort_unstable_by_key(|&(k, _)| k);
    ///
    /// let m = Map::new().insert_many(v.iter().map(|(k, v)| (*k, *v)));
    ///
    /// for (k, v) in &v {
    ///   assert_eq!(m.get(k), Option::Some(v))
    /// }
    /// ```
    pub fn insert_many<E: IntoIterator<Item=(K, V)>>(
        &self, elts: E
    ) -> Self {
        let (root, len) = self.root.insert_many(self.len, elts);
        Map { len, root }
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
    /// use self::immutable_chunkmap::map::Map;
    ///
    /// let m = Map::new().insert_many((0..4).map(|k| (k, k)));
    /// let m = m.update_many(
    ///     (0..4).map(|x| (x, ())),
    ///     &mut |_, (), cur| cur.map(|c| c + 1)
    /// );
    /// assert_eq!(
    ///     m.into_iter().map(|(k, v)| (*k, *v)).collect::<Vec<_>>(),
    ///     vec![(0, 1), (1, 2), (2, 3), (3, 4)]
    /// );
    /// ```
    pub fn update_many<Q, D, E, F>(&self, elts: E, f: &mut F) -> Self
    where E: IntoIterator<Item=(Q, D)>, Q: Ord, K: Borrow<Q>,
          F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)> {
        let (root, len) = self.root.update_many(self.len, elts, f);
        Map { len, root }
    }

    /// return a new map with (k, v) inserted into it. If k
    /// already exists in the old map, the old binding will be
    /// returned, and the new map will contain the new
    /// binding. In fact this method is just a wrapper around
    /// update.
    pub fn insert(&self, k: K, v: V) -> (Self, Option<V>) {
        let (root, len, prev) = self.root.insert(self.len, k, v);
        (Map {len, root}, prev)
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
    /// use self::immutable_chunkmap::map::Map;
    ///
    /// let (m, _) = Map::new().update(0, 0, &mut |k, d, _| Some(d));
    /// let (m, _) = m.update(1, 1, &mut |k, d, _| Some(d));
    /// let (m, _) = m.update(2, 2, &mut |k, d, _| Some(d));
    /// assert_eq!(m.get(&0), Some(&0));
    /// assert_eq!(m.get(&1), Some(&1));
    /// assert_eq!(m.get(&2), Some(&2));
    ///
    /// let (m, _) = m.update(0, (), &mut |_, (), v| v.map(|v| v + 1));
    /// assert_eq!(m.get(&0), Some(&1));
    /// assert_eq!(m.get(&1), Some(&1));
    /// assert_eq!(m.get(&2), Some(&2));
    ///
    /// let (m, _) = m.update(1, (), &mut |_, (), _| None);
    /// assert_eq!(m.get(&0), Some(&1));
    /// assert_eq!(m.get(&1), None);
    /// assert_eq!(m.get(&2), Some(&2));
    /// ```
    pub fn update<Q, D, F>(&self, q: Q, d: D, f: &mut F) -> (Self, Option<V>)
    where Q: Ord, K: Borrow<Q>, F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)> {
        let (root, len, prev) = self.root.update(self.len, q, d, f);
        (Map {len, root}, prev)
    }

    /// lookup the mapping for k. If it doesn't exist return
    /// None. Runs in log(N) time and constant space. where N
    /// is the size of the map.
    pub fn get<'a, Q: ?Sized + Ord>(&'a self, k: &Q) -> Option<&'a V>
    where K: Borrow<Q>
    { self.root.get(k) }

    /// lookup the mapping for k. Return the key. If it doesn't exist
    /// return None. Runs in log(N) time and constant space. where N
    /// is the size of the map.
    pub fn get_key<'a, Q: ?Sized + Ord>(&'a self, k: &Q) -> Option<&'a K>
    where K: Borrow<Q>
    { self.root.get_key(k) }

    /// lookup the mapping for k. Return both the key and the
    /// value. If it doesn't exist return None. Runs in log(N) time
    /// and constant space. where N is the size of the map.
    pub fn get_full<'a, Q: ?Sized + Ord>(&'a self, k: &Q) -> Option<(&'a K, &'a V)>
    where K: Borrow<Q>
    { self.root.get_full(k) }

    /// return a new map with the mapping under k removed. If
    /// the binding existed in the old map return it. Runs in
    /// log(N) time and log(N) space, where N is the size of
    /// the map.
    pub fn remove<Q: Sized + Ord>(&self, k: &Q) -> (Self, Option<V>)
    where K: Borrow<Q>
    {
        let (t, len, prev) = self.root.remove(self.len, k);
        (Map {root: t, len: len}, prev)
    }

    /// get the number of elements in the map O(1) time and space
    pub fn len(&self) -> usize { self.len }

    /// return an iterator over the subset of elements in the
    /// map that are within the specified range.
    ///
    /// The returned iterator runs in O(log(N) + M) time, and
    /// constant space. N is the number of elements in the
    /// tree, and M is the number of elements you examine.
    ///
    /// if lbound >= ubound the returned iterator will be empty
    pub fn range<'a, Q>(
        &'a self, lbound: Bound<Q>, ubound: Bound<Q>
    ) -> Iter<'a, Q, K, V> where Q: Ord, K: Borrow<Q> {
        self.root.range(lbound, ubound)
    }
}

impl<K, V> Map<K, V> where K: Ord + Clone + Debug, V: Clone + Debug {
    #[allow(dead_code)]
    pub(crate) fn invariant(&self) -> () { self.root.invariant(self.len) }
}
