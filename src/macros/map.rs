macro_rules! map {
  ($treeimport:path) => {
    use $treeimport::{Tree, Iter};
    use std::fmt::Debug;
    use std::borrow::Borrow;

    /// This module uses a similar strategy to BTreeMap to ensure cache
    /// efficient performance on modern hardware while still providing
    /// log(N) get, insert, and remove operations.
    ///     There are however a few notable differences between this module and BTreeMap.
    /// The tree algorithm is a classic AVL balanced binary tree. However each node contains a
    /// sorted array instead of a single key/value pair. Instead of a linear scan through the array
    /// (as in BTreeMap) we binary search. This means that our map will always perform the optimal
    /// (log(N)) number of comparison operations. In situations where comparison is very cheap
    /// BTreeMap may be slightly faster, where as in situations where comparison is more expensive
    /// this module may be slightly faster, though the measured performance difference with i64
    /// keys (cheap) is quite small. This module does not use unsafe, as BTreeMap does. Because it
    /// is immutable insert and remove are much more expensive than for BTreeMap, but the advantage
    /// is that previous versions are still valid. This is an intrinsic property of immutable data
    /// structures. The Arc version of this structure is well suited to multi threaded
    /// applications. In particular it is safe to insert/remove without blocking reader threads, as
    /// they can simply be given the previous version of the structure.

    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Map<K: Ord + Clone + Debug, V: Clone + Debug> {
      len: usize,
      root: Tree<K, V>
    }

    impl<'a,K,V> IntoIterator for &'a Map<K,V>
      where K: 'a + Ord + Clone + Debug, V: 'a + Clone + Debug
    {
      type Item = (&'a K, &'a V);
      type IntoIter = Iter<'a, K, V>;
      fn into_iter(self) -> Self::IntoIter { self.root.into_iter() }
    }

    impl<K,V> Map<K,V> where K: Ord + Clone + Debug, V: Clone + Debug {
      /// Create a new empty map
      pub fn new() -> Self { Map { len: 0, root: Tree::new() } }

      /// This method of insertion can be orders of magnitude faster than inserting elements one by
      /// one. Assuming you are inserting a large number of elements relative to the size of the
      /// map (1/10 +). Assuming your elements are already sorted, or nearly sorted. The reason it
      /// can be so much faster is we can avoid building every intermediate tree, as would be
      /// produced when adding one by one, and go almost straight to the final tree.
      ///
      /// A word of warning however. If you're inserting small chunks (< 1/10) relative to the size
      /// of the map, or your chunks are not sorted, this method will still work, but it will be
      /// significantly slower than adding each element one by one.
      ///
      /// Regardless of whether the input is sorted or not, and regardless of it's size relative to
      /// the size of the map, this method is log(N) where N is the size of the map.
      pub fn insert_sorted(&self, elts: &[(&K, &V)]) -> Self {
        let (t, len) = self.root.insert_sorted(self.len, elts);
        Map { len: len, root: t }
      }

      /// return a new map with (k, v) inserted into it. If k already exists in the old map, the
      /// new map will contain the new binding, not the old. This method runs in log(N) time, where
      /// N is the size of the map.
      pub fn insert(&self, k: &K, v: &V) -> Self {
        let (t, len) = self.root.insert(self.len, k, v);
        Map { len: len, root: t }
      }

      /// lookup the mapping for k. If it doesn't exist return None. Runs in log(N) time where N is
      /// the size of the map.
      pub fn get<'a, Q: Sized + Ord + Debug>(&'a self, k: &Q) -> Option<&'a V>
        where K: Borrow<Q>
      { self.root.get(k) }

      /// return a new map with the mapping under k removed. Runs in log(N) time, where N is the
      /// size of the map
      pub fn remove<Q: Sized + Ord>(&self, k: &Q) -> Self
        where K: Borrow<Q>
      {
        let (t, len) = self.root.remove(self.len, k);
        Map {root: t, len: len}
      }

      /// get the number of elements in the map O(1)
      pub fn length(&self) -> usize { self.len }

      #[allow(dead_code)]
      pub(crate) fn invariant(&self) -> () { self.root.invariant(self.len) }
    }
  };
}
