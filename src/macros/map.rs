macro_rules! map {
  ($treeimport:path) => {
    use $treeimport::{Tree, Iter};
    use std::fmt::Debug;
    use std::borrow::Borrow;

    /// This Map uses a similar strategy to BTreeMap to ensure cache
    /// efficient performance on modern hardware while still providing
    /// log(N) get, insert, and remove operations.
    /// # Examples
    /// ```
    /// use std::string::String;
    /// use self::immutable_chunkmap::rc::map::Map;
    ///
    /// let m =
    ///    Map::new()
    ///    .insert(&String::from("1"), &1)
    ///    .insert(&String::from("2"), &2)
    ///    .insert(&String::from("3"), &3);
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
      /// map (1/10 +). Assuming your elements are already sorted, or nearly sorted.
      ///
      /// A word of warning however. If you're inserting small chunks (< 1/10) relative to the size
      /// of the map, or your chunks are not sorted, this method will still work, but it may be
      /// significantly slower than adding each element one by one.
      ///
      /// Regardless of whether the input is sorted or not, and regardless of it's size relative to
      /// the size of the map, this method runs in log(N) time where N is the size of the map.
      /// #Examples
      /// ```
      /// use self::immutable_chunkmap::rc::map::Map;
      ///
      /// let v = vec![(1, 3), (10, 1), (-12, 2), (44, 0), (50, -1)];
      /// let mut refs: Vec<(&i64, &i64)> = v.iter().map(|&(ref k, ref v)| (k, v)).collect();
      /// refs.sort_unstable_by_key(|&(k, _)| k);
      ///
      /// let m = Map::new().insert_sorted(&refs);
      ///
      /// for &(ref k, ref v) in &v {
      ///   assert_eq!(m.get(k), Option::Some(v))
      /// }
      /// ```
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
      pub fn get<'a, Q: ?Sized + Ord + Debug>(&'a self, k: &Q) -> Option<&'a V>
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
