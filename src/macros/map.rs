macro_rules! map {
    ($treeimport:path) => {
        use $treeimport::{Tree, Iter};
        use std::{fmt::Debug, borrow::Borrow, ops::Bound};

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

        impl<'a, K, V> IntoIterator for &'a Map<K, V>
        where
            K: 'a + Borrow<K> + Ord + Clone + Debug,
            V: 'a + Clone + Debug
        {
            type Item = (&'a K, &'a V);
            type IntoIter = Iter<'a, K, K, V>;
            fn into_iter(self) -> Self::IntoIter { self.root.into_iter() }
        }

        impl<K, V> Map<K, V> where K: Ord + Clone + Debug, V: Clone + Debug {
            /// Create a new empty map
            pub fn new() -> Self { Map { len: 0, root: Tree::new() } }

            /// This method inserts many elements at once, skipping
            /// the intermediate node allocations where possible,
            /// which in most cases provides a significant speedup. It
            /// is able to skip more allocations if the data is
            /// sorted, however it will still work with unsorted data.
            ///
            /// #Examples
            ///```
            /// use self::immutable_chunkmap::rc::map::Map;
            ///
            /// let mut v = vec![(1, 3), (10, 1), (-12, 2), (44, 0), (50, -1)];
            /// v.sort_unstable_by_key(|&(k, _)| k);
            ///
            /// let m = Map::new().insert_sorted(v.iter().map(|(k, v)| (*k, *v)));
            ///
            /// for (k, v) in &v {
            ///   assert_eq!(m.get(k), Option::Some(v))
            /// }
            /// ```
            pub fn insert_sorted<E: IntoIterator<Item=(K, V)>>(
                &self, elts: E
            ) -> Self {
                let (t, len) = self.root.insert_sorted(self.len, elts);
                Map { len: len, root: t }
            }

            /// return a new map with (k, v) inserted into it. If k already
            /// exists in the old map, the new map will contain the new
            /// binding, not the old. This method runs in log(N) time, where
            /// N is the size of the map. `k` and `v` will be cloned on
            /// insert, and on subsuquent inserts or removals, if `k` or `v`
            /// is expensive to clone, pass an `Rc` or `Arc` pointer to it
            /// instead. A `Box` won't work, because it can't be shared, so
            /// clone will deep copy the contents.
            pub fn insert(&self, k: &K, v: &V) -> Self {
                let (t, len) = self.root.insert(self.len, k, v);
                Map { len: len, root: t }
            }

            /// lookup the mapping for k. If it doesn't exist return
            /// None. Runs in log(N) time where N is the size of the
            /// map.
            pub fn get<'a, Q: ?Sized + Ord + Debug>(&'a self, k: &Q) -> Option<&'a V>
            where K: Borrow<Q>
            { self.root.get(k) }

            /// return a new map with the mapping under k
            /// removed. Runs in log(N) time, where N is the size of
            /// the map
            pub fn remove<Q: Sized + Ord>(&self, k: &Q) -> Self
            where K: Borrow<Q>
            {
                let (t, len) = self.root.remove(self.len, k);
                Map {root: t, len: len}
            }

            /// get the number of elements in the map O(1)
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

            #[allow(dead_code)]
            pub(crate) fn invariant(&self) -> () { self.root.invariant(self.len) }
        }
    };
}
