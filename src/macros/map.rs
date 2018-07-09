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

            /// This will insert many elements at once, and is
            /// potentially a lot faster than inserting one by one,
            /// especially if the data is sorted. It is just a wrapper
            /// around the more general update_many method.
            ///
            /// #Examples
            ///```
            /// use self::immutable_chunkmap::rc::map::Map;
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

            /// This method updates multiple bindings in one call.
            /// Given an iterator of an arbitrary type D, a key
            /// extraction function on D, an update function taking D,
            /// the current binding in the map, if any, and producing
            /// the new binding, if any, this method will produce a
            /// new map with updated bindings of many elements at
            /// once. It will skip intermediate node allocations where
            /// possible. If the data in elts is sorted, it will be
            /// able to skip many more intermediate allocations, and
            /// can produce a speedup of about 10x compared to
            /// inserting/updating one by one. In some cases it can be
            /// as fast as using a hashmap.
            ///
            /// This method will panic if kf, and uf return
            /// inconsistent keys.
            ///
            /// #Examples
            /// ```
            /// use self::immutable_chunkmap::rc::map::Map;
            ///
            /// let m = Map::new().insert_many(0..4.map(|k| (k, k)));
            /// let m = m.update_many(
            ///     0..4,
            ///     &mut |k| k,
            ///     &mut |k, cur| Some((*k, cur.unwrap() + 1))
            /// );
            /// assert_eq!(
            ///     m.into_iter().map(|(k, v)| (*k, *v)).collect<Vec<_>>(),
            ///     vec![(0, 1), (1, 2), (2, 3), (3, 4)]
            /// );
            /// ```
            pub fn update_many<D, E, F>(&self, elts: E, f: &mut F) -> Self
            where E: IntoIterator<Item=(K, D)>,
                  F: FnMut(&K, D, Option<&V>) -> Option<V> {
                let (root, len) = self.root.update_many(self.len, elts, f);
                Map { len, root }
            }

            /// return a new map with (k, v) inserted into it. If k
            /// already exists in the old map, the old binding will be
            /// returned, and the new map will contain the new
            /// binding. In fact this method is just a wrapper around
            /// update.
            pub fn insert(&self, k: K, v: V) -> (Self, Option<(K, V)>) {
                let (root, len, prev) = self.root.insert(self.len, k, v);
                (Map {len, root}, prev)
            }

            /// return a new map with the binding for k updated to the
            /// result of f. If f returns None, the binding will be
            /// removed from the new map, otherwise it will be
            /// inserted. This function is more efficient than calling
            /// `get` and then `insert`, since it makes only one tree
            /// traversal instead of two. This method runs in log(N)
            /// time and space where N is the size of the map.
            ///
            /// # Examples
            /// ```
            /// use self::immutable_chunkmap::rc::map::Map;
            ///
            /// let m = Map::new().update(0, 0, &mut |k, d, _| Some(d))
            /// assert_eq!(m.get(0), Some(0));
            ///
            /// let m = m.update(0, (), &mut |_, (), v| v.map(|v| v + 1));
            /// assert_eq!(m.get(0), Some(1));
            /// ```
            pub fn update<D, F>(&self, k: K, d: D, f: &mut F) -> (Self, Option<(K, V)>)
            where F: FnMut(&K, D, Option<&V>) -> Option<V> {
                let (root, len, prev) = self.root.update(self.len, k, d, f);
                (Map {len, root}, prev)
            }

            /// lookup the mapping for k. If it doesn't exist return
            /// None. Runs in log(N) time and constant space. where N
            /// is the size of the map.
            pub fn get<'a, Q: ?Sized + Ord + Debug>(&'a self, k: &Q) -> Option<&'a V>
            where K: Borrow<Q>
            { self.root.get(k) }

            /// return a new map with the mapping under k
            /// removed. Runs in log(N) time and log(N) space, where N
            /// is the size of the map
            pub fn remove<Q: Sized + Ord>(&self, k: &Q) -> Self
            where K: Borrow<Q>
            {
                let (t, len) = self.root.remove(self.len, k);
                Map {root: t, len: len}
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

            #[allow(dead_code)]
            pub(crate) fn invariant(&self) -> () { self.root.invariant(self.len) }
        }
    };
}
