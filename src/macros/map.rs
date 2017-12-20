macro_rules! map {
  ($treeimport:path) => {
    use $treeimport::{Tree, Iter};
    use std::fmt::Debug;
    use std::borrow::Borrow;

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
      pub fn new() -> Self { Map { len: 0, root: Tree::new() } }

      pub fn insert_sorted(&self, elts: &[(&K, &V)]) -> Self {
        let (t, len) = self.root.insert_sorted(self.len, elts);
        Map { len: len, root: t }
      }

      pub fn insert(&self, k: &K, v: &V) -> Self {
        let (t, len) = self.root.insert(self.len, k, v);
        Map { len: len, root: t }
      }

      pub fn get<'a, Q: Sized + Ord + Debug>(&'a self, k: &Q) -> Option<&'a V> 
        where K: Borrow<Q>
      { self.root.get(k) }

      pub fn remove<Q: Sized + Ord>(&self, k: &Q) -> Self 
        where K: Borrow<Q>
      {
        let (t, len) = self.root.remove(self.len, k);
        Map {root: t, len: len}
      }

      pub fn length(&self) -> usize { self.len }

      #[allow(dead_code)]
      pub(crate) fn invariant(&self) -> () { self.root.invariant(self.len) }
    }
  };
}
