use avl;
use std::fmt::Debug;
use std::borrow::Borrow;

#[derive(Clone)]
pub struct Map<K: Ord + Clone + Debug, V: Clone + Debug> {
  len: usize,
  root: avl::Tree<K, V>
}

impl<K,V> Map<K,V> where K: Ord + Clone + Debug, V: Clone + Debug {
  pub fn new() -> Self { Map { len: 0, root: avl::Tree::new() } }

  pub fn add(&self, k: &K, v: &V) -> Self {
    let (t, len) = self.root.add(self.len, k, v);
    Map { len: len, root: t }
  }

  pub fn find<'a, Q: ?Sized + Ord>(&'a self, k: &Q) -> Option<&'a V> 
    where K: Borrow<Q>
  { self.root.find(k) }

  pub fn remove<Q: ?Sized + Ord>(&self, k: &Q) -> Self 
    where K: Borrow<Q>
  {
    let (t, len) = self.root.remove(self.len, k);
    Map {root: t, len: len}
  }

  pub fn length(&self) -> usize { self.len }

  #[allow(dead_code)]
  pub(crate) fn invariant(&self) -> () { self.root.invariant(self.len) }
}
