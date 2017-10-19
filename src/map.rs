use avl;

#[derive(Clone)]
pub struct Map<K: Ord + Clone, V: Clone> {
  len: usize,
  root: avl::Tree<K, V>
}

pub fn empty<K, V>() -> Map<K, V> where K: Ord + Clone, V: Clone {
  Map { len: 0, root: avl::empty() }
}

pub fn add<K, V>(t:&Map<K, V>, k: &K, v: &V) -> Map<K, V>
  where K: Ord + Clone, V: Clone
{
  let (t, len) = avl::add(&t.root, t.len, k, v);
  Map { len: len, root: t }
}

pub fn find<'a, K, V>(t:&'a Map<K, V>, k: &K) -> Option<&'a V>
  where K: Ord + Clone, V: Clone
{
  avl::find(&t.root, k)
}

pub fn remove<K, V>(t:&Map<K, V>, k: &K) -> Map<K,V>
  where K: Ord + Clone, V: Clone
{
  let (t, len) = avl::remove(&t.root, t.len, k);
  Map {root: t, len: len}
}

pub fn length<K, V>(t:&Map<K, V>) -> usize where K: Ord + Clone, V: Clone { t.len }

#[allow(dead_code)]
pub(crate) fn invariant<K, V>(t:&Map<K, V>) -> () where K: Ord + Clone, V: Clone {
  avl::invariant(&t.root, t.len)
}
