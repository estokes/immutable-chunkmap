use avl;

struct Map<K: Ord + Clone, V: Clone> {
  len: u64,
  root: avl::Tree<K, V>
}
