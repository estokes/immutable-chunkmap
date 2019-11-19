use crate::avl::{Iter, Tree};
use std::{
    borrow::Borrow,
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    default::Default,
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
    iter::{self, FromIterator},
    ops::{Bound, Index},
    sync::Arc,
    slice
};

static CACHE_SIZE: usize = 128;

struct Node<T> {
    data: T,
    next: List<T>,
}

#[derive(Clone)]
enum List<T> {
    Empty,
    Node(Arc<Node<T>>)
}

impl<T> List<T> {
    fn empty() -> Self { List::Emtpy }

    fn push(&self, data: T) -> Self {
        Node(Arc::new(Node { data, next: self.clone() }))
    }
}

#[derive(Clone)]
enum CacheOp<V: Clone> {
    Updated(V),
    Removed
}

#[derive(Clone)]
struct Cache<K: Ord + Clone, V: Clone> {
    keys: Vec<K>,
    vals: Vec<CacheOp<V>>
}

impl<'a, K, V> IntoIterator for &'a Cache<K, V>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
{
    type Item = (&'a K, &'a CacheOp<V>);
    type IntoIter = iter::Zip<slice::Iter<'a, K>, slice::Iter<'a, CacheOp<V>>>;
    fn into_iter(self) -> Self::IntoIter {
        (&self.keys).into_iter().zip(&self.vals)
    }
}

impl<K, V> Cache<K, V> where K: Ord + Clone, V: Clone {
    fn empty() -> Self {
        Cache {
            keys: Vec::new(),
            vals: Vec::new(),
        }
    }

    fn with_empty<F: FnOnce(&mut Cache<K, V>)>(f: F) -> Self {
        let mut cache = Cache::empty();
        f(&mut cache);
        cache
    }

    fn get<Q: ?Sized + Ord>(&self, k: &Q) -> Result<usize, usize>
    where K: Borrow<Q>
    {
        self.keys.binary_search_by_key(&k, |k| k.borrow())
    }

    fn len(&self) -> usize {
        self.keys.len()
    }
    
    fn update(&self, k: K, v: CacheOp<V>) -> Self {
        match self.get(&k) {
            Ok(i) => Cache::with_empty(|elts| {
                elts.keys.extend_from_slice(&self.keys[0..i]);
                elts.vals.extend_from_slice(&self.vals[0..i]);
                elts.keys.push(k);
                elts.vals.push(v);
                if i + 1 < self.len() {
                    elts.keys.extend_from_slice(&self.keys[i + 1..]);
                    elts.vals.extend_from_slice(&self.vals[i + 1..]);
                }
            }),
            Err(i) => Cache::with_empty(|elts| {
                elts.keys.extend_from_slice(&self.keys[0..i]);
                elts.vals.extend_from_slice(&self.vals[0..i]);
                elts.keys.push(k);
                elts.vals.push(v);
                elts.keys.extend_from_slice(&self.keys[i..]);
                elts.vals.extend_from_slice(&self.vals[i..]);
            })
        }
    }
}

#[derive(Clone)]
pub struct Map<K: Ord + Clone, V: Clone> {
    cache: Arc<Cache<K, V>>,
    root: Tree<K, V>
}


impl<K, V> Debug for Map<K, V>
where
    K: Debug + Ord + Clone,
    V: Debug + Clone,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.root.fmt(f)
    }
}

impl<'a, Q, K, V> Index<&'a Q> for Map<K, V>
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

impl<K, V> FromIterator<(K, V)> for Map<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Map::new().insert_many(iter)
    }
}

impl<'a, K, V> IntoIterator for &'a Map<K, V>
where
    K: 'a + Borrow<K> + Ord + Clone,
    V: 'a + Clone,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        if self.cache.len() > 0 {
            panic!("you must flush before iter")
        }
        self.root.into_iter()
    }
}

impl<K, V> Map<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    /// Create a new empty map
    pub fn new() -> Self {
        Map {
            cache: Arc::new(Cache::empty()),
            root: Tree::new(),
        }
    }

    pub fn flush(&self) -> Self {
        if self.cache.len() == 0 {
            self.clone()
        } else {
            let items = self.cache.into_iter().map(|(k, v)| (k.clone(), v.clone()));
            let root = self.root.update_many(items, &mut |k, op, _| {
                match op {
                    CacheOp::Removed => None,
                    CacheOp::Updated(v) => Some((k, v))
                }
            });
            Map { root, cache: Arc::new(Cache::empty()) }
        }
    }

    pub fn insert_many<E: IntoIterator<Item = (K, V)>>(&self, elts: E) -> Self {
        let m = self.flush();
        Map {
            cache: m.cache,
            root: m.root.insert_many(elts),
        }
    }

    pub fn update_many<Q, D, E, F>(&self, elts: E, mut f: F) -> Self
    where
        E: IntoIterator<Item = (Q, D)>,
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        let m = self.flush();
        Map {
            cache: m.cache,
            root: m.root.update_many(elts, &mut f),
        }
    }

    pub fn insert(&self, k: K, v: V) -> (Self, Option<V>) {
        let prev = self.get(&k);
        let m = Map {
            cache: Arc::new(self.cache.update(k, CacheOp::Updated(v))),
            root: self.root.clone()
        };
        if m.cache.len() <= CACHE_SIZE {
            (m, prev.cloned())
        } else {
            (m.flush(), prev.cloned())
        }
    }

    pub fn update<Q, D, F>(&self, q: Q, d: D, mut f: F) -> (Self, Option<V>)
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        let prev = self.get_full(&q);
        let cache = match f(q, d, prev) {
            Some((k, v)) => Arc::new(self.cache.update(k, CacheOp::Updated(v))),
            None => match prev {
                None => self.cache.clone(),
                Some((k, _)) => Arc::new(self.cache.update(k.clone(), CacheOp::Removed)),
            }
        };
        let m = Map { cache, root: self.root.clone() };
        let prev = prev.map(|(_, v)| v.clone());
        if m.cache.len() <= CACHE_SIZE {
            (m, prev)
        } else {
            (m.flush(), prev)
        }
    }

    pub fn union<F>(&self, other: &Map<K, V>, mut f: F) -> Self
    where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        Map {
            cache: Arc::new(Cache::empty()),
            root: Tree::union(&self.flush().root, &other.flush().root, &mut f),
        }
    }

    pub fn intersect<F>(&self, other: &Map<K, V>, mut f: F) -> Self
    where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        Map {
            cache: Arc::new(Cache::empty()),
            root: Tree::intersect(&self.flush().root, &other.flush().root, &mut f)
        }
    }

    pub fn diff<F>(&self, other: &Map<K, V>, mut f: F) -> Self
    where F: FnMut(&K, &V, &V) -> Option<V>, K: Debug, V: Debug
    {
        Map {
            cache: Arc::new(Cache::empty()),
            root: Tree::diff(&self.flush().root, &other.flush().root, &mut f)
        }
    }

    pub fn get<'a, Q: ?Sized + Ord>(&'a self, k: &Q) -> Option<&'a V>
    where
        K: Borrow<Q>,
    {
        match self.cache.get(k) {
            Err(_) => self.root.get(k),
            Ok(i) => match self.cache.vals[i] {
                CacheOp::Removed => None,
                CacheOp::Updated(ref v) => Some(v)
            }
        }
    }

    pub fn get_key<'a, Q: ?Sized + Ord>(&'a self, k: &Q) -> Option<&'a K>
    where
        K: Borrow<Q>,
    {
        match self.cache.get(k) {
            Err(_) => self.root.get_key(k),
            Ok(i) => match self.cache.vals[i] {
                CacheOp::Removed => None,
                CacheOp::Updated(_) => Some(&self.cache.keys[i])
            }
        }
    }

    pub fn get_full<'a, Q: ?Sized + Ord>(&'a self, k: &Q) -> Option<(&'a K, &'a V)>
    where
        K: Borrow<Q>,
    {
        match self.cache.get(k) {
            Err(_) => self.root.get_full(k),
            Ok(i) => match self.cache.vals[i] {
                CacheOp::Removed => None,
                CacheOp::Updated(ref v) => Some((&self.cache.keys[i], v))
            }
        }
    }

    pub fn remove<Q: Sized + Ord + Clone>(&self, k: &Q) -> (Self, Option<V>)
    where
        K: Borrow<Q>,
    {
        self.update(k.clone(), (), |k, (), _| None)
    }

    pub fn len(&self) -> usize {
        // CR estokes: this is way too expensive
        self.flush().root.len()
    }

    pub fn range<'a, Q>(&'a self, lbound: Bound<Q>, ubound: Bound<Q>) -> Iter<'a, Q, K, V>
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        // CR estokes: this is broken
        self.root.range(lbound, ubound)
    }
}

impl<K, V> Map<K, V>
where
    K: Ord + Clone + Debug,
    V: Clone + Debug,
{
    #[allow(dead_code)]
    pub fn invariant(&self) -> () {
        self.root.invariant()
    }
}
