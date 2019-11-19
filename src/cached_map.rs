use crate::avl::{Iter, Tree};
use std::{
    borrow::Borrow,
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    default::Default,
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
    iter::{self, FromIterator, IntoIterator, Iterator},
    ops::{Bound, Index},
    sync::Arc,
    slice
};

static CACHE_SIZE: usize = 128;

struct Node<T> {
    data: T,
    next: List<T>,
}

enum List<T> {
    Empty,
    Node(Arc<Node<T>>)
}

impl<T> Clone for List<T> {
    fn clone(&self) -> Self {
        match self {
            List::Empty => List::Empty,
            List::Node(n) => List::Node(n.clone())
        }
    }
}

impl<T> List<T> {
    fn empty() -> Self { List::Empty }

    fn push(&self, data: T) -> Self {
        let next = self.clone();
        List::Node(Arc::new(Node { data, next }))
    }

    fn hd(&self) -> Option<&T> {
        match self {
            List::Empty => None,
            List::Node(n) => Some(&n.data)
        }
    }

    fn tl(&self) -> Self {
        match self {
            List::Empty => List::Empty,
            List::Node(n) => n.next.clone()
        }
    }

    fn len(&self) -> usize {
        let mut len = 0;
        let mut hd = self;
        while let List::Node(n) = hd {
            len += 1;
            hd = &n.next
        }
        len
    }
}

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = ListIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        ListIter(self)
    }
}

struct ListIter<'a, T>(&'a List<T>);

impl<'a, T> Iterator for ListIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0 {
            List::Empty => None,
            List::Node(n) => {
                self.0 = &n.next;
                Some(&n.data)
            }
        }
    }
}


#[derive(Clone)]
enum CacheOp<V: Clone> {
    Updated(V),
    Removed
}

#[derive(Clone)]
struct Cache<K: Ord + Clone, V: Clone> {
    len: usize,
    data: List<(K, CacheOp<V>)>
}

impl<K, V> Cache<K, V> where K: Ord + Clone, V: Clone {
    fn empty() -> Self {
        Cache {
            len: 0,
            data: List::empty()
        }
    }

    fn get<Q: ?Sized + Ord>(&self, k: &Q) -> Option<(&K, &CacheOp<V>)>
    where K: Borrow<Q>
    {
        for (k0, v) in &self.data {
            if k == k0.borrow() {
                return Some((k0, v))
            }
        }
        None
    }

    fn len(&self) -> usize {
        self.len
    }
    
    fn update(&self, k: K, v: CacheOp<V>) -> Self {
        Cache {
            len: self.len + 1,
            data: self.data.push((k, v)),
        }
    }

    fn iter<'a>(&'a self) -> ListIter<'a, (K, CacheOp<V>)> {
        self.data.into_iter()
    }
}

#[derive(Clone)]
pub struct Map<K: Ord + Clone, V: Clone> {
    cache: Cache<K, V>,
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
            cache: Cache::empty(),
            root: Tree::new(),
        }
    }

    pub fn flush(&self) -> Self {
        if self.cache.len() == 0 {
            self.clone()
        } else {
            let items = self.cache.iter().map(|(k, v)| (k.clone(), v.clone()));
            let root = self.root.update_many(items, &mut |k, op, _| {
                match op {
                    CacheOp::Removed => None,
                    CacheOp::Updated(v) => Some((k, v))
                }
            });
            Map { root, cache: Cache::empty() }
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
            cache: self.cache.update(k, CacheOp::Updated(v)),
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
            Some((k, v)) => self.cache.update(k, CacheOp::Updated(v)),
            None => match prev {
                None => self.cache.clone(),
                Some((k, _)) => self.cache.update(k.clone(), CacheOp::Removed),
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
            cache: Cache::empty(),
            root: Tree::union(&self.flush().root, &other.flush().root, &mut f),
        }
    }

    pub fn intersect<F>(&self, other: &Map<K, V>, mut f: F) -> Self
    where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        Map {
            cache: Cache::empty(),
            root: Tree::intersect(&self.flush().root, &other.flush().root, &mut f)
        }
    }

    pub fn diff<F>(&self, other: &Map<K, V>, mut f: F) -> Self
    where F: FnMut(&K, &V, &V) -> Option<V>, K: Debug, V: Debug
    {
        Map {
            cache: Cache::empty(),
            root: Tree::diff(&self.flush().root, &other.flush().root, &mut f)
        }
    }

    pub fn get<'a, Q: ?Sized + Ord>(&'a self, k: &Q) -> Option<&'a V>
    where
        K: Borrow<Q>,
    {
        match self.cache.get(k) {
            None => self.root.get(k),
            Some((_, v)) => match v {
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
            None => self.root.get_key(k),
            Some((k, v)) => match v {
                CacheOp::Removed => None,
                CacheOp::Updated(_) => Some(&k)
            }
        }
    }

    pub fn get_full<'a, Q: ?Sized + Ord>(&'a self, k: &Q) -> Option<(&'a K, &'a V)>
    where
        K: Borrow<Q>,
    {
        match self.cache.get(k) {
            None => self.root.get_full(k),
            Some((k, v)) => match v {
                CacheOp::Removed => None,
                CacheOp::Updated(ref v) => Some((k, v))
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
        // CR estokes: This is broken
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
