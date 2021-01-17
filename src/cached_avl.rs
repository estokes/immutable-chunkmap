use crate::avl::Tree;
use std::{
    borrow::Borrow,
    iter::{IntoIterator, Iterator},
    sync::Arc,
};

#[derive(Debug, Clone)]
enum List<T> {
    Nil,
    Head(Arc<(T, List<T>)>),
}

impl<T> List<T> {
    fn insert(&self, v: T) -> Self {
        let tl = match self {
            List::Nil => List::Nil,
            List::Head(a) => List::Head(Arc::clone(a)),
        };
        List::Head(Arc::new((v, tl)))
    }

    fn iter(&self) -> impl Iterator<Item = &T> {
        self.into_iter()
    }

    // examine every element in the list until a match is found,
    // replace that match with the result of f. Not tail recursive.
    fn replace(
        &self,
        test: impl Fn(usize, &T) -> bool,
        update: impl FnOnce(&T) -> T,
    ) -> Self
    where
        T: Clone,
    {
        fn replace_inner<T>(
            t: &List<T>,
            i: usize,
            test: impl Fn(usize, &T) -> bool,
            update: impl FnOnce(&T) -> T,
        ) -> List<T>
        where
            T: Clone,
        {
            match t {
                List::Nil => List::Nil,
                List::Head(a) => {
                    if test(i, &a.0) {
                        List::Head(Arc::new((
                            a.0.clone(),
                            replace_inner(&a.1, i + 1, test, update),
                        )))
                    } else {
                        List::Head(Arc::new((update(&a.0), a.1.clone())))
                    }
                }
            }
        }
        replace_inner(self, 0, test, update)
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

    fn next(&mut self) -> Option<&'a T> {
        match &self.0 {
            List::Nil => None,
            List::Head(a) => {
                self.0 = &a.1;
                Some(&a.0)
            }
        }
    }
}

#[derive(Clone)]
pub(crate) struct CacheAvl<K: Ord + Clone, V: Clone> {
    cached: usize,
    cache: List<(K, Option<V>)>,
    avl: Tree<K, V>,
}

impl<K: Ord + Clone, V: Clone> CacheAvl<K, V> {
    pub(crate) fn new() -> Self {
        CacheAvl {
            cached: 0,
            cache: List::Nil,
            avl: Tree::new(),
        }
    }

    pub(crate) fn wrap(avl: Tree<K, V>) -> Self {
        CacheAvl {
            cached: 0,
            cache: List::Nil,
            avl,
        }
    }

    pub(crate) fn is_flushed(&self) -> bool {
        self.cached() == 0
    }

    pub(crate) fn flush(&self) -> Self {
        let ops = self.cache.iter().map(|(k, op)| (k.clone(), op.clone()));
        let avl = self
            .avl
            .update_many(ops, &mut |k, op: Option<V>, _| op.map(|v| (k, v)));
        CacheAvl {
            cached: 0,
            cache: List::Nil,
            avl,
        }
    }

    pub(crate) fn fast_insert(&self, k: K, v: V) -> Self {
        CacheAvl {
            cached: self.cached + 1,
            cache: self.cache.insert((k, Some(v))),
            avl: self.avl.clone(),
        }
    }

    pub fn update<Q, D, F>(&self, q: Q, d: D, mut f: F) -> (Self, Option<V>)
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        match self
            .cache
            .iter()
            .enumerate()
            .find(|(_, (k, _))| k.borrow() == &q)
        {
            None => {
                let cached = self.cached;
                let cache = self.cache.clone();
                let (avl, prev) = self.avl.update(q, d, &mut f);
                (CacheAvl { cached, cache, avl }, prev)
            }
            Some((i, _)) => {
                let mut prev = None;
                let prox_prev = &mut prev;
                let cache = self.cache.replace(
                    |j, _| i == j,
                    move |(k, v)| {
                        *prox_prev = v.clone();
                        let kv = match v {
                            None => None,
                            Some(v) => Some((k, v)),
                        };
                        match f(q, d, kv) {
                            None => (k.clone(), None),
                            Some((k, v)) => (k, Some(v)),
                        }
                    },
                );
                let t = CacheAvl {
                    cached: self.cached,
                    cache,
                    avl: self.avl.clone(),
                };
                (t, prev)
            }
        }
    }

    pub(crate) fn insert(&self, k: K, v: V) -> (Self, Option<V>) {
        let prev = self.get(&k).cloned();
        (self.fast_insert(k, v), prev)
    }

    pub(crate) fn remove<Q>(&self, q: &Q) -> (Self, Option<V>)
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        match self.get_full(q) {
            None => (self.clone(), None),
            Some((k, v)) => {
                let t = CacheAvl {
                    cached: self.cached + 1,
                    cache: self.cache.insert((k.clone(), None)),
                    avl: self.avl.clone(),
                };
                (t, Some(v.clone()))
            }
        }
    }

    pub(crate) fn tree(&self) -> &Tree<K, V> {
        &self.avl
    }

    pub(crate) fn cached(&self) -> usize {
        self.cached
    }

    pub(crate) fn get<'a, Q>(&'a self, q: &Q) -> Option<&'a V>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        match self.cache.iter().find(|(k, _)| k.borrow() == q) {
            None => self.avl.get(q),
            Some((_, v)) => v.as_ref(),
        }
    }

    pub(crate) fn get_key<'a, Q>(&'a self, q: &Q) -> Option<&'a K>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        match self.cache.iter().find(|(k, _)| k.borrow() == q) {
            None => self.avl.get_key(q),
            Some((k, _)) => Some(k),
        }
    }

    pub(crate) fn get_full<'a, Q>(&'a self, q: &Q) -> Option<(&'a K, &'a V)>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        match self.cache.iter().find(|(k, _)| k.borrow() == q) {
            None => self.avl.get_full(q),
            Some((k, Some(v))) => Some((k, v)),
            Some((_, None)) => None,
        }
    }
}
