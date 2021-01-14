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
    fn empty() -> Self {
        List::Nil
    }

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
struct CacheAvl<K: Ord + Clone, V: Clone> {
    cache: List<(K, Option<V>)>,
    avl: Tree<K, V>,
}

impl<K: Ord + Clone, V: Clone> CacheAvl<K, V> {
    pub(crate) fn fast_insert(&self, k: K, v: V) -> Self {
        CacheAvl {
            cache: self.cache.insert((k, Some(v))),
            avl: self.avl.clone(),
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
                    cache: self.cache.insert((k.clone(), None)),
                    avl: self.avl.clone(),
                };
                (t, Some(v.clone()))
            }
        }
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
