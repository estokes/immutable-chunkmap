use crate::{
    avl::Tree,
    chunk::{Chunk, Update, SIZE},
};
use std::{borrow::Borrow, iter::Iterator};

#[derive(Clone)]
pub(crate) enum CacheAvl<K: Ord + Clone, V: Clone> {
    Tree(Tree<K, V>),
    Cached(Chunk<K, Option<V>>, Tree<K, V>),
}

impl<K: Ord + Clone, V: Clone> CacheAvl<K, V> {
    pub(crate) fn new(avl: Tree<K, V>) -> Self {
        CacheAvl::Tree(avl)
    }

    pub(crate) fn cached(&self) -> usize {
        match self {
            CacheAvl::Tree(_) => 0,
            CacheAvl::Cached(c, _) => c.len(),
        }
    }

    pub(crate) fn flush(&self) -> Tree<K, V> {
        match self {
            CacheAvl::Tree(t) => t.clone(),
            CacheAvl::Cached(cached, tree) => {
                let ops = cached.into_iter().map(|(k, op)| (k.clone(), op.clone()));
                tree.update_many(ops, &mut |k, op: Option<V>, _| op.map(|v| (k, v)))
            }
        }
    }

    pub(crate) fn insert(&self, k: K, v: V) -> (Self, Option<V>) {
        let prev = self.get(&k);
        if self.cached() == SIZE {
            let t = CacheAvl::Cached(Chunk::singleton(k, Some(v)), self.flush());
            (t, prev.cloned())
        } else {
            let t = match self {
                CacheAvl::Tree(t) => {
                    CacheAvl::Cached(Chunk::singleton(k, Some(v)), t.clone())
                }
                CacheAvl::Cached(chunk, t) => {
                    match chunk.update(k, Some(v), true, &mut |k, v, _| Some((k, v))) {
                        Update::Updated { elts, .. } => CacheAvl::Cached(elts, t.clone()),
                        Update::UpdateLeft(_, _) | Update::UpdateRight(_, _) => {
                            unreachable!()
                        }
                    }
                }
            };
            (t, prev.cloned())
        }
    }

    pub(crate) fn remove<Q>(&self, q: Q) -> (Self, Option<V>)
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        match self.get_full(&q) {
            None => (self.clone(), None),
            Some((k, v)) => {
                if self.cached() == SIZE {
                    let t = self.flush();
                    let chunk = Chunk::singleton(k.clone(), None);
                    (CacheAvl::Cached(chunk, t), Some(v.clone()))
                } else {
                    let t = match self {
                        CacheAvl::Tree(t) => {
                            let t = t.clone();
                            let chunk = Chunk::singleton(k.clone(), None);
                            CacheAvl::Cached(chunk, t)
                        }
                        CacheAvl::Cached(chunk, t) => {
                            match chunk.update(q, (), true, &mut |_, _, _| None) {
                                Update::Updated { elts, .. } => {
                                    CacheAvl::Cached(elts, t.clone())
                                }
                                Update::UpdateLeft(_, _) | Update::UpdateRight(_, _) => {
                                    unreachable!()
                                }
                            }
                        }
                    };
                    (t, Some(v.clone()))
                }
            }
        }
    }

    pub(crate) fn get<'a, Q>(&'a self, q: &Q) -> Option<&'a V>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        match self {
            CacheAvl::Tree(t) => t.get(q),
            CacheAvl::Cached(cached, t) => match cached.get_local(q) {
                None => t.get(q),
                Some(i) => cached.val(i).as_ref(),
            },
        }
    }

    pub(crate) fn get_key<'a, Q>(&'a self, q: &Q) -> Option<&'a K>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        match self {
            CacheAvl::Tree(t) => t.get_key(q),
            CacheAvl::Cached(cached, t) => match cached.get_local(q) {
                None => t.get_key(q),
                Some(i) => Some(cached.key(i)),
            },
        }
    }

    pub(crate) fn get_full<'a, Q>(&'a self, q: &Q) -> Option<(&'a K, &'a V)>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        match self {
            CacheAvl::Tree(t) => t.get_full(q),
            CacheAvl::Cached(cached, t) => match cached.get_local(q) {
                None => t.get_full(q),
                Some(i) => cached.val(i).as_ref().map(|v| (cached.key(i), v)),
            },
        }
    }
}
