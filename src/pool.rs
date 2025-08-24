use crate::{avl::Node, chunk::ChunkInner};
use core::mem;
use fxhash::FxHashMap;
use poolshark::RawPool;
pub use poolshark::{
    arc::{Arc, Weak},
    Poolable,
};
use std::{cell::RefCell, collections::HashMap, sync::Arc as SArc};

struct ChunkPoolInner<K: Ord + Clone, V: Clone, const SIZE: usize> {
    chunk: RawPool<Arc<ChunkInner<K, V, SIZE>>>,
    node: RawPool<Arc<Node<K, V, SIZE>>>,
}

/// a chunk pool holds unused chunks in a thread safe queue so they can be
/// recycled. This reduces memory fragmentation, and allocation.
#[repr(transparent)]
pub struct ChunkPool<K: Ord + Clone, V: Clone, const SIZE: usize>(
    SArc<ChunkPoolInner<K, V, SIZE>>,
);

impl<K: Ord + Clone, V: Clone, const SIZE: usize> Clone for ChunkPool<K, V, SIZE> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<K: Ord + Clone, V: Clone, const SIZE: usize> ChunkPool<K, V, SIZE> {
    pub fn new(max_elts: usize) -> Self {
        ChunkPool(SArc::new(ChunkPoolInner {
            chunk: RawPool::new(max_elts, 1),
            node: RawPool::new(max_elts, 1),
        }))
    }

    pub(crate) fn take_chunk(&self) -> Arc<ChunkInner<K, V, SIZE>> {
        self.0.chunk.take()
    }

    pub(crate) fn new_node(&self, n: Node<K, V, SIZE>) -> Arc<Node<K, V, SIZE>> {
        Arc::new(&self.0.node, n)
    }
}

thread_local! {
    static POOLS: RefCell<FxHashMap<Discriminant, *const ()>> =
        RefCell::new(HashMap::default());
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Discriminant {
    k_size: usize,
    k_align: usize,
    v_size: usize,
    v_align: usize,
    size: usize,
}

impl Discriminant {
    fn new<K: Ord + Clone, V: Clone, const SIZE: usize>() -> Self {
        Self {
            k_size: mem::size_of::<K>(),
            k_align: mem::align_of::<K>(),
            v_size: mem::size_of::<V>(),
            v_align: mem::align_of::<V>(),
            size: SIZE,
        }
    }
}

// this is safe because chunks are reset before they are inserted into pools, so
// it is not possible for a chunk to have a K or a V (which might have a
// lifetime).
pub(crate) fn pool<K: Ord + Clone, V: Clone, const SIZE: usize>(
    size: usize,
) -> ChunkPool<K, V, SIZE> {
    POOLS.with_borrow_mut(|pools| {
        let pool = pools
            .entry(Discriminant::new::<K, V, SIZE>())
            .or_insert_with(|| {
                Box::into_raw(Box::new(ChunkPool::<K, V, SIZE>::new(size))) as *const ()
            });
        let pool = unsafe {
            mem::transmute::<&mut *const (), &mut Box<ChunkPool<K, V, SIZE>>>(pool)
        };
        (**pool).clone()
    })
}
