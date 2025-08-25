use crate::{avl::Node, chunk::ChunkInner};
use core::alloc::Layout;
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

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Discriminant {
    k: Layout,
    v: Layout,
    size: usize,
}

impl Discriminant {
    fn new<K: Ord + Clone, V: Clone, const SIZE: usize>() -> Self {
        Self {
            k: Layout::new::<K>(),
            v: Layout::new::<V>(),
            size: SIZE,
        }
    }
}

struct Opaque {
    t: *mut (),
    drop: Option<Box<dyn FnOnce(*mut ())>>,
}

impl Drop for Opaque {
    fn drop(&mut self) {
        if let Some(f) = self.drop.take() {
            f(self.t)
        }
    }
}

thread_local! {
    static POOLS: RefCell<FxHashMap<Discriminant, Opaque>> =
        RefCell::new(HashMap::default());
}

// This is safe because:
// 1. Chunks are reset before being returned to pools, so they contain no active K or V values
// 2. We only reuse pools for types with identical memory layouts (same size/alignment via Discriminant)
// 3. The Opaque wrapper ensures proper cleanup when the thread local is destroyed
pub(crate) fn pool<K: Ord + Clone, V: Clone, const SIZE: usize>(
    size: usize,
) -> ChunkPool<K, V, SIZE> {
    POOLS.with_borrow_mut(|pools| {
        let pool = pools
            .entry(Discriminant::new::<K, V, SIZE>())
            .or_insert_with(|| {
                let b = Box::new(ChunkPool::<K, V, SIZE>::new(size));
                let t = Box::into_raw(b) as *mut ();
                let drop = Some(Box::new(|t: *mut ()| unsafe {
                    drop(Box::from_raw(t as *mut ChunkPool<K, V, SIZE>))
                }) as Box<dyn FnOnce(*mut ())>);
                Opaque { t, drop }
            });
        unsafe { &*(pool.t as *const ChunkPool<K, V, SIZE>) }.clone()
    })
}
