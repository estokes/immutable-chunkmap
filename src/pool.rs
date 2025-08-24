use crate::chunk::ChunkInner;
use core::mem;
use fxhash::FxHashMap;
use poolshark::RawPool;
pub use poolshark::{arc::Arc, Poolable};
use std::{cell::RefCell, collections::HashMap};

/// a chunk pool holds unused chunks in a thread safe queue so they can be
/// recycled. This reduces memory fragmentation, and allocation.
#[repr(transparent)]
pub struct ChunkPool<K, V, const SIZE: usize>(RawPool<Arc<ChunkInner<K, V, SIZE>>>);

impl<K, V, const SIZE: usize> Clone for ChunkPool<K, V, SIZE> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<K, V, const SIZE: usize> ChunkPool<K, V, SIZE> {
    pub fn new(max_elts: usize) -> Self {
        ChunkPool(RawPool::new(max_elts, 1))
    }

    pub(crate) fn take(&self) -> Arc<ChunkInner<K, V, SIZE>> {
        self.0.take()
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
    fn new<K, V, const SIZE: usize>() -> Self {
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
pub(crate) fn pool<K, V, const SIZE: usize>(size: usize) -> ChunkPool<K, V, SIZE> {
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
