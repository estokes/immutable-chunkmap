use crate::chunk::ChunkInner;
pub use alloc::sync::Arc;
use core::marker::PhantomData;

pub trait Poolable {
    fn empty() -> Self;
    fn reset(&mut self);
    fn capacity(&self) -> usize;
}

/// a dummy, 0 sized, chunk pool
pub struct ChunkPool<K, V, const SIZE: usize>(PhantomData<K>, PhantomData<V>);

impl<K, V, const SIZE: usize> Clone for ChunkPool<K, V, SIZE> {
    fn clone(&self) -> Self {
        Self(PhantomData, PhantomData)
    }
}

impl<K, V, const SIZE: usize> ChunkPool<K, V, SIZE> {
    pub fn new(_max_elts: usize) -> Self {
        ChunkPool(PhantomData, PhantomData)
    }

    pub(crate) fn take(&self) -> Arc<ChunkInner<K, V, SIZE>> {
        Arc::new(ChunkInner::empty())
    }
}

pub(crate) fn pool<K, V, const SIZE: usize>(_size: usize) -> ChunkPool<K, V, SIZE> {
    ChunkPool(PhantomData, PhantomData)
}
