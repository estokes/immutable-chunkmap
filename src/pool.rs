use crate::{avl::NodeInner, chunk::ChunkInner};
use core::{alloc::Layout, hash::Hash};
use fxhash::FxHashMap;
use std::{
    cell::RefCell,
    collections::HashMap,
    sync::{Arc, LazyLock, Mutex},
};

pub(crate) struct Pool<K: Ord + Clone, V: Clone, const SIZE: usize> {
    pub(crate) max: usize,
    pub(crate) chunks: Vec<Arc<ChunkInner<K, V, SIZE>>>,
    pub(crate) nodes: Vec<Arc<NodeInner<K, V, SIZE>>>,
}

impl<K: Ord + Clone, V: Clone, const SIZE: usize> Pool<K, V, SIZE> {
    fn new(max: usize) -> Self {
        Self {
            max,
            chunks: Vec::with_capacity(max),
            nodes: Vec::with_capacity(max),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ULayout(u16);

impl ULayout {
    fn new<T>() -> Option<Self> {
        let l = Layout::new::<T>();
        let size = l.size();
        let align = l.align();
        if size >= 0xFFFF {
            return None;
        }
        if align > 0x0F {
            return None;
        }
        Some(Self(((size << 4) | (0x0F & align)) as u16))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Discriminant {
    k: ULayout,
    v: ULayout,
    size: u16,
}

impl Discriminant {
    fn new<K, V, const SIZE: usize>() -> Option<Self> {
        if SIZE >= 0xFFFF {
            return None;
        }
        Some(Self {
            k: ULayout::new::<K>()?,
            v: ULayout::new::<V>()?,
            size: SIZE as u16,
        })
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

static SIZES: LazyLock<Mutex<FxHashMap<Discriminant, usize>>> =
    LazyLock::new(|| Mutex::new(FxHashMap::default()));

// This is safe because:
// 1. Chunks are reset before being returned to pools, so they contain no active K or V values
// 2. We only reuse pools for types with identical memory layouts (same size/alignment via Discriminant)
// 3. The Opaque wrapper ensures proper cleanup when the thread local is destroyed
pub(crate) fn with_pool<K, V, R, F, const SIZE: usize>(f: F) -> R
where
    K: Ord + Clone,
    V: Clone,
    F: FnOnce(Option<&mut Pool<K, V, SIZE>>) -> R,
{
    POOLS.with_borrow_mut(|pools| match Discriminant::new::<K, V, SIZE>() {
        Some(d) => {
            let pool = pools.entry(d).or_insert_with(|| {
                let size = *SIZES.lock().unwrap().get(&d).unwrap_or(&1024);
                let b = Box::new(Pool::<K, V, SIZE>::new(size));
                let t = Box::into_raw(b) as *mut ();
                let drop = Some(Box::new(|t: *mut ()| unsafe {
                    drop(Box::from_raw(t as *mut Pool<K, V, SIZE>))
                }) as Box<dyn FnOnce(*mut ())>);
                Opaque { t, drop }
            });
            f(unsafe { Some(&mut *(pool.t as *mut Pool<K, V, SIZE>)) })
        }
        None => f(None),
    })
}

/// Clear all thread local pools on this thread. Note this will happen
/// automatically when the thread dies.
pub fn clear() {
    POOLS.with_borrow_mut(|pools| pools.clear())
}

/// Delete the thread local pool for the specified K, V and SIZE. This will
/// happen automatically when the current thread dies.
pub fn clear_type<K, V, const SIZE: usize>() {
    POOLS.with_borrow_mut(|pools| {
        if let Some(d) = Discriminant::new::<K, V, SIZE>() {
            pools.remove(&d);
        }
    })
}

/// Set the pool size for this type. Pools that have already been created will
/// not be resized, but new pools (on new threads) will use the specified size
/// as their max size. If you wish to resize an existing pool you can first
/// clear_type (or clear) and then set_size.
pub fn set_size<K, V, const SIZE: usize>(size: usize) {
    if let Some(d) = Discriminant::new::<K, V, SIZE>() {
        SIZES.lock().unwrap().insert(d, size);
    }
}
