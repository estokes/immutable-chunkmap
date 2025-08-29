use crate::chunk::{Chunk, Loc, MutUpdate, Update, UpdateChunk};
use alloc::{
    sync::{Arc, Weak},
    vec::Vec,
};
use arrayvec::ArrayVec;
#[cfg(feature = "pool")]
use core::hint::unreachable_unchecked;
use core::{
    borrow::Borrow,
    cmp::{max, min, Eq, Ord, Ordering, PartialEq, PartialOrd},
    default::Default,
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
    iter,
    marker::PhantomData,
    ops::{Bound, Deref, Index, RangeBounds, RangeFull},
    slice,
};

#[cfg(feature = "pool")]
use core::{mem::ManuallyDrop, ptr};
#[cfg(feature = "pool")]
use poolshark::{
    container_id_once,
    local::{insert_raw, take},
    ContainerId, Discriminant, LocalPoolable, Poolable,
};

// until we get 128 bit machines with exabytes of memory
const MAX_DEPTH: usize = 64;

fn pack_height_and_size(height: u8, size: usize) -> u64 {
    assert!((size & 0x00ffffff_ffffffff) == size);
    ((height as u64) << 56) | (size as u64)
}

#[cfg(feature = "pool")]
#[derive(Clone, Debug)]
pub(crate) struct NodeInner<K: Ord + Clone, V: Clone, const SIZE: usize> {
    elts: Option<Chunk<K, V, SIZE>>, // only none in pool
    min_key: Option<K>,              // only none in pool
    max_key: Option<K>,              // only none in pool
    left: Tree<K, V, SIZE>,
    right: Tree<K, V, SIZE>,
    height_and_size: u64,
}

#[cfg(feature = "pool")]
pub(crate) struct Node<K: Ord + Clone, V: Clone, const SIZE: usize>(
    ManuallyDrop<Arc<NodeInner<K, V, SIZE>>>,
);

#[cfg(feature = "pool")]
impl<K: Ord + Clone, V: Clone, const SIZE: usize> Poolable for Node<K, V, SIZE> {
    fn capacity(&self) -> usize {
        1
    }

    fn empty() -> Self {
        let n = NodeInner {
            elts: None,
            min_key: None,
            max_key: None,
            left: Tree::Empty,
            right: Tree::Empty,
            height_and_size: 0,
        };
        Node(ManuallyDrop::new(Arc::new(n)))
    }

    fn really_dropped(&mut self) -> bool {
        Arc::get_mut(&mut *self.0).is_some()
    }

    fn reset(&mut self) {
        Arc::get_mut(&mut self.0).unwrap().reset()
    }
}

#[cfg(feature = "pool")]
unsafe impl<K: Ord + Clone, V: Clone, const SIZE: usize> LocalPoolable
    for Node<K, V, SIZE>
{
    fn discriminant() -> Option<Discriminant> {
        let id = container_id_once!();
        dbg!(Discriminant::new_p1::<NodeInner<K, V, SIZE>>(id))
    }
}

#[cfg(feature = "pool")]
impl<K: Ord + Clone, V: Clone, const SIZE: usize> Drop for Node<K, V, SIZE> {
    fn drop(&mut self) {
        match Arc::get_mut(&mut self.0) {
            None => unsafe { ManuallyDrop::drop(&mut self.0) },
            Some(inner) => {
                inner.reset();
                if let Some(mut n) = unsafe { insert_raw(ptr::read(self)) } {
                    unsafe { ManuallyDrop::drop(&mut n.0) }
                }
            }
        }
    }
}

#[cfg(feature = "pool")]
impl<K: Ord + Clone, V: Clone, const SIZE: usize> Clone for Node<K, V, SIZE> {
    fn clone(&self) -> Self {
        Self(ManuallyDrop::new(Arc::clone(&*self.0)))
    }
}

#[cfg(not(feature = "pool"))]
#[derive(Clone, Debug)]
pub(crate) struct NodeInner<K: Ord + Clone, V: Clone, const SIZE: usize> {
    elts: Chunk<K, V, SIZE>,
    min_key: K,
    max_key: K,
    left: Tree<K, V, SIZE>,
    right: Tree<K, V, SIZE>,
    height_and_size: u64,
}

#[cfg(not(feature = "pool"))]
pub(crate) struct Node<K: Ord + Clone, V: Clone, const SIZE: usize>(
    Arc<NodeInner<K, V, SIZE>>,
);

#[cfg(not(feature = "pool"))]
impl<K: Ord + Clone, V: Clone, const SIZE: usize> Clone for Node<K, V, SIZE> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl<K: Ord + Clone, V: Clone, const SIZE: usize> Deref for Node<K, V, SIZE> {
    type Target = NodeInner<K, V, SIZE>;

    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl<K: Ord + Clone, V: Clone, const SIZE: usize> Node<K, V, SIZE> {
    fn downgrade(&self) -> WeakNode<K, V, SIZE> {
        WeakNode(Arc::downgrade(&self.0))
    }
}

#[derive(Clone)]
pub(crate) struct WeakNode<K: Ord + Clone, V: Clone, const SIZE: usize>(
    Weak<NodeInner<K, V, SIZE>>,
);

impl<K: Ord + Clone, V: Clone, const SIZE: usize> WeakNode<K, V, SIZE> {
    fn upgrade(&self) -> Option<Node<K, V, SIZE>> {
        #[cfg(feature = "pool")]
        {
            Weak::upgrade(&self.0).map(|n| Node(ManuallyDrop::new(n)))
        }
        #[cfg(not(feature = "pool"))]
        {
            Weak::upgrade(&self.0).map(Node)
        }
    }
}

impl<K, V, const SIZE: usize> NodeInner<K, V, SIZE>
where
    K: Ord + Clone,
    V: Clone,
{
    #[cfg(feature = "pool")]
    fn reset(&mut self) {
        let Self {
            elts,
            min_key,
            max_key,
            left,
            right,
            height_and_size,
        } = self;
        *elts = None;
        *min_key = None;
        *max_key = None;
        *left = Tree::Empty;
        *right = Tree::Empty;
        *height_and_size = 0
    }

    // a node that is not in the pool will never have elts set to None
    #[cfg(feature = "pool")]
    fn elts(&self) -> &Chunk<K, V, SIZE> {
        match &self.elts {
            Some(e) => e,
            None => unsafe { unreachable_unchecked() },
        }
    }

    #[cfg(not(feature = "pool"))]
    fn elts(&self) -> &Chunk<K, V, SIZE> {
        &self.elts
    }

    // a node that is not in the pool will never have elts set to None
    #[cfg(feature = "pool")]
    fn elts_mut(&mut self) -> &mut Chunk<K, V, SIZE> {
        match &mut self.elts {
            Some(e) => e,
            None => unsafe { unreachable_unchecked() },
        }
    }

    #[cfg(not(feature = "pool"))]
    fn elts_mut(&mut self) -> &mut Chunk<K, V, SIZE> {
        &mut self.elts
    }

    // a node that is not in the pool will never have min_key set to None
    #[cfg(feature = "pool")]
    fn min_key(&self) -> &K {
        match &self.min_key {
            Some(k) => k,
            None => unsafe { unreachable_unchecked() },
        }
    }

    #[cfg(not(feature = "pool"))]
    fn min_key(&self) -> &K {
        &self.min_key
    }

    // a node that is not in the pool will never have max_key set to None
    #[cfg(feature = "pool")]
    fn max_key(&self) -> &K {
        match &self.max_key {
            Some(k) => k,
            None => unsafe { unreachable_unchecked() },
        }
    }

    #[cfg(not(feature = "pool"))]
    fn max_key(&self) -> &K {
        &self.max_key
    }

    fn height(&self) -> u8 {
        (self.height_and_size >> 56) as u8
    }

    fn mutated(&mut self) {
        #[cfg(not(feature = "pool"))]
        if let Some((min, max)) = self.elts().min_max_key() {
            self.min_key = min;
            self.max_key = max;
        }
        #[cfg(feature = "pool")]
        if let Some((min, max)) = self.elts().min_max_key() {
            self.min_key = Some(min);
            self.max_key = Some(max);
        }
        self.height_and_size = pack_height_and_size(
            1 + max(self.left.height(), self.right.height()),
            self.left.len() + self.right.len(),
        );
    }
}

#[derive(Clone)]
pub(crate) enum WeakTree<K: Ord + Clone, V: Clone, const SIZE: usize> {
    Empty,
    Node(WeakNode<K, V, SIZE>),
}

impl<K: Ord + Clone, V: Clone, const SIZE: usize> WeakTree<K, V, SIZE> {
    pub(crate) fn upgrade(&self) -> Option<Tree<K, V, SIZE>> {
        match self {
            WeakTree::Empty => Some(Tree::Empty),
            WeakTree::Node(n) => n.upgrade().map(Tree::Node),
        }
    }
}

#[derive(Clone)]
pub(crate) enum Tree<K: Ord + Clone, V: Clone, const SIZE: usize> {
    Empty,
    Node(Node<K, V, SIZE>),
}

impl<K, V, const SIZE: usize> Hash for Tree<K, V, SIZE>
where
    K: Hash + Ord + Clone,
    V: Hash + Clone,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        for elt in self {
            elt.hash(state)
        }
    }
}

impl<K, V, const SIZE: usize> Default for Tree<K, V, SIZE>
where
    K: Ord + Clone,
    V: Clone,
{
    fn default() -> Tree<K, V, SIZE> {
        Tree::Empty
    }
}

impl<K, V, const SIZE: usize> PartialEq for Tree<K, V, SIZE>
where
    K: PartialEq + Ord + Clone,
    V: PartialEq + Clone,
{
    fn eq(&self, other: &Tree<K, V, SIZE>) -> bool {
        self.len() == other.len() && self.into_iter().zip(other).all(|(e0, e1)| e0 == e1)
    }
}

impl<K, V, const SIZE: usize> Eq for Tree<K, V, SIZE>
where
    K: Eq + Ord + Clone,
    V: Eq + Clone,
{
}

impl<K, V, const SIZE: usize> PartialOrd for Tree<K, V, SIZE>
where
    K: Ord + Clone,
    V: PartialOrd + Clone,
{
    fn partial_cmp(&self, other: &Tree<K, V, SIZE>) -> Option<Ordering> {
        self.into_iter().partial_cmp(other.into_iter())
    }
}

impl<K, V, const SIZE: usize> Ord for Tree<K, V, SIZE>
where
    K: Ord + Clone,
    V: Ord + Clone,
{
    fn cmp(&self, other: &Tree<K, V, SIZE>) -> Ordering {
        self.into_iter().cmp(other.into_iter())
    }
}

impl<K, V, const SIZE: usize> Debug for Tree<K, V, SIZE>
where
    K: Debug + Ord + Clone,
    V: Debug + Clone,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_map().entries(self.into_iter()).finish()
    }
}

impl<'a, Q, K, V, const SIZE: usize> Index<&'a Q> for Tree<K, V, SIZE>
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

pub struct Iter<'a, R, Q, K, V, const SIZE: usize>
where
    Q: Ord + ?Sized,
    R: RangeBounds<Q> + 'a,
    K: 'a + Borrow<Q> + Ord + Clone,
    V: 'a + Clone,
{
    q: PhantomData<Q>,
    stack: ArrayVec<(bool, &'a Node<K, V, SIZE>), MAX_DEPTH>,
    elts: Option<iter::Zip<slice::Iter<'a, K>, slice::Iter<'a, V>>>,
    current: Option<&'a K>,
    stack_rev: ArrayVec<(bool, &'a Node<K, V, SIZE>), MAX_DEPTH>,
    elts_rev: Option<iter::Zip<slice::Iter<'a, K>, slice::Iter<'a, V>>>,
    current_rev: Option<&'a K>,
    bounds: R,
}

impl<'a, R, Q, K, V, const SIZE: usize> Iter<'a, R, Q, K, V, SIZE>
where
    Q: Ord + ?Sized,
    R: RangeBounds<Q> + 'a,
    K: 'a + Borrow<Q> + Ord + Clone,
    V: 'a + Clone,
{
    // is at least one element of the chunk in bounds
    fn any_elts_above_lbound(&self, n: &'a Node<K, V, SIZE>) -> bool {
        let l = n.elts().len();
        match self.bounds.start_bound() {
            Bound::Unbounded => true,
            Bound::Included(bound) => l == 0 || n.elts().key(l - 1).borrow() >= bound,
            Bound::Excluded(bound) => l == 0 || n.elts().key(l - 1).borrow() > bound,
        }
    }

    fn any_elts_below_ubound(&self, n: &'a Node<K, V, SIZE>) -> bool {
        let l = n.elts().len();
        match self.bounds.end_bound() {
            Bound::Unbounded => true,
            Bound::Included(bound) => l == 0 || n.elts().key(0).borrow() <= bound,
            Bound::Excluded(bound) => l == 0 || n.elts().key(0).borrow() < bound,
        }
    }

    fn any_elts_in_bounds(&self, n: &'a Node<K, V, SIZE>) -> bool {
        self.any_elts_above_lbound(n) && self.any_elts_below_ubound(n)
    }

    fn above_lbound(&self, k: &'a K) -> bool {
        match self.bounds.start_bound() {
            Bound::Unbounded => true,
            Bound::Included(bound) => k.borrow() >= bound,
            Bound::Excluded(bound) => k.borrow() > bound,
        }
    }

    fn below_ubound(&self, k: &'a K) -> bool {
        match self.bounds.end_bound() {
            Bound::Unbounded => true,
            Bound::Included(bound) => k.borrow() <= bound,
            Bound::Excluded(bound) => k.borrow() < bound,
        }
    }
}

impl<'a, R, Q, K, V, const SIZE: usize> Iterator for Iter<'a, R, Q, K, V, SIZE>
where
    Q: Ord + ?Sized,
    R: RangeBounds<Q> + 'a,
    K: 'a + Borrow<Q> + Ord + Clone,
    V: 'a + Clone,
{
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            loop {
                let (k, v) = match &mut self.elts {
                    None => break,
                    Some(s) => match s.next() {
                        Some((k, v)) => (k, v),
                        None => break,
                    },
                };
                if let Some(back) = self.current_rev {
                    if k >= back {
                        return None;
                    }
                }
                if !self.below_ubound(k) {
                    return None;
                }
                self.current = Some(k);
                if self.above_lbound(k) {
                    return Some((k, v));
                }
            }
            if self.stack.is_empty() {
                return None;
            }
            self.elts = None;
            let top = self.stack.len() - 1;
            let (visited, current) = self.stack[top];
            if visited {
                if self.any_elts_in_bounds(current) {
                    self.elts = Some(current.elts().into_iter());
                }
                self.stack.pop();
                match current.right {
                    Tree::Empty => (),
                    Tree::Node(ref n) => {
                        if self.any_elts_below_ubound(n) || !n.left.is_empty() {
                            self.stack.push((false, n))
                        }
                    }
                };
            } else {
                self.stack[top].0 = true;
                match current.left {
                    Tree::Empty => (),
                    Tree::Node(ref n) => {
                        if self.any_elts_above_lbound(n) || !n.right.is_empty() {
                            self.stack.push((false, n))
                        }
                    }
                }
            }
        }
    }
}

impl<'a, R, Q, K, V, const SIZE: usize> DoubleEndedIterator for Iter<'a, R, Q, K, V, SIZE>
where
    Q: Ord + ?Sized,
    R: RangeBounds<Q> + 'a,
    K: 'a + Borrow<Q> + Ord + Clone,
    V: 'a + Clone,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            loop {
                let (k, v) = match &mut self.elts_rev {
                    &mut None => break,
                    &mut Some(ref mut s) => match s.next_back() {
                        None => break,
                        Some((k, v)) => (k, v),
                    },
                };
                if let Some(front) = self.current {
                    if k <= front {
                        return None;
                    }
                }
                if !self.above_lbound(k) {
                    return None;
                }
                self.current_rev = Some(k);
                if self.below_ubound(k) {
                    return Some((k, v));
                }
            }
            if self.stack_rev.is_empty() {
                return None;
            }
            self.elts_rev = None;
            let top = self.stack_rev.len() - 1;
            let (visited, current) = self.stack_rev[top];
            if visited {
                if self.any_elts_in_bounds(current) {
                    self.elts_rev = Some(current.elts().into_iter());
                }
                self.stack_rev.pop();
                match current.left {
                    Tree::Empty => (),
                    Tree::Node(ref n) => {
                        if self.any_elts_above_lbound(n) || !n.right.is_empty() {
                            self.stack_rev.push((false, n))
                        }
                    }
                };
            } else {
                self.stack_rev[top].0 = true;
                match current.right {
                    Tree::Empty => (),
                    Tree::Node(ref n) => {
                        if self.any_elts_below_ubound(n) || !n.left.is_empty() {
                            self.stack_rev.push((false, n))
                        }
                    }
                }
            }
        }
    }
}

pub struct IterMut<'a, R, Q, K, V, const SIZE: usize>
where
    Q: Ord + ?Sized,
    R: RangeBounds<Q> + 'a,
    K: 'a + Borrow<Q> + Ord + Clone,
    V: 'a + Clone,
{
    q: PhantomData<Q>,
    stack: ArrayVec<(bool, *mut Node<K, V, SIZE>), MAX_DEPTH>,
    elts: Option<iter::Zip<slice::Iter<'a, K>, slice::IterMut<'a, V>>>,
    current: Option<&'a K>,
    stack_rev: ArrayVec<(bool, *mut Node<K, V, SIZE>), MAX_DEPTH>,
    elts_rev: Option<iter::Zip<slice::Iter<'a, K>, slice::IterMut<'a, V>>>,
    current_rev: Option<&'a K>,
    bounds: R,
}

impl<'a, R, Q, K, V, const SIZE: usize> IterMut<'a, R, Q, K, V, SIZE>
where
    Q: Ord + ?Sized,
    R: RangeBounds<Q> + 'a,
    K: 'a + Borrow<Q> + Ord + Clone,
    V: 'a + Clone,
{
    // is at least one element of the chunk in bounds
    fn any_elts_above_lbound(&self, n: &'a NodeInner<K, V, SIZE>) -> bool {
        let l = n.elts().len();
        match self.bounds.start_bound() {
            Bound::Unbounded => true,
            Bound::Included(bound) => l == 0 || n.elts().key(l - 1).borrow() >= bound,
            Bound::Excluded(bound) => l == 0 || n.elts().key(l - 1).borrow() > bound,
        }
    }

    fn any_elts_below_ubound(&self, n: &'a NodeInner<K, V, SIZE>) -> bool {
        let l = n.elts().len();
        match self.bounds.end_bound() {
            Bound::Unbounded => true,
            Bound::Included(bound) => l == 0 || n.elts().key(0).borrow() <= bound,
            Bound::Excluded(bound) => l == 0 || n.elts().key(0).borrow() < bound,
        }
    }

    fn any_elts_in_bounds(&self, n: &'a NodeInner<K, V, SIZE>) -> bool {
        self.any_elts_above_lbound(n) && self.any_elts_below_ubound(n)
    }

    fn above_lbound(&self, k: &'a K) -> bool {
        match self.bounds.start_bound() {
            Bound::Unbounded => true,
            Bound::Included(bound) => k.borrow() >= bound,
            Bound::Excluded(bound) => k.borrow() > bound,
        }
    }

    fn below_ubound(&self, k: &'a K) -> bool {
        match self.bounds.end_bound() {
            Bound::Unbounded => true,
            Bound::Included(bound) => k.borrow() <= bound,
            Bound::Excluded(bound) => k.borrow() < bound,
        }
    }
}

impl<'a, R, Q, K, V, const SIZE: usize> Iterator for IterMut<'a, R, Q, K, V, SIZE>
where
    Q: Ord + ?Sized,
    R: RangeBounds<Q> + 'a,
    K: 'a + Borrow<Q> + Ord + Clone,
    V: 'a + Clone,
{
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            loop {
                let (k, v) = match &mut self.elts {
                    &mut None => break,
                    &mut Some(ref mut s) => match s.next() {
                        Some((k, v)) => (k, v),
                        None => break,
                    },
                };
                if let Some(back) = self.current_rev {
                    if k >= back {
                        return None;
                    }
                }
                if !self.below_ubound(k) {
                    return None;
                }
                self.current = Some(k);
                if self.above_lbound(k) {
                    return Some((k, v));
                }
            }
            if self.stack.is_empty() {
                return None;
            }
            self.elts = None;
            let top = self.stack.len() - 1;
            let (visited, current) = self.stack[top];
            if visited {
                if self.any_elts_in_bounds(unsafe { &*current }) {
                    self.elts = Some(
                        (unsafe { (Arc::make_mut(&mut (*current).0)).elts_mut() })
                            .into_iter(),
                    );
                }
                self.stack.pop();
                match unsafe { &mut (Arc::make_mut(&mut (*current).0)).right } {
                    Tree::Empty => (),
                    Tree::Node(ref mut n) => {
                        if self.any_elts_below_ubound(n) || !n.left.is_empty() {
                            self.stack.push((false, n))
                        }
                    }
                };
            } else {
                self.stack[top].0 = true;
                match unsafe { &mut (Arc::make_mut(&mut (*current).0)).left } {
                    Tree::Empty => (),
                    Tree::Node(n) => {
                        if self.any_elts_above_lbound(n) || !n.right.is_empty() {
                            self.stack.push((false, n))
                        }
                    }
                }
            }
        }
    }
}

impl<'a, R, Q, K, V, const SIZE: usize> DoubleEndedIterator
    for IterMut<'a, R, Q, K, V, SIZE>
where
    Q: Ord + ?Sized,
    R: RangeBounds<Q> + 'a,
    K: 'a + Borrow<Q> + Ord + Clone,
    V: 'a + Clone,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            loop {
                let (k, v) = match &mut self.elts_rev {
                    &mut None => break,
                    &mut Some(ref mut s) => match s.next_back() {
                        None => break,
                        Some((k, v)) => (k, v),
                    },
                };
                if let Some(front) = self.current {
                    if k <= front {
                        return None;
                    }
                }
                if !self.above_lbound(k) {
                    return None;
                }
                self.current_rev = Some(k);
                if self.below_ubound(k) {
                    return Some((k, v));
                }
            }
            if self.stack_rev.is_empty() {
                return None;
            }
            self.elts_rev = None;
            let top = self.stack_rev.len() - 1;
            let (visited, current) = self.stack_rev[top];
            if visited {
                if self.any_elts_in_bounds(unsafe { &*current }) {
                    self.elts_rev = Some(
                        (unsafe { (Arc::make_mut(&mut (*current).0)).elts_mut() })
                            .into_iter(),
                    );
                }
                self.stack_rev.pop();
                match unsafe { &mut (Arc::make_mut(&mut (*current).0)).left } {
                    Tree::Empty => (),
                    Tree::Node(ref mut n) => {
                        if self.any_elts_above_lbound(n) || !n.right.is_empty() {
                            self.stack_rev.push((false, n))
                        }
                    }
                };
            } else {
                self.stack_rev[top].0 = true;
                match unsafe { &mut (Arc::make_mut(&mut (*current).0)).right } {
                    Tree::Empty => (),
                    Tree::Node(ref mut n) => {
                        if self.any_elts_below_ubound(n) || !n.left.is_empty() {
                            self.stack_rev.push((false, n))
                        }
                    }
                }
            }
        }
    }
}

impl<'a, K, V, const SIZE: usize> IntoIterator for &'a Tree<K, V, SIZE>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, RangeFull, K, K, V, SIZE>;
    fn into_iter(self) -> Self::IntoIter {
        self.range(..)
    }
}

impl<K, V, const SIZE: usize> Tree<K, V, SIZE>
where
    K: Ord + Clone,
    V: Clone,
{
    pub(crate) fn new() -> Self {
        Tree::Empty
    }

    pub(crate) fn downgrade(&self) -> WeakTree<K, V, SIZE> {
        match self {
            Tree::Empty => WeakTree::Empty,
            Tree::Node(n) => WeakTree::Node(n.downgrade()),
        }
    }

    pub(crate) fn strong_count(&self) -> usize {
        match self {
            Tree::Empty => 0,
            Tree::Node(n) => Arc::strong_count(&n.0),
        }
    }

    pub(crate) fn weak_count(&self) -> usize {
        match self {
            Tree::Empty => 0,
            Tree::Node(n) => Arc::weak_count(&n.0),
        }
    }

    pub(crate) fn range<'a, Q, R>(&'a self, r: R) -> Iter<'a, R, Q, K, V, SIZE>
    where
        Q: Ord + ?Sized + 'a,
        K: Borrow<Q>,
        R: RangeBounds<Q> + 'a,
    {
        match self {
            &Tree::Empty => Iter {
                q: PhantomData,
                bounds: r,
                stack: ArrayVec::<_, MAX_DEPTH>::new(),
                elts: None,
                current: None,
                stack_rev: ArrayVec::<_, MAX_DEPTH>::new(),
                elts_rev: None,
                current_rev: None,
            },
            &Tree::Node(ref n) => {
                let mut stack =
                    ArrayVec::<(bool, &'a Node<K, V, SIZE>), MAX_DEPTH>::new();
                let mut stack_rev =
                    ArrayVec::<(bool, &'a Node<K, V, SIZE>), MAX_DEPTH>::new();
                stack.push((false, n));
                stack_rev.push((false, n));
                Iter {
                    q: PhantomData,
                    bounds: r,
                    stack,
                    elts: None,
                    current: None,
                    stack_rev,
                    elts_rev: None,
                    current_rev: None,
                }
            }
        }
    }

    pub(crate) fn range_mut_cow<'a, Q, R>(
        &'a mut self,
        r: R,
    ) -> IterMut<'a, R, Q, K, V, SIZE>
    where
        Q: Ord + ?Sized + 'a,
        K: Borrow<Q>,
        R: RangeBounds<Q> + 'a,
    {
        match self {
            Tree::Empty => IterMut {
                q: PhantomData,
                bounds: r,
                stack: ArrayVec::<_, MAX_DEPTH>::new(),
                elts: None,
                current: None,
                stack_rev: ArrayVec::<_, MAX_DEPTH>::new(),
                elts_rev: None,
                current_rev: None,
            },
            Tree::Node(ref mut n) => {
                let mut stack =
                    ArrayVec::<(bool, *mut Node<K, V, SIZE>), MAX_DEPTH>::new();
                let mut stack_rev =
                    ArrayVec::<(bool, *mut Node<K, V, SIZE>), MAX_DEPTH>::new();
                stack.push((false, n));
                stack_rev.push((false, n));
                IterMut {
                    q: PhantomData,
                    bounds: r,
                    stack,
                    elts: None,
                    current: None,
                    stack_rev,
                    elts_rev: None,
                    current_rev: None,
                }
            }
        }
    }

    pub(crate) fn iter_mut_cow<'a, Q>(
        &'a mut self,
    ) -> IterMut<'a, RangeFull, Q, K, V, SIZE>
    where
        Q: Ord + ?Sized + 'a,
        K: Borrow<Q>,
    {
        self.range_mut_cow(..)
    }

    fn add_min_elts(&self, elts: &Chunk<K, V, SIZE>) -> Self {
        match self {
            Tree::Empty => Tree::create(&Tree::Empty, elts.clone(), &Tree::Empty),
            Tree::Node(ref n) => {
                Tree::bal(&n.left.add_min_elts(elts), n.elts().clone(), &n.right)
            }
        }
    }

    fn add_max_elts(&self, elts: &Chunk<K, V, SIZE>) -> Self {
        match self {
            Tree::Empty => Tree::create(&Tree::Empty, elts.clone(), &Tree::Empty),
            Tree::Node(ref n) => {
                Tree::bal(&n.left, n.elts().clone(), &n.right.add_max_elts(elts))
            }
        }
    }

    // This is the same as create except it makes no assumption about the tree
    // heights or tree balance, so you can pass it anything, and it will return
    // a balanced tree.
    fn join(
        l: &Tree<K, V, SIZE>,
        elts: &Chunk<K, V, SIZE>,
        r: &Tree<K, V, SIZE>,
    ) -> Self {
        match (l, r) {
            (Tree::Empty, _) => r.add_min_elts(elts),
            (_, Tree::Empty) => l.add_max_elts(elts),
            (Tree::Node(ref ln), Tree::Node(ref rn)) => {
                let (ln_height, rn_height) = (ln.height(), rn.height());
                if ln_height > rn_height + 2 {
                    Tree::bal(
                        &ln.left,
                        ln.elts().clone(),
                        &Tree::join(&ln.right, elts, r),
                    )
                } else if rn_height > ln_height + 2 {
                    Tree::bal(
                        &Tree::join(l, elts, &rn.left),
                        rn.elts().clone(),
                        &rn.right,
                    )
                } else {
                    Tree::create(l, elts.clone(), r)
                }
            }
        }
    }

    /// split the tree according to elts, return two balanced trees
    /// representing all the elements less than and greater than elts,
    /// if there is a possible intersection return the intersecting
    /// chunk. In the case of an intersection there may also be an
    /// intersection at the left and/or right nodes.
    fn split(&self, vmin: &K, vmax: &K) -> (Self, Option<Chunk<K, V, SIZE>>, Self) {
        match self {
            Tree::Empty => (Tree::Empty, None, Tree::Empty),
            Tree::Node(ref n) => {
                if vmax < n.min_key() {
                    let (ll, inter, rl) = n.left.split(vmin, vmax);
                    (ll, inter, Tree::join(&rl, n.elts(), &n.right))
                } else if vmin > n.max_key() {
                    let (lr, inter, rr) = n.right.split(vmin, vmax);
                    (Tree::join(&n.left, n.elts(), &lr), inter, rr)
                } else {
                    (n.left.clone(), Some(n.elts().clone()), n.right.clone())
                }
            }
        }
    }

    /// merge all the values in the root node of from into to, and
    /// return from with it's current root remove, and to with the
    /// elements merged.
    fn merge_root_to<F>(
        from: &Tree<K, V, SIZE>,
        to: &Tree<K, V, SIZE>,
        f: &mut F,
    ) -> (Self, Self)
    where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        match (from, to) {
            (Tree::Empty, to) => (Tree::Empty, to.clone()),
            (Tree::Node(ref n), to) => {
                let to =
                    to.update_chunk(n.elts().to_vec(), &mut |k0, v0, cur| match cur {
                        None => Some((k0, v0)),
                        Some((_, v1)) => f(&k0, &v0, v1).map(|v| (k0, v)),
                    });
                if n.height() == 1 {
                    (Tree::Empty, to)
                } else {
                    match n.right {
                        Tree::Empty => (n.left.clone(), to),
                        Tree::Node(_) => {
                            let elts = n.right.min_elts().unwrap();
                            let right = n.right.remove_min_elts();
                            (Tree::join(&n.left, elts, &right), to)
                        }
                    }
                }
            }
        }
    }

    /// merge two trees, where f is run on the intersection. O(log(n)
    /// + m) where n is the size of the largest tree, and m is the number of
    /// intersecting chunks.
    pub(crate) fn union<F>(
        t0: &Tree<K, V, SIZE>,
        t1: &Tree<K, V, SIZE>,
        f: &mut F,
    ) -> Self
    where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        match (t0, t1) {
            (Tree::Empty, Tree::Empty) => Tree::Empty,
            (Tree::Empty, t1) => t1.clone(),
            (t0, Tree::Empty) => t0.clone(),
            (Tree::Node(ref n0), Tree::Node(ref n1)) => {
                if n0.height() > n1.height() {
                    match t1.split(n0.min_key(), n0.max_key()) {
                        (_, Some(_), _) => {
                            let (t0, t1) = Tree::merge_root_to(&t0, &t1, f);
                            Tree::union(&t0, &t1, f)
                        }
                        (l1, None, r1) => Tree::join(
                            &Tree::union(&n0.left, &l1, f),
                            n0.elts(),
                            &Tree::union(&n0.right, &r1, f),
                        ),
                    }
                } else {
                    match t0.split(n1.min_key(), n1.max_key()) {
                        (_, Some(_), _) => {
                            let (t1, t0) = Tree::merge_root_to(&t1, &t0, f);
                            Tree::union(&t0, &t1, f)
                        }
                        (l0, None, r0) => Tree::join(
                            &Tree::union(&l0, &n1.left, f),
                            n1.elts(),
                            &Tree::union(&r0, &n1.right, f),
                        ),
                    }
                }
            }
        }
    }

    fn intersect_int<F>(
        t0: &Tree<K, V, SIZE>,
        t1: &Tree<K, V, SIZE>,
        r: &mut Vec<(K, V)>,
        f: &mut F,
    ) where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        match (t0, t1) {
            (Tree::Empty, _) => (),
            (_, Tree::Empty) => (),
            (Tree::Node(ref n0), t1) => match t1.split(n0.min_key(), n0.max_key()) {
                (l1, None, r1) => {
                    Tree::intersect_int(&n0.left, &l1, r, f);
                    Tree::intersect_int(&n0.right, &r1, r, f);
                }
                (l1, Some(elts), r1) if elts.len() == 0 => {
                    Tree::intersect_int(&n0.left, &l1, r, f);
                    Tree::intersect_int(&n0.right, &r1, r, f);
                }
                (l1, Some(elts), r1) => {
                    let (min_k, max_k) = elts.min_max_key().unwrap();
                    Chunk::intersect(n0.elts(), &elts, r, f);
                    if n0.min_key() < &min_k && n0.max_key() > &max_k {
                        Tree::intersect_int(t0, &Tree::concat(&l1, &r1), r, f)
                    } else if n0.min_key() >= &min_k && n0.max_key() <= &max_k {
                        let t0 = Tree::concat(&n0.left, &n0.right);
                        let t1 = Tree::join(&l1, &elts, &r1);
                        Tree::intersect_int(&t0, &t1, r, f);
                    } else if n0.min_key() < &min_k {
                        let tl = Tree::join(&n0.left, n0.elts(), &Tree::Empty);
                        Tree::intersect_int(&tl, &l1, r, f);
                        let tr = Tree::join(&Tree::Empty, &elts, &r1);
                        Tree::intersect_int(&n0.right, &tr, r, f);
                    } else {
                        let tl = Tree::join(&l1, &elts, &Tree::Empty);
                        Tree::intersect_int(&tl, &n0.left, r, f);
                        let tr = Tree::join(&Tree::Empty, n0.elts(), &n0.right);
                        Tree::intersect_int(&r1, &tr, r, f);
                    }
                }
            },
        }
    }

    pub(crate) fn intersect<F>(
        t0: &Tree<K, V, SIZE>,
        t1: &Tree<K, V, SIZE>,
        f: &mut F,
    ) -> Self
    where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        let mut r = Vec::new();
        Tree::intersect_int(t0, t1, &mut r, f);
        Tree::Empty.insert_many(r.into_iter())
    }

    pub(crate) fn diff<F>(t0: &Tree<K, V, SIZE>, t1: &Tree<K, V, SIZE>, f: &mut F) -> Self
    where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        let mut actions = Vec::new();
        Tree::intersect_int(t0, t1, &mut Vec::new(), &mut |k, v0, v1| {
            actions.push((k.clone(), f(k, v0, v1)));
            None
        });
        t0.update_many(actions, &mut |k, v, _| v.map(|v| (k, v)))
    }

    fn is_empty(&self) -> bool {
        match self {
            Tree::Empty => true,
            Tree::Node(..) => false,
        }
    }

    pub(crate) fn len(&self) -> usize {
        match self {
            Tree::Empty => 0,
            Tree::Node(n) => {
                // on a 64 bit platform usize == u64, and on a 32 bit
                // platform there can't be enough elements to overflow
                // a u32
                let size_of_children = (n.height_and_size & 0x00ffffff_ffffffff) as usize;
                n.elts().len() + size_of_children
            }
        }
    }

    fn height(&self) -> u8 {
        match self {
            Tree::Empty => 0,
            Tree::Node(ref n) => n.height(),
        }
    }

    #[cfg(feature = "pool")]
    fn create(
        l: &Tree<K, V, SIZE>,
        elts: Chunk<K, V, SIZE>,
        r: &Tree<K, V, SIZE>,
    ) -> Self {
        let (min_key, max_key) = elts.min_max_key().unwrap();
        let height_and_size =
            pack_height_and_size(1 + max(l.height(), r.height()), l.len() + r.len());
        let mut t = take::<Node<K, V, SIZE>>();
        let inner = Arc::get_mut(&mut t.0).unwrap();
        inner.elts = Some(elts);
        inner.min_key = Some(min_key);
        inner.max_key = Some(max_key);
        inner.left = l.clone();
        inner.right = r.clone();
        inner.height_and_size = height_and_size;
        Tree::Node(t)
    }

    #[cfg(not(feature = "pool"))]
    fn create(
        l: &Tree<K, V, SIZE>,
        elts: Chunk<K, V, SIZE>,
        r: &Tree<K, V, SIZE>,
    ) -> Self {
        let (min_key, max_key) = elts.min_max_key().unwrap();
        let height_and_size =
            pack_height_and_size(1 + max(l.height(), r.height()), l.len() + r.len());
        let n = NodeInner {
            elts,
            min_key,
            max_key,
            left: l.clone(),
            right: r.clone(),
            height_and_size,
        };
        Tree::Node(Node(Arc::new(n)))
    }

    fn in_bal(l: &Tree<K, V, SIZE>, r: &Tree<K, V, SIZE>) -> bool {
        let (hl, hr) = (l.height(), r.height());
        (hl <= hr.saturating_add(2)) && (hr <= hl.saturating_add(2))
    }

    fn compact(self) -> Self {
        match self {
            Tree::Empty => self,
            Tree::Node(ref tn) => {
                let len = tn.elts().len();
                if len > SIZE >> 1 {
                    self
                } else {
                    match tn.right.min_elts() {
                        None => self,
                        Some(chunk) => {
                            let n = SIZE - len;
                            let to_add =
                                chunk.into_iter().map(|(k, v)| (k.clone(), v.clone()));
                            let overflow = chunk
                                .into_iter()
                                .skip(n)
                                .map(|(k, v)| (k.clone(), v.clone()));
                            let elts = tn.elts().append(to_add);
                            let t =
                                Tree::bal(&tn.left, elts, &tn.right.remove_min_elts());
                            if n >= chunk.len() {
                                t
                            } else {
                                t.insert_many(overflow)
                            }
                        }
                    }
                }
            }
        }
    }

    fn bal(l: &Tree<K, V, SIZE>, elts: Chunk<K, V, SIZE>, r: &Tree<K, V, SIZE>) -> Self {
        let (hl, hr) = (l.height(), r.height());
        if hl > hr.saturating_add(2) {
            match *l {
                Tree::Empty => panic!("tree heights wrong"),
                Tree::Node(ref ln) => {
                    if ln.left.height() >= ln.right.height() {
                        Tree::create(
                            &ln.left,
                            ln.elts().clone(),
                            &Tree::create(&ln.right, elts, r),
                        )
                        .compact()
                    } else {
                        match ln.right {
                            Tree::Empty => panic!("tree heights wrong"),
                            Tree::Node(ref lrn) => Tree::create(
                                &Tree::create(&ln.left, ln.elts().clone(), &lrn.left),
                                lrn.elts().clone(),
                                &Tree::create(&lrn.right, elts, r),
                            )
                            .compact(),
                        }
                    }
                }
            }
        } else if hr > hl.saturating_add(2) {
            match *r {
                Tree::Empty => panic!("tree heights are wrong"),
                Tree::Node(ref rn) => {
                    if rn.right.height() >= rn.left.height() {
                        Tree::create(
                            &Tree::create(l, elts, &rn.left),
                            rn.elts().clone(),
                            &rn.right,
                        )
                        .compact()
                    } else {
                        match rn.left {
                            Tree::Empty => panic!("tree heights are wrong"),
                            Tree::Node(ref rln) => Tree::create(
                                &Tree::create(l, elts, &rln.left),
                                rln.elts().clone(),
                                &Tree::create(&rln.right, rn.elts().clone(), &rn.right),
                            )
                            .compact(),
                        }
                    }
                }
            }
        } else {
            Tree::create(l, elts, r).compact()
        }
    }

    fn update_chunk<Q, D, F>(&self, chunk: Vec<(Q, D)>, f: &mut F) -> Self
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        if chunk.len() == 0 {
            return self.clone();
        }
        match self {
            &Tree::Empty => {
                let chunk = Chunk::create_with(chunk, f);
                if chunk.len() == 0 {
                    Tree::Empty
                } else {
                    Tree::create(&Tree::Empty, chunk, &Tree::Empty)
                }
            }
            &Tree::Node(ref tn) => {
                let leaf = match (&tn.left, &tn.right) {
                    (&Tree::Empty, &Tree::Empty) => true,
                    (_, _) => false,
                };
                match tn.elts().update_chunk(chunk, leaf, f) {
                    UpdateChunk::Updated {
                        elts,
                        update_left,
                        update_right,
                        overflow_right,
                    } => {
                        let l = tn.left.update_chunk(update_left, f);
                        let r = tn.right.insert_chunk(overflow_right);
                        let r = r.update_chunk(update_right, f);
                        Tree::bal(&l, elts, &r)
                    }
                    UpdateChunk::Removed {
                        not_done,
                        update_left,
                        update_right,
                    } => {
                        let l = tn.left.update_chunk(update_left, f);
                        let r = tn.right.update_chunk(update_right, f);
                        let t = Tree::concat(&l, &r);
                        t.update_chunk(not_done, f)
                    }
                    UpdateChunk::UpdateLeft(chunk) => {
                        let l = tn.left.update_chunk(chunk, f);
                        Tree::bal(&l, tn.elts().clone(), &tn.right)
                    }
                    UpdateChunk::UpdateRight(chunk) => {
                        let r = tn.right.update_chunk(chunk, f);
                        Tree::bal(&tn.left, tn.elts().clone(), &r)
                    }
                }
            }
        }
    }

    fn insert_chunk(&self, chunk: Vec<(K, V)>) -> Self {
        self.update_chunk(chunk, &mut |k, v, _| Some((k, v)))
    }

    pub(crate) fn update_many<Q, D, E, F>(&self, elts: E, f: &mut F) -> Self
    where
        E: IntoIterator<Item = (Q, D)>,
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        let mut elts = {
            let mut v = elts.into_iter().collect::<Vec<(Q, D)>>();
            v.sort_by(|(ref k0, _), (ref k1, _)| k0.cmp(k1));
            v.dedup_by(|t0, t1| t0.0 == t1.0);
            v
        };
        let mut t = self.clone();
        while elts.len() > 0 {
            let chunk = elts.drain(0..min(SIZE, elts.len())).collect::<Vec<_>>();
            t = t.update_chunk(chunk, f)
        }
        t
    }

    pub(crate) fn insert_many<E: IntoIterator<Item = (K, V)>>(&self, elts: E) -> Self {
        self.update_many(elts, &mut |k, v, _| Some((k, v)))
    }

    pub(crate) fn update_cow<Q, D, F>(&mut self, q: Q, d: D, f: &mut F) -> Option<V>
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        match self {
            Tree::Empty => match f(q, d, None) {
                None => None,
                Some((k, v)) => {
                    *self =
                        Tree::create(&Tree::Empty, Chunk::singleton(k, v), &Tree::Empty);
                    None
                }
            },
            Tree::Node(ref mut tn) => {
                // CR estokes: problem? doesn't use the pool. check chunk as well.
                let tn = Arc::make_mut(&mut tn.0);
                let leaf = match (&tn.left, &tn.right) {
                    (&Tree::Empty, &Tree::Empty) => true,
                    (_, _) => false,
                };
                match tn.elts_mut().update_mut(q, d, leaf, f) {
                    MutUpdate::UpdateLeft(k, d) => {
                        let prev = tn.left.update_cow(k, d, f);
                        if !Tree::in_bal(&tn.left, &tn.right) {
                            *self = Tree::bal(&tn.left, tn.elts().clone(), &tn.right)
                        } else {
                            tn.mutated();
                        }
                        prev
                    }
                    MutUpdate::UpdateRight(k, d) => {
                        let prev = tn.right.update_cow(k, d, f);
                        if !Tree::in_bal(&tn.left, &tn.right) {
                            *self = Tree::bal(&tn.left, tn.elts().clone(), &tn.right)
                        } else {
                            tn.mutated();
                        }
                        prev
                    }
                    MutUpdate::Updated { overflow, previous } => match overflow {
                        None => {
                            if tn.elts().len() > 0 {
                                tn.mutated();
                                previous
                            } else {
                                *self = Tree::concat(&tn.left, &tn.right);
                                previous
                            }
                        }
                        Some((ovk, ovv)) => {
                            let _ = tn.right.insert_cow(ovk, ovv);
                            if tn.elts().len() > 0 {
                                if !Tree::in_bal(&tn.left, &tn.right) {
                                    *self =
                                        Tree::bal(&tn.left, tn.elts().clone(), &tn.right);
                                    previous
                                } else {
                                    tn.mutated();
                                    previous
                                }
                            } else {
                                // this should be impossible
                                *self = Tree::concat(&tn.left, &tn.right);
                                previous
                            }
                        }
                    },
                }
            }
        }
    }

    pub(crate) fn update<Q, D, F>(&self, q: Q, d: D, f: &mut F) -> (Self, Option<V>)
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        match self {
            Tree::Empty => match f(q, d, None) {
                None => (self.clone(), None),
                Some((k, v)) => (
                    Tree::create(&Tree::Empty, Chunk::singleton(k, v), &Tree::Empty),
                    None,
                ),
            },
            Tree::Node(ref tn) => {
                let leaf = match (&tn.left, &tn.right) {
                    (&Tree::Empty, &Tree::Empty) => true,
                    (_, _) => false,
                };
                match tn.elts().update(q, d, leaf, f) {
                    Update::UpdateLeft(k, d) => {
                        let (l, prev) = tn.left.update(k, d, f);
                        (Tree::bal(&l, tn.elts().clone(), &tn.right), prev)
                    }
                    Update::UpdateRight(k, d) => {
                        let (r, prev) = tn.right.update(k, d, f);
                        (Tree::bal(&tn.left, tn.elts().clone(), &r), prev)
                    }
                    Update::Updated {
                        elts,
                        overflow,
                        previous,
                    } => match overflow {
                        None => {
                            if elts.len() == 0 {
                                (Tree::concat(&tn.left, &tn.right), previous)
                            } else {
                                (Tree::create(&tn.left, elts, &tn.right), previous)
                            }
                        }
                        Some((ovk, ovv)) => {
                            let (r, _) = tn.right.insert(ovk, ovv);
                            if elts.len() == 0 {
                                (Tree::concat(&tn.left, &r), previous)
                            } else {
                                (Tree::bal(&tn.left, elts, &r), previous)
                            }
                        }
                    },
                }
            }
        }
    }

    pub(crate) fn insert(&self, k: K, v: V) -> (Self, Option<V>) {
        self.update(k, v, &mut |k, v, _| Some((k, v)))
    }

    pub(crate) fn insert_cow(&mut self, k: K, v: V) -> Option<V> {
        self.update_cow(k, v, &mut |k, v, _| Some((k, v)))
    }

    fn min_elts<'a>(&'a self) -> Option<&'a Chunk<K, V, SIZE>> {
        match self {
            Tree::Empty => None,
            Tree::Node(ref tn) => match tn.left {
                Tree::Empty => Some(tn.elts()),
                Tree::Node(_) => tn.left.min_elts(),
            },
        }
    }

    fn remove_min_elts(&self) -> Self {
        match self {
            Tree::Empty => panic!("remove min elt"),
            Tree::Node(ref tn) => match tn.left {
                Tree::Empty => tn.right.clone(),
                Tree::Node(_) => {
                    Tree::bal(&tn.left.remove_min_elts(), tn.elts().clone(), &tn.right)
                }
            },
        }
    }

    fn concat(l: &Tree<K, V, SIZE>, r: &Tree<K, V, SIZE>) -> Tree<K, V, SIZE> {
        match (l, r) {
            (Tree::Empty, _) => r.clone(),
            (_, Tree::Empty) => l.clone(),
            (_, _) => {
                let elts = match r.min_elts() {
                    Some(e) => e,
                    None => &Chunk::empty(), // this shouldn't happen
                };
                Tree::bal(l, elts.clone(), &r.remove_min_elts())
            }
        }
    }

    pub(crate) fn remove<Q: ?Sized + Ord>(&self, k: &Q) -> (Self, Option<V>)
    where
        K: Borrow<Q>,
    {
        match self {
            &Tree::Empty => (Tree::Empty, None),
            &Tree::Node(ref tn) => match tn.elts().get(k) {
                Loc::NotPresent(_) => (self.clone(), None),
                Loc::Here(i) => {
                    let p = tn.elts().val(i).clone();
                    let elts = tn.elts().remove_elt_at(i);
                    if elts.len() == 0 {
                        (Tree::concat(&tn.left, &tn.right), Some(p))
                    } else {
                        (Tree::create(&tn.left, elts, &tn.right), Some(p))
                    }
                }
                Loc::InLeft => {
                    let (l, p) = tn.left.remove(k);
                    (Tree::bal(&l, tn.elts().clone(), &tn.right), p)
                }
                Loc::InRight => {
                    let (r, p) = tn.right.remove(k);
                    (Tree::bal(&tn.left, tn.elts().clone(), &r), p)
                }
            },
        }
    }

    pub(crate) fn remove_cow<Q: ?Sized + Ord>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
    {
        match self {
            Tree::Empty => None,
            Tree::Node(ref mut tn) => {
                // CR estokes: validate this
                let tn = Arc::make_mut(&mut tn.0);
                match tn.elts().get(k) {
                    Loc::NotPresent(_) => None,
                    Loc::Here(i) => {
                        let (_, p) = tn.elts_mut().remove_elt_at_mut(i);
                        if tn.elts().len() == 0 {
                            *self = Tree::concat(&tn.left, &tn.right);
                            Some(p)
                        } else {
                            tn.mutated();
                            Some(p)
                        }
                    }
                    Loc::InLeft => {
                        let p = tn.left.remove_cow(k);
                        if !Tree::in_bal(&tn.left, &tn.right) {
                            *self = Tree::bal(&tn.left, tn.elts().clone(), &tn.right);
                        } else {
                            tn.mutated()
                        }
                        p
                    }
                    Loc::InRight => {
                        let p = tn.right.remove_cow(k);
                        if !Tree::in_bal(&tn.left, &tn.right) {
                            *self = Tree::bal(&tn.left, tn.elts().clone(), &tn.right);
                        } else {
                            tn.mutated()
                        }
                        p
                    }
                }
            }
        }
    }

    // this is structured as a loop so that the optimizer can inline
    // the closure argument. Sadly it doesn't do that if get_gen is a
    // recursive function, and the difference is >10%. True as of
    // 2018-07-19
    fn get_gen<'a, Q, F, R>(&'a self, k: &Q, f: F) -> Option<R>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
        F: FnOnce(&'a Chunk<K, V, SIZE>, usize) -> R,
        R: 'a,
    {
        match self {
            Tree::Empty => None,
            Tree::Node(n) => {
                let mut tn = n;
                loop {
                    match (k.cmp(tn.min_key().borrow()), k.cmp(tn.max_key().borrow())) {
                        (Ordering::Less, _) => match tn.left {
                            Tree::Empty => break None,
                            Tree::Node(ref n) => tn = n,
                        },
                        (_, Ordering::Greater) => match tn.right {
                            Tree::Empty => break None,
                            Tree::Node(ref n) => tn = n,
                        },
                        (_, _) => {
                            let e = tn.elts();
                            break e.get_local(k).map(|i| f(e, i));
                        }
                    }
                }
            }
        }
    }

    pub(crate) fn get<'a, Q>(&'a self, k: &Q) -> Option<&'a V>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        self.get_gen(k, |e, i| e.val(i))
    }

    pub(crate) fn get_key<'a, Q>(&'a self, k: &Q) -> Option<&'a K>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        self.get_gen(k, |e, i| e.key(i))
    }

    pub(crate) fn get_full<'a, Q>(&'a self, k: &Q) -> Option<(&'a K, &'a V)>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        self.get_gen(k, |e, i| e.kv(i))
    }

    pub(crate) fn get_mut_cow<'a, Q>(&'a mut self, k: &Q) -> Option<&'a mut V>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        match self {
            Tree::Empty => None,
            Tree::Node(tn) => {
                let tn = Arc::make_mut(&mut tn.0);
                match (k.cmp(tn.min_key().borrow()), k.cmp(tn.max_key().borrow())) {
                    (Ordering::Less, _) => tn.left.get_mut_cow(k),
                    (_, Ordering::Greater) => tn.right.get_mut_cow(k),
                    (_, _) => match tn.elts().get_local(k) {
                        Some(i) => Some(tn.elts_mut().val_mut(i)),
                        None => None,
                    },
                }
            }
        }
    }

    pub(crate) fn get_or_insert_cow<'a, F>(&'a mut self, k: K, f: F) -> &'a mut V
    where
        F: FnOnce() -> V,
    {
        match self.get_mut_cow(&k).map(|v| v as *mut V) {
            Some(v) => unsafe { &mut *v },
            None => {
                self.insert_cow(k.clone(), f());
                self.get_mut_cow(&k).unwrap()
            }
        }
    }
}

impl<K, V, const SIZE: usize> Tree<K, V, SIZE>
where
    K: Ord + Clone + Debug,
    V: Clone + Debug,
{
    #[allow(dead_code)]
    pub(crate) fn invariant(&self) -> () {
        fn in_range<K, V, const SIZE: usize>(
            lower: Option<&K>,
            upper: Option<&K>,
            elts: &Chunk<K, V, SIZE>,
        ) -> bool
        where
            K: Ord + Clone + Debug,
            V: Clone + Debug,
        {
            (match lower {
                None => true,
                Some(lower) => elts
                    .into_iter()
                    .all(|(k, _)| lower.cmp(k) == Ordering::Less),
            }) && (match upper {
                None => true,
                Some(upper) => elts
                    .into_iter()
                    .all(|(k, _)| upper.cmp(k) == Ordering::Greater),
            })
        }

        fn sorted<K, V, const SIZE: usize>(elts: &Chunk<K, V, SIZE>) -> bool
        where
            K: Ord + Clone + Debug,
            V: Clone + Debug,
        {
            if elts.len() == 1 {
                true
            } else {
                for i in 0..(elts.len() - 1) {
                    match elts.key(i).cmp(&elts.key(i + 1)) {
                        Ordering::Greater => return false,
                        Ordering::Less => (),
                        Ordering::Equal => panic!("duplicates found: {:#?}", elts),
                    }
                }
                true
            }
        }

        fn check<K, V, const SIZE: usize>(
            t: &Tree<K, V, SIZE>,
            lower: Option<&K>,
            upper: Option<&K>,
            len: usize,
        ) -> (u8, usize)
        where
            K: Ord + Clone + Debug,
            V: Clone + Debug,
        {
            match *t {
                Tree::Empty => (0, len),
                Tree::Node(ref tn) => {
                    if !in_range(lower, upper, tn.elts()) {
                        panic!("tree invariant violated lower\n{:#?}\n\nupper\n{:#?}\n\nelts\n{:#?}\n\ntree\n{:#?}",
                               lower, upper, &tn.elts, t)
                    };
                    if !sorted(tn.elts()) {
                        panic!("elements isn't sorted")
                    };
                    let (thl, len) =
                        check(&tn.left, lower, tn.elts().min_elt().map(|(k, _)| k), len);
                    let (thr, len) =
                        check(&tn.right, tn.elts().max_elt().map(|(k, _)| k), upper, len);
                    let th = max(thl, thr).saturating_add(1);
                    let (hl, hr) = (tn.left.height(), tn.right.height());
                    let ub = max(hl, hr) - min(hl, hr);
                    if thl != hl {
                        panic!("left node height is wrong")
                    };
                    if thr != hr {
                        panic!("right node height is wrong")
                    };
                    let h = t.height();
                    if th != h {
                        panic!("node height is wrong {} vs {}", th, h)
                    };
                    if ub > 2 {
                        panic!("tree is unbalanced {:#?} tree: {:#?}", ub, t)
                    };
                    (th, len + tn.elts().len())
                }
            }
        }

        //println!("{:#?}", self);
        let (_height, tlen) = check(self, None, None, 0);
        let len = self.len();
        if len != tlen {
            panic!("len is wrong {} vs {}", len, tlen)
        }
    }
}
