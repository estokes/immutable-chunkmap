use arrayvec::ArrayVec;
use crate::chunk::{Chunk, Loc, Update, UpdateChunk, SIZE};
use std::{
    borrow::Borrow,
    cmp::{max, min, Eq, Ord, Ordering, PartialEq, PartialOrd},
    default::Default,
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
    iter,
    mem::swap,
    ops::{Bound, Index},
    slice,
    sync::Arc,
};

// until we get 128 bit machines with exabytes of memory
const MAX_DEPTH: usize = 64;

#[derive(Clone, Debug)]
pub(crate) struct Node<K: Ord + Clone, V: Clone> {
    elts: Arc<Chunk<K, V>>,
    min_key: K,
    max_key: K,
    left: Tree<K, V>,
    right: Tree<K, V>,
    size_of_children: usize,
    height: u16,
}

#[derive(Clone)]
pub(crate) enum Tree<K: Ord + Clone, V: Clone> {
    Empty,
    Node(Arc<Node<K, V>>),
}

impl<K, V> Hash for Tree<K, V>
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

impl<K, V> Default for Tree<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    fn default() -> Tree<K, V> {
        Tree::Empty
    }
}

impl<K, V> PartialEq for Tree<K, V>
where
    K: PartialEq + Ord + Clone,
    V: PartialEq + Clone,
{
    fn eq(&self, other: &Tree<K, V>) -> bool {
        self.len() == other.len() && self.into_iter().zip(other).all(|(e0, e1)| e0 == e1)
    }
}

impl<K, V> Eq for Tree<K, V>
where
    K: Eq + Ord + Clone,
    V: Eq + Clone,
{
}

impl<K, V> PartialOrd for Tree<K, V>
where
    K: Ord + Clone,
    V: PartialOrd + Clone,
{
    fn partial_cmp(&self, other: &Tree<K, V>) -> Option<Ordering> {
        self.into_iter().partial_cmp(other.into_iter())
    }
}

impl<K, V> Ord for Tree<K, V>
where
    K: Ord + Clone,
    V: Ord + Clone,
{
    fn cmp(&self, other: &Tree<K, V>) -> Ordering {
        self.into_iter().cmp(other.into_iter())
    }
}

impl<K, V> Debug for Tree<K, V>
where
    K: Debug + Ord + Clone,
    V: Debug + Clone,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_map().entries(self.into_iter()).finish()
    }
}

impl<'a, Q, K, V> Index<&'a Q> for Tree<K, V>
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

pub struct Iter<'a, Q, K, V>
where
    Q: Ord,
    K: 'a + Borrow<Q> + Ord + Clone,
    V: 'a + Clone,
{
    ubound: Bound<Q>,
    lbound: Bound<Q>,
    stack: ArrayVec<[(bool, &'a Node<K, V>); MAX_DEPTH]>,
    elts: Option<iter::Zip<slice::Iter<'a, K>, slice::Iter<'a, V>>>,
    current: Option<&'a K>,
    stack_rev: ArrayVec<[(bool, &'a Node<K, V>); MAX_DEPTH]>,
    elts_rev: Option<iter::Zip<slice::Iter<'a, K>, slice::Iter<'a, V>>>,
    current_rev: Option<&'a K>,
}

impl<'a, Q, K, V> Iter<'a, Q, K, V>
where
    Q: Ord,
    K: 'a + Borrow<Q> + Ord + Clone,
    V: 'a + Clone,
{
    // is at least one element of the chunk in bounds
    fn any_elts_above_lbound(&self, n: &'a Node<K, V>) -> bool {
        let l = n.elts.len();
        match self.lbound {
            Bound::Unbounded => true,
            Bound::Included(ref bound) => l == 0 || n.elts.key(l - 1).borrow() >= bound,
            Bound::Excluded(ref bound) => l == 0 || n.elts.key(l - 1).borrow() > bound,
        }
    }

    fn any_elts_below_ubound(&self, n: &'a Node<K, V>) -> bool {
        let l = n.elts.len();
        match self.ubound {
            Bound::Unbounded => true,
            Bound::Included(ref bound) => l == 0 || n.elts.key(0).borrow() <= bound,
            Bound::Excluded(ref bound) => l == 0 || n.elts.key(0).borrow() < bound,
        }
    }

    fn any_elts_in_bounds(&self, n: &'a Node<K, V>) -> bool {
        self.any_elts_above_lbound(n) && self.any_elts_below_ubound(n)
    }

    fn above_lbound(&self, k: &'a K) -> bool {
        match self.lbound {
            Bound::Unbounded => true,
            Bound::Included(ref bound) => k.borrow() >= bound,
            Bound::Excluded(ref bound) => k.borrow() > bound,
        }
    }

    fn below_ubound(&self, k: &'a K) -> bool {
        match self.ubound {
            Bound::Unbounded => true,
            Bound::Included(ref bound) => k.borrow() <= bound,
            Bound::Excluded(ref bound) => k.borrow() < bound,
        }
    }
}

impl<'a, Q, K, V> Iterator for Iter<'a, Q, K, V>
where
    Q: Ord,
    K: 'a + Borrow<Q> + Ord + Clone,
    V: 'a + Clone,
{
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            loop {
                let (k, v) = match &mut self.elts {
                    &mut None => break,
                    &mut Some(ref mut s) => match s.next() {
                        None => break,
                        Some((k, v)) => (k, v),
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
                    self.elts = Some((&(*current.elts)).into_iter());
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

impl<'a, Q, K, V> DoubleEndedIterator for Iter<'a, Q, K, V>
where
    Q: Ord,
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
                    self.elts_rev = Some((&(*current.elts)).into_iter());
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

impl<'a, K, V> IntoIterator for &'a Tree<K, V>
where
    K: 'a + Borrow<K> + Ord + Clone,
    V: 'a + Clone,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.range(Bound::Unbounded, Bound::Unbounded)
    }
}

impl<K, V> Tree<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    pub(crate) fn new() -> Self {
        Tree::Empty
    }

    pub(crate) fn range<'a, Q>(
        &'a self,
        lbound: Bound<Q>,
        ubound: Bound<Q>,
    ) -> Iter<'a, Q, K, V>
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        match self {
            &Tree::Empty => Iter {
                lbound,
                ubound,
                stack: ArrayVec::<[_; MAX_DEPTH]>::new(),
                elts: None,
                current: None,
                stack_rev: ArrayVec::<[_; MAX_DEPTH]>::new(),
                elts_rev: None,
                current_rev: None,
            },
            &Tree::Node(ref n) => {
                let mut stack = ArrayVec::<[(bool, &'a Node<K, V>); MAX_DEPTH]>::new();
                let mut stack_rev =
                    ArrayVec::<[(bool, &'a Node<K, V>); MAX_DEPTH]>::new();
                stack.push((false, n));
                stack_rev.push((false, n));
                Iter {
                    lbound,
                    ubound,
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

    fn add_min_elts(&self, elts: &Arc<Chunk<K, V>>) -> Self {
        match self {
            Tree::Empty => Tree::create(&Tree::Empty, elts.clone(), &Tree::Empty),
            Tree::Node(ref n) => Tree::bal(&n.left.add_min_elts(elts), &n.elts, &n.right),
        }
    }

    fn add_max_elts(&self, elts: &Arc<Chunk<K, V>>) -> Self {
        match self {
            Tree::Empty => Tree::create(&Tree::Empty, elts.clone(), &Tree::Empty),
            Tree::Node(ref n) => Tree::bal(&n.left, &n.elts, &n.right.add_max_elts(elts)),
        }
    }

    // This is the same as create except it makes no assumption about the tree
    // heights or tree balance, so you can pass it anything, and it will return
    // a balanced tree.
    fn join(l: &Tree<K, V>, elts: &Arc<Chunk<K, V>>, r: &Tree<K, V>) -> Self {
        match (l, r) {
            (Tree::Empty, _) => r.add_min_elts(elts),
            (_, Tree::Empty) => l.add_max_elts(elts),
            (Tree::Node(ref ln), Tree::Node(ref rn)) => {
                if ln.height > rn.height + 2 {
                    Tree::bal(&ln.left, &ln.elts, &Tree::join(&ln.right, elts, r))
                } else if rn.height > ln.height + 2 {
                    Tree::bal(&Tree::join(l, elts, &rn.left), &rn.elts, &rn.right)
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
    fn split(&self, vmin: &K, vmax: &K) -> (Self, Option<Arc<Chunk<K, V>>>, Self) {
        match self {
            Tree::Empty => (Tree::Empty, None, Tree::Empty),
            Tree::Node(ref n) => {
                if *vmax < n.min_key {
                    let (ll, inter, rl) = n.left.split(vmin, vmax);
                    (ll, inter, Tree::join(&rl, &n.elts, &n.right))
                } else if *vmin > n.max_key {
                    let (lr, inter, rr) = n.right.split(vmin, vmax);
                    (Tree::join(&n.left, &n.elts, &lr), inter, rr)
                } else {
                    (n.left.clone(), Some(n.elts.clone()), n.right.clone())
                }
            }
        }
    }

    /// merge all the values in the root node of from into to, and
    /// return from with it's current root remove, and to with the
    /// elements merged.
    fn merge_root_to<F>(from: &Tree<K, V>, to: &Tree<K, V>, f: &mut F) -> (Self, Self)
    where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        match (from, to) {
            (Tree::Empty, to) => (Tree::Empty, to.clone()),
            (Tree::Node(ref n), to) => {
                let to = to.update_chunk(n.elts.to_vec(), &mut |k0, v0, cur| match cur {
                    None => Some((k0, v0)),
                    Some((_, v1)) => f(&k0, &v0, v1).map(|v| (k0, v)),
                });
                if n.height == 1 {
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
    pub(crate) fn union<F>(t0: &Tree<K, V>, t1: &Tree<K, V>, f: &mut F) -> Self
    where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        match (t0, t1) {
            (Tree::Empty, Tree::Empty) => Tree::Empty,
            (Tree::Empty, t1) => t1.clone(),
            (t0, Tree::Empty) => t0.clone(),
            (Tree::Node(ref n0), Tree::Node(ref n1)) => {
                if n0.height > n1.height {
                    match t1.split(&n0.min_key, &n0.max_key) {
                        (_, Some(_), _) => {
                            let (t0, t1) = Tree::merge_root_to(&t0, &t1, f);
                            Tree::union(&t0, &t1, f)
                        }
                        (l1, None, r1) => Tree::join(
                            &Tree::union(&n0.left, &l1, f),
                            &n0.elts,
                            &Tree::union(&n0.right, &r1, f),
                        ),
                    }
                } else {
                    match t0.split(&n1.min_key, &n1.max_key) {
                        (_, Some(_), _) => {
                            let (t1, t0) = Tree::merge_root_to(&t1, &t0, f);
                            Tree::union(&t0, &t1, f)
                        }
                        (l0, None, r0) => Tree::join(
                            &Tree::union(&l0, &n1.left, f),
                            &n1.elts,
                            &Tree::union(&r0, &n1.right, f),
                        ),
                    }
                }
            }
        }
    }

    fn intersect_int<F>(t0: &Tree<K, V>, t1: &Tree<K, V>, r: &mut Vec<(K, V)>, f: &mut F)
    where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        match (t0, t1) {
            (Tree::Empty, _) => (),
            (_, Tree::Empty) => (),
            (Tree::Node(ref n0), t1) => match t1.split(&n0.min_key, &n0.max_key) {
                (l1, None, r1) => {
                    Tree::intersect_int(&n0.left, &l1, r, f);
                    Tree::intersect_int(&n0.right, &r1, r, f);
                }
                (l1, Some(elts), r1) => {
                    let (min_k, max_k) = elts.min_max_key().unwrap();
                    Chunk::intersect(&n0.elts, &elts, r, f);
                    if n0.min_key < min_k && n0.max_key > max_k {
                        Tree::intersect_int(t0, &Tree::concat(&l1, &r1), r, f)
                    } else if n0.min_key >= min_k && n0.max_key <= max_k {
                        let t0 = Tree::concat(&n0.left, &n0.right);
                        let t1 = Tree::join(&l1, &elts, &r1);
                        Tree::intersect_int(&t0, &t1, r, f);
                    } else if n0.min_key < min_k {
                        let tl = Tree::join(&n0.left, &n0.elts, &Tree::Empty);
                        Tree::intersect_int(&tl, &l1, r, f);
                        let tr = Tree::join(&Tree::Empty, &elts, &r1);
                        Tree::intersect_int(&n0.right, &tr, r, f);
                    } else {
                        let tl = Tree::join(&l1, &elts, &Tree::Empty);
                        Tree::intersect_int(&tl, &n0.left, r, f);
                        let tr = Tree::join(&Tree::Empty, &n0.elts, &n0.right);
                        Tree::intersect_int(&r1, &tr, r, f);
                    }
                }
            },
        }
    }

    pub(crate) fn intersect<F>(t0: &Tree<K, V>, t1: &Tree<K, V>, f: &mut F) -> Self
    where
        F: FnMut(&K, &V, &V) -> Option<V>,
    {
        let mut r = Vec::new();
        Tree::intersect_int(t0, t1, &mut r, f);
        Tree::Empty.insert_many(r.into_iter())
    }

    pub(crate) fn diff<F>(t0: &Tree<K, V>, t1: &Tree<K, V>, f: &mut F) -> Self
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
            Tree::Node(n) => n.elts.len() + n.size_of_children,
        }
    }

    fn height(&self) -> u16 {
        match self {
            &Tree::Empty => 0,
            &Tree::Node(ref n) => n.height,
        }
    }

    fn create(l: &Tree<K, V>, elts: Arc<Chunk<K, V>>, r: &Tree<K, V>) -> Self {
        let (min_key, max_key) = elts.min_max_key().unwrap();
        let n = Node {
            elts: elts,
            min_key: min_key,
            max_key: max_key,
            left: l.clone(),
            right: r.clone(),
            size_of_children: l.len() + r.len(),
            height: 1 + max(l.height(), r.height()),
        };
        Tree::Node(Arc::new(n))
    }

    fn bal(l: &Tree<K, V>, elts: &Arc<Chunk<K, V>>, r: &Tree<K, V>) -> Self {
        let (hl, hr) = (l.height(), r.height());
        if hl > hr + 1 {
            match *l {
                Tree::Empty => panic!("tree heights wrong"),
                Tree::Node(ref ln) => if ln.left.height() >= ln.right.height() {
                    Tree::create(
                        &ln.left,
                        ln.elts.clone(),
                        &Tree::create(&ln.right, elts.clone(), r)
                    )
                } else {
                    match ln.right {
                        Tree::Empty => panic!("tree heights wrong"),
                        Tree::Node(ref lrn) => Tree::create(
                            &Tree::create(&ln.left, ln.elts.clone(), &lrn.left),
                            lrn.elts.clone(),
                            &Tree::create(&lrn.right, elts.clone(), r),
                        ),
                    }
                }
            }
        } else if hr > hl + 1 {
            match *r {
                Tree::Empty => panic!("tree heights are wrong"),
                Tree::Node(ref rn) => if rn.right.height() >= rn.left.height() {
                    Tree::create(
                        &Tree::create(l, elts.clone(), &rn.left),
                        rn.elts.clone(),
                        &rn.right
                    )
                } else {
                    match rn.left {
                        Tree::Empty => panic!("tree heights are wrong"),
                        Tree::Node(ref rln) => Tree::create(
                            &Tree::create(l, elts.clone(), &rln.left),
                            rln.elts.clone(),
                            &Tree::create(&rln.right, rn.elts.clone(), &rn.right),
                        ),
                    }
                }
            }
        } else {
            Tree::create(l, elts.clone(), r)
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
                let elts = {
                    let t = Chunk::empty();
                    match t.update_chunk(chunk, true, f) {
                        UpdateChunk::Created(elts) => elts,
                        UpdateChunk::Removed { .. } => unreachable!(),
                        UpdateChunk::Updated { .. } => unreachable!(),
                        UpdateChunk::UpdateLeft(_) => unreachable!(),
                        UpdateChunk::UpdateRight(_) => unreachable!(),
                    }
                };
                Tree::create(&Tree::Empty, Arc::new(elts), &Tree::Empty)
            }
            &Tree::Node(ref tn) => {
                let leaf = match (&tn.left, &tn.right) {
                    (&Tree::Empty, &Tree::Empty) => true,
                    (_, _) => false,
                };
                match tn.elts.update_chunk(chunk, leaf, f) {
                    UpdateChunk::Created(elts) => {
                        Tree::create(&tn.left, Arc::new(elts), &tn.right)
                    }
                    UpdateChunk::Updated {
                        elts,
                        update_left,
                        update_right,
                        overflow_right,
                    } => {
                        let l = tn.left.update_chunk(update_left, f);
                        let r = tn.right.insert_chunk(overflow_right);
                        let r = r.update_chunk(update_right, f);
                        Tree::bal(&l, &Arc::new(elts), &r)
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
                        Tree::bal(&l, &tn.elts, &tn.right)
                    }
                    UpdateChunk::UpdateRight(chunk) => {
                        let r = tn.right.update_chunk(chunk, f);
                        Tree::bal(&tn.left, &tn.elts, &r)
                    }
                }
            }
        }
    }

    fn insert_chunk(&self, chunk: Vec<(K, V)>) -> Self {
        self.update_chunk(chunk, &mut |k, v, _| Some((k, v)))
    }

    fn do_chunk<Q, D, F>(&mut self, chunk: &mut Vec<(Q, D)>, f: &mut F)
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        if chunk.len() < 6 {
            for (q, d) in chunk.drain(0..) {
                *self = self.update(q, d, f).0;
            }
        } else {
            let mut new_chunk = Vec::new();
            swap(&mut new_chunk, chunk);
            *self = self.update_chunk(new_chunk, f);
        }
    }

    pub(crate) fn update_many<Q, D, E, F>(&self, elts: E, f: &mut F) -> Self
    where
        E: IntoIterator<Item = (Q, D)>,
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        let mut t = self.clone();
        let mut chunk: Vec<(Q, D)> = Vec::new();
        for (q, d) in elts {
            match chunk.last().map(|p| p.0.cmp(&q)) {
                None => chunk.push((q, d)),
                Some(Ordering::Equal) => {
                    let l = chunk.len();
                    chunk[l - 1] = (q, d)
                }
                Some(Ordering::Less) => {
                    chunk.push((q, d));
                    if chunk.len() >= SIZE {
                        t.do_chunk(&mut chunk, f);
                    }
                }
                Some(Ordering::Greater) => {
                    t.do_chunk(&mut chunk, f);
                    chunk.push((q, d))
                }
            }
        }
        t.do_chunk(&mut chunk, f);
        t
    }

    pub(crate) fn insert_many<E: IntoIterator<Item = (K, V)>>(&self, elts: E) -> Self {
        self.update_many(elts, &mut |k, v, _| Some((k, v)))
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
                    Tree::create(
                        &Tree::Empty,
                        Arc::new(Chunk::singleton(k, v)),
                        &Tree::Empty,
                    ),
                    None,
                ),
            },
            Tree::Node(ref tn) => {
                let leaf = match (&tn.left, &tn.right) {
                    (&Tree::Empty, &Tree::Empty) => true,
                    (_, _) => false,
                };
                match tn.elts.update(q, d, leaf, f) {
                    Update::UpdateLeft(k, d) => {
                        let (l, prev) = tn.left.update(k, d, f);
                        (Tree::bal(&l, &tn.elts, &tn.right), prev)
                    }
                    Update::UpdateRight(k, d) => {
                        let (r, prev) = tn.right.update(k, d, f);
                        (Tree::bal(&tn.left, &tn.elts, &r), prev)
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
                                (
                                    Tree::create(&tn.left, Arc::new(elts), &tn.right),
                                    previous,
                                )
                            }
                        }
                        Some((ovk, ovv)) => {
                            let (r, _) = tn.right.insert(ovk, ovv);
                            if elts.len() == 0 {
                                (Tree::concat(&tn.left, &r), previous)
                            } else {
                                (Tree::bal(&tn.left, &Arc::new(elts), &r), previous)
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

    fn min_elts<'a>(&'a self) -> Option<&'a Arc<Chunk<K, V>>> {
        match self {
            &Tree::Empty => None,
            &Tree::Node(ref tn) => match tn.left {
                Tree::Empty => Some(&tn.elts),
                Tree::Node(_) => tn.left.min_elts(),
            },
        }
    }

    fn remove_min_elts(&self) -> Self {
        match self {
            &Tree::Empty => panic!("remove min elt"),
            &Tree::Node(ref tn) => match tn.left {
                Tree::Empty => tn.right.clone(),
                Tree::Node(_) => {
                    Tree::bal(&tn.left.remove_min_elts(), &tn.elts, &tn.right)
                }
            },
        }
    }

    fn concat(l: &Tree<K, V>, r: &Tree<K, V>) -> Tree<K, V> {
        match (l, r) {
            (&Tree::Empty, _) => r.clone(),
            (_, &Tree::Empty) => l.clone(),
            (_, _) => {
                let elts = r.min_elts().unwrap();
                Tree::bal(l, elts, &r.remove_min_elts())
            }
        }
    }

    pub(crate) fn remove<Q: ?Sized + Ord>(&self, k: &Q) -> (Self, Option<V>)
    where
        K: Borrow<Q>,
    {
        match self {
            &Tree::Empty => (Tree::Empty, None),
            &Tree::Node(ref tn) => match tn.elts.get(k) {
                Loc::NotPresent(_) => (self.clone(), None),
                Loc::Here(i) => {
                    let p = tn.elts.val(i).clone();
                    let elts = tn.elts.remove_elt_at(i);
                    if elts.len() == 0 {
                        (Tree::concat(&tn.left, &tn.right), Some(p))
                    } else {
                        (Tree::create(&tn.left, Arc::new(elts), &tn.right), Some(p))
                    }
                }
                Loc::InLeft => {
                    let (l, p) = tn.left.remove(k);
                    (Tree::bal(&l, &tn.elts, &tn.right), p)
                }
                Loc::InRight => {
                    let (r, p) = tn.right.remove(k);
                    (Tree::bal(&tn.left, &tn.elts, &r), p)
                }
            },
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
        F: FnOnce(&'a Chunk<K, V>, usize) -> R,
        R: 'a,
    {
        match self {
            Tree::Empty => None,
            Tree::Node(n) => {
                let mut tn = n;
                loop {
                    match (k.cmp(tn.min_key.borrow()), k.cmp(tn.max_key.borrow())) {
                        (Ordering::Less, _) => match tn.left {
                            Tree::Empty => break None,
                            Tree::Node(ref n) => tn = n,
                        },
                        (_, Ordering::Greater) => match tn.right {
                            Tree::Empty => break None,
                            Tree::Node(ref n) => tn = n,
                        },
                        (_, _) => {
                            let e = &tn.elts;
                            break e.get_local(k).map(|i| f(e, i))
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
}

impl<K, V> Tree<K, V>
where
    K: Ord + Clone + Debug,
    V: Clone + Debug,
{
    #[allow(dead_code)]
    pub(crate) fn invariant(&self) -> () {
        fn in_range<K, V>(
            lower: Option<&K>,
            upper: Option<&K>,
            elts: &Chunk<K, V>,
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

        fn sorted<K, V>(elts: &Chunk<K, V>) -> bool
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

        fn check<K, V>(
            t: &Tree<K, V>,
            lower: Option<&K>,
            upper: Option<&K>,
            len: usize,
        ) -> (u16, usize)
        where
            K: Ord + Clone + Debug,
            V: Clone + Debug,
        {
            match *t {
                Tree::Empty => (0, len),
                Tree::Node(ref tn) => {
                    if !in_range(lower, upper, &tn.elts) {
                        panic!("tree invariant violated lower\n{:#?}\n\nupper\n{:#?}\n\nelts\n{:#?}\n\ntree\n{:#?}",
                               lower, upper, &tn.elts, t)
                    };
                    if !sorted(&tn.elts) {
                        panic!("elements isn't sorted")
                    };
                    let (thl, len) =
                        check(&tn.left, lower, tn.elts.min_elt().map(|(k, _)| k), len);
                    let (thr, len) =
                        check(&tn.right, tn.elts.max_elt().map(|(k, _)| k), upper, len);
                    let th = 1 + max(thl, thr);
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
                    (th, len + tn.elts.len())
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
