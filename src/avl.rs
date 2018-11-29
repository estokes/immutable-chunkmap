use arrayvec::ArrayVec;
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
    vec,
};

// until we get 128 bit machines with exabytes of memory
const MAX_DEPTH: usize = 64;

#[derive(PartialEq)]
enum Loc {
    InRight,
    InLeft,
    NotPresent(usize),
    Here(usize),
}

/*
elts is a sorted array of pairs, increasing the SIZE has several effects;
-- decreases the height of the tree for a given number of
elements, decreasing the amount of indirection necessary to
get to any given key.
-- decreases the number of objects allocated on the heap each
time a key is added or removed
-- increases the size of each allocation
-- icreases the overall amount of memory allocated for each change to the tree
 */
const SIZE: usize = 512;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Elts<K: Ord + Clone, V: Clone> {
    keys: Vec<K>,
    vals: Vec<V>,
}

impl<K, V> Debug for Elts<K, V>
where
    K: Debug + Ord + Clone,
    V: Debug + Clone,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_map().entries(self.into_iter()).finish()
    }
}

enum UpdateChunk<Q: Ord, K: Ord + Clone + Borrow<Q>, V: Clone, D> {
    UpdateLeft(Vec<(Q, D)>),
    UpdateRight(Vec<(Q, D)>),
    Created(Elts<K, V>),
    Updated {
        elts: Elts<K, V>,
        update_left: Vec<(Q, D)>,
        update_right: Vec<(Q, D)>,
        overflow_right: Vec<(K, V)>,
    },
    Removed {
        not_done: Vec<(Q, D)>,
        update_left: Vec<(Q, D)>,
        update_right: Vec<(Q, D)>,
    },
}

enum Update<Q: Ord, K: Ord + Clone + Borrow<Q>, V: Clone, D> {
    UpdateLeft(Q, D),
    UpdateRight(Q, D),
    Updated {
        elts: Elts<K, V>,
        overflow: Option<(K, V)>,
        previous: Option<V>,
    },
}

impl<K, V> Elts<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    fn singleton(k: K, v: V) -> Self {
        let mut t = Elts::with_capacity(1);
        t.keys.push(k);
        t.vals.push(v);
        t
    }

    fn empty() -> Self {
        Elts {
            keys: Vec::new(),
            vals: Vec::new(),
        }
    }

    fn with_capacity(n: usize) -> Self {
        Elts {
            keys: Vec::with_capacity(n),
            vals: Vec::with_capacity(n),
        }
    }

    fn get<Q: ?Sized + Ord>(&self, k: &Q) -> Loc
    where
        K: Borrow<Q>,
    {
        let len = self.len();
        if len == 0 {
            Loc::NotPresent(0)
        } else {
            let first = k.cmp(&self.keys[0].borrow());
            let last = k.cmp(&self.keys[len - 1].borrow());
            match (first, last) {
                (Ordering::Equal, _) => Loc::Here(0),
                (_, Ordering::Equal) => Loc::Here(len - 1),
                (Ordering::Less, _) => Loc::InLeft,
                (_, Ordering::Greater) => Loc::InRight,
                (Ordering::Greater, Ordering::Less) => {
                    match self.keys.binary_search_by_key(&k, |k| k.borrow()) {
                        Result::Ok(i) => Loc::Here(i),
                        Result::Err(i) => Loc::NotPresent(i),
                    }
                }
            }
        }
    }

    // chunk must be sorted
    fn update_chunk<Q, D, F>(
        &self,
        mut chunk: Vec<(Q, D)>,
        leaf: bool,
        f: &mut F,
    ) -> UpdateChunk<Q, K, V, D>
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        assert!(chunk.len() <= SIZE && chunk.len() > 0);
        if self.len() == 0 {
            let mut elts = Elts::empty();
            let (keys, vals): (Vec<_>, Vec<_>) =
                chunk.drain(0..).filter_map(|(q, d)| f(q, d, None)).unzip();
            elts.keys = keys;
            elts.vals = vals;
            UpdateChunk::Created(elts)
        } else {
            let full = !leaf || self.len() >= SIZE;
            let in_left = self.get(&chunk[chunk.len() - 1].0) == Loc::InLeft;
            let in_right = self.get(&chunk[0].0) == Loc::InRight;
            if full && in_left {
                UpdateChunk::UpdateLeft(chunk)
            } else if full && in_right {
                UpdateChunk::UpdateRight(chunk)
            } else if leaf && in_left {
                let mut elts = Elts::empty();
                let (keys, vals): (Vec<_>, Vec<_>) =
                    chunk.drain(0..).filter_map(|(q, d)| f(q, d, None)).unzip();
                elts.keys = keys;
                elts.vals = vals;
                elts.keys.extend_from_slice(&self.keys);
                elts.vals.extend_from_slice(&self.vals);
                let overflow_right = {
                    if elts.len() <= SIZE {
                        Vec::new()
                    } else {
                        elts.keys
                            .split_off(SIZE)
                            .into_iter()
                            .zip(elts.vals.split_off(SIZE).into_iter())
                            .collect::<Vec<_>>()
                    }
                };
                elts.keys.shrink_to_fit();
                elts.vals.shrink_to_fit();
                UpdateChunk::Updated {
                    elts,
                    update_left: Vec::new(),
                    update_right: Vec::new(),
                    overflow_right,
                }
            } else {
                let mut elts = self.clone();
                let mut not_done = Vec::new();
                let mut update_left = Vec::new();
                let mut update_right = Vec::new();
                let mut overflow_right = Vec::new();
                for (q, d) in chunk.drain(0..) {
                    if elts.len() == 0 {
                        not_done.push((q, d));
                        continue;
                    }
                    match elts.get(&q) {
                        Loc::Here(i) => {
                            match f(q, d, Some((&elts.keys[i], &elts.vals[i]))) {
                                None => {
                                    elts.keys.remove(i);
                                    elts.vals.remove(i);
                                }
                                Some((k, v)) => {
                                    elts.keys[i] = k;
                                    elts.vals[i] = v;
                                }
                            }
                        }
                        Loc::NotPresent(i) => {
                            if elts.len() < SIZE {
                                if let Some((k, v)) = f(q, d, None) {
                                    elts.keys.insert(i, k);
                                    elts.vals.insert(i, v);
                                }
                            } else {
                                if let Some((k, v)) = f(q, d, None) {
                                    overflow_right.push((
                                        elts.keys.pop().unwrap(),
                                        elts.vals.pop().unwrap(),
                                    ));
                                    elts.keys.insert(i, k);
                                    elts.vals.insert(i, v);
                                }
                            }
                        }
                        Loc::InLeft => {
                            if leaf && elts.keys.len() < SIZE {
                                if let Some((k, v)) = f(q, d, None) {
                                    elts.keys.insert(0, k);
                                    elts.vals.insert(0, v);
                                }
                            } else {
                                update_left.push((q, d))
                            }
                        }
                        Loc::InRight => {
                            if leaf && elts.len() < SIZE {
                                if let Some((k, v)) = f(q, d, None) {
                                    elts.keys.push(k);
                                    elts.vals.push(v);
                                }
                            } else {
                                update_right.push((q, d))
                            }
                        }
                    }
                }
                overflow_right.reverse();
                if elts.len() > 0 {
                    assert_eq!(not_done.len(), 0);
                    UpdateChunk::Updated {
                        elts,
                        update_left,
                        update_right,
                        overflow_right,
                    }
                } else {
                    assert_eq!(overflow_right.len(), 0);
                    UpdateChunk::Removed {
                        not_done,
                        update_left,
                        update_right,
                    }
                }
            }
        }
    }

    fn update<Q, D, F>(&self, q: Q, d: D, leaf: bool, f: &mut F) -> Update<Q, K, V, D>
    where
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        match self.get(&q) {
            Loc::Here(i) => {
                let mut elts = Elts::with_capacity(self.len());
                elts.keys.extend_from_slice(&self.keys[0..i]);
                elts.vals.extend_from_slice(&self.vals[0..i]);
                if let Some((k, v)) = f(q, d, Some((&self.keys[i], &self.vals[i]))) {
                    elts.keys.push(k);
                    elts.vals.push(v);
                }
                if i + 1 < self.len() {
                    elts.keys.extend_from_slice(&self.keys[i + 1..self.len()]);
                    elts.vals.extend_from_slice(&self.vals[i + 1..self.len()]);
                }
                Update::Updated {
                    elts,
                    overflow: None,
                    previous: Some(self.vals[i].clone()),
                }
            }
            Loc::NotPresent(i) => {
                let mut elts = Elts::with_capacity(self.len() + 1);
                elts.keys.extend_from_slice(&self.keys[0..i]);
                elts.vals.extend_from_slice(&self.vals[0..i]);
                if let Some((k, v)) = f(q, d, None) {
                    elts.keys.push(k);
                    elts.vals.push(v);
                }
                elts.keys.extend_from_slice(&self.keys[i..self.len()]);
                elts.vals.extend_from_slice(&self.vals[i..self.len()]);
                let overflow = {
                    if elts.len() <= SIZE {
                        None
                    } else {
                        elts.keys
                            .pop()
                            .and_then(|k| elts.vals.pop().map(move |v| (k, v)))
                    }
                };
                Update::Updated {
                    elts,
                    overflow,
                    previous: None,
                }
            }
            loc @ Loc::InLeft | loc @ Loc::InRight => {
                if !leaf || self.len() == SIZE {
                    match loc {
                        Loc::InLeft => Update::UpdateLeft(q, d),
                        Loc::InRight => Update::UpdateRight(q, d),
                        Loc::Here(..) | Loc::NotPresent(..) => unreachable!(),
                    }
                } else {
                    let mut elts = Elts::with_capacity(self.len() + 1);
                    match loc {
                        Loc::InLeft => {
                            if let Some((k, v)) = f(q, d, None) {
                                elts.keys.push(k);
                                elts.vals.push(v);
                            }
                            elts.keys.extend_from_slice(&self.keys[0..self.len()]);
                            elts.vals.extend_from_slice(&self.vals[0..self.len()]);
                        }
                        Loc::InRight => {
                            elts.keys.extend_from_slice(&self.keys[0..self.len()]);
                            elts.vals.extend_from_slice(&self.vals[0..self.len()]);
                            if let Some((k, v)) = f(q, d, None) {
                                elts.keys.push(k);
                                elts.vals.push(v);
                            }
                        }
                        _ => unreachable!("bug"),
                    };
                    Update::Updated {
                        elts,
                        overflow: None,
                        previous: None,
                    }
                }
            }
        }
    }

    fn remove_elt_at(&self, i: usize) -> Self {
        let mut elts = Elts::with_capacity(self.len() - 1);
        if self.len() == 0 {
            panic!("can't remove from an empty chunk")
        } else if self.len() == 1 {
            assert_eq!(i, 0);
            elts
        } else if i == 0 {
            elts.keys.extend_from_slice(&self.keys[1..self.len()]);
            elts.vals.extend_from_slice(&self.vals[1..self.len()]);
            elts
        } else if i == self.len() - 1 {
            elts.keys.extend_from_slice(&self.keys[0..self.len() - 1]);
            elts.vals.extend_from_slice(&self.vals[0..self.len() - 1]);
            elts
        } else {
            elts.keys.extend_from_slice(&self.keys[0..i]);
            elts.keys.extend_from_slice(&self.keys[i + 1..self.len()]);
            elts.vals.extend_from_slice(&self.vals[0..i]);
            elts.vals.extend_from_slice(&self.vals[i + 1..self.len()]);
            elts
        }
    }

    fn min_max_key(&self) -> Option<(K, K)> {
        if self.len() == 0 {
            None
        } else {
            Some((self.keys[0].clone(), self.keys[self.len() - 1].clone()))
        }
    }

    fn min_elt<'a>(&'a self) -> Option<(&'a K, &'a V)> {
        if self.len() == 0 {
            None
        } else {
            Some((&self.keys[0], &self.vals[0]))
        }
    }

    fn max_elt<'a>(&'a self) -> Option<(&'a K, &'a V)> {
        if self.len() == 0 {
            None
        } else {
            let last = self.len() - 1;
            Some((&self.keys[last], &self.vals[last]))
        }
    }

    fn len(&self) -> usize {
        self.keys.len()
    }
}

impl<K, V> IntoIterator for Elts<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    type Item = (K, V);
    type IntoIter = iter::Zip<vec::IntoIter<K>, vec::IntoIter<V>>;
    fn into_iter(self) -> Self::IntoIter {
        self.keys.into_iter().zip(self.vals)
    }
}

impl<'a, K, V> IntoIterator for &'a Elts<K, V>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
{
    type Item = (&'a K, &'a V);
    type IntoIter = iter::Zip<slice::Iter<'a, K>, slice::Iter<'a, V>>;
    fn into_iter(self) -> Self::IntoIter {
        (&self.keys).into_iter().zip(&self.vals)
    }
}

#[derive(Clone)]
pub(crate) struct Node<K: Ord + Clone, V: Clone> {
    elts: Arc<Elts<K, V>>,
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
        let l = n.elts.keys.len();
        match self.lbound {
            Bound::Unbounded => true,
            Bound::Included(ref bound) => l == 0 || n.elts.keys[l - 1].borrow() >= bound,
            Bound::Excluded(ref bound) => l == 0 || n.elts.keys[l - 1].borrow() > bound,
        }
    }

    fn any_elts_below_ubound(&self, n: &'a Node<K, V>) -> bool {
        let l = n.elts.keys.len();
        match self.ubound {
            Bound::Unbounded => true,
            Bound::Included(ref bound) => l == 0 || n.elts.keys[0].borrow() <= bound,
            Bound::Excluded(ref bound) => l == 0 || n.elts.keys[0].borrow() < bound,
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

    fn create(l: &Tree<K, V>, elts: &Arc<Elts<K, V>>, r: &Tree<K, V>) -> Self {
        let (min_key, max_key) = elts.min_max_key().unwrap();
        let n = Node {
            elts: elts.clone(),
            min_key: min_key,
            max_key: max_key,
            left: l.clone(),
            right: r.clone(),
            size_of_children: l.len() + r.len(),
            height: 1 + max(l.height(), r.height()),
        };
        Tree::Node(Arc::new(n))
    }

    fn bal(l: &Tree<K, V>, elts: &Arc<Elts<K, V>>, r: &Tree<K, V>) -> Self {
        let (hl, hr) = (l.height(), r.height());
        if hl > hr + 1 {
            match *l {
                Tree::Empty => panic!("tree heights wrong"),
                Tree::Node(ref ln) => if ln.left.height() >= ln.right.height() {
                    Tree::create(&ln.left, &ln.elts, &Tree::create(&ln.right, elts, r))
                } else {
                    match ln.right {
                        Tree::Empty => panic!("tree heights wrong"),
                        Tree::Node(ref lrn) => Tree::create(
                            &Tree::create(&ln.left, &ln.elts, &lrn.left),
                            &lrn.elts,
                            &Tree::create(&lrn.right, elts, r),
                        ),
                    }
                },
            }
        } else if hr > hl + 1 {
            match *r {
                Tree::Empty => panic!("tree heights are wrong"),
                Tree::Node(ref rn) => if rn.right.height() >= rn.left.height() {
                    Tree::create(&Tree::create(l, elts, &rn.left), &rn.elts, &rn.right)
                } else {
                    match rn.left {
                        Tree::Empty => panic!("tree heights are wrong"),
                        Tree::Node(ref rln) => Tree::create(
                            &Tree::create(l, elts, &rln.left),
                            &rln.elts,
                            &Tree::create(&rln.right, &rn.elts, &rn.right),
                        ),
                    }
                },
            }
        } else {
            Tree::create(l, elts, r)
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
                    let t = Elts::empty();
                    match t.update_chunk(chunk, true, f) {
                        UpdateChunk::Created(elts) => elts,
                        UpdateChunk::Removed { .. } => unreachable!(),
                        UpdateChunk::Updated { .. } => unreachable!(),
                        UpdateChunk::UpdateLeft(_) => unreachable!(),
                        UpdateChunk::UpdateRight(_) => unreachable!(),
                    }
                };
                Tree::create(&Tree::Empty, &Arc::new(elts), &Tree::Empty)
            }
            &Tree::Node(ref tn) => {
                let leaf = match (&tn.left, &tn.right) {
                    (&Tree::Empty, &Tree::Empty) => true,
                    (_, _) => false,
                };
                match tn.elts.update_chunk(chunk, leaf, f) {
                    UpdateChunk::Created(elts) => {
                        Tree::create(&tn.left, &Arc::new(elts), &tn.right)
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

    pub(crate) fn update_many<Q, D, E, F>(&self, elts: E, f: &mut F) -> Self
    where
        E: IntoIterator<Item = (Q, D)>,
        Q: Ord,
        K: Borrow<Q>,
        F: FnMut(Q, D, Option<(&K, &V)>) -> Option<(K, V)>,
    {
        let mut t = self.clone();
        let mut chunk: Vec<(Q, D)> = Vec::new();
        let do_chunk = |t: &mut Tree<K, V>, chunk: &mut Vec<(Q, D)>, f: &mut F| {
            if chunk.len() < 6 {
                for (q, d) in chunk.drain(0..) {
                    *t = t.update(q, d, f).0;
                }
            } else {
                let mut new_chunk = Vec::new();
                swap(&mut new_chunk, chunk);
                *t = t.update_chunk(new_chunk, f);
            }
        };
        for (q, d) in elts {
            let cmp = chunk.last().map(|p| p.0.cmp(&q));
            match cmp {
                None => chunk.push((q, d)),
                Some(Ordering::Equal) => {
                    let l = chunk.len();
                    chunk[l - 1] = (q, d)
                }
                Some(Ordering::Less) => {
                    chunk.push((q, d));
                    if chunk.len() >= SIZE {
                        do_chunk(&mut t, &mut chunk, f);
                    }
                }
                Some(Ordering::Greater) => {
                    do_chunk(&mut t, &mut chunk, f);
                    chunk.push((q, d))
                }
            }
        }
        do_chunk(&mut t, &mut chunk, f);
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
                        &Arc::new(Elts::singleton(k, v)),
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
                                    Tree::create(&tn.left, &Arc::new(elts), &tn.right),
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

    fn min_elts<'a>(&'a self) -> Option<&'a Arc<Elts<K, V>>> {
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
                    let p = tn.elts.vals[i].clone();
                    let elts = tn.elts.remove_elt_at(i);
                    if elts.len() == 0 {
                        (Tree::concat(&tn.left, &tn.right), Some(p))
                    } else {
                        (Tree::create(&tn.left, &Arc::new(elts), &tn.right), Some(p))
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
        F: FnOnce(&'a Elts<K, V>, usize) -> R,
        R: 'a,
    {
        match self {
            &Tree::Empty => None,
            &Tree::Node(ref n) => {
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
                            match e.keys.binary_search_by_key(&k, |k| k.borrow()) {
                                Ok(i) => break Some(f(e, i)),
                                Err(_) => break None,
                            }
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
        self.get_gen(k, |e, i| &e.vals[i])
    }

    pub(crate) fn get_key<'a, Q>(&'a self, k: &Q) -> Option<&'a K>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        self.get_gen(k, |e, i| &e.keys[i])
    }

    pub(crate) fn get_full<'a, Q>(&'a self, k: &Q) -> Option<(&'a K, &'a V)>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        self.get_gen(k, |e, i| (&e.keys[i], &e.vals[i]))
    }
}

impl<K, V> Tree<K, V>
where
    K: Ord + Clone + Debug,
    V: Clone + Debug,
{
    #[allow(dead_code)]
    pub(crate) fn invariant(&self) -> () {
        fn in_range<K, V>(lower: Option<&K>, upper: Option<&K>, elts: &Elts<K, V>) -> bool
        where
            K: Ord + Clone + Debug,
            V: Clone + Debug,
        {
            (match lower {
                None => true,
                Some(lower) => (&elts.keys)
                    .into_iter()
                    .all(|k| lower.cmp(k) == Ordering::Less),
            }) && (match upper {
                None => true,
                Some(upper) => (&elts.keys)
                    .into_iter()
                    .all(|k| upper.cmp(k) == Ordering::Greater),
            })
        }

        fn sorted<K, V>(elts: &Elts<K, V>) -> bool
        where
            K: Ord + Clone + Debug,
            V: Clone + Debug,
        {
            if elts.keys.len() == 1 {
                true
            } else {
                for i in 0..(elts.len() - 1) {
                    match elts.keys[i].cmp(&elts.keys[i + 1]) {
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
