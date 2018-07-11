macro_rules! avltree {
    ($pimport:path, $ptyp:ident, $pinit:path, $chunksize:expr) => {
        use $pimport;
        use arrayvec::ArrayVec;
        use std::{
            cmp::{Ord, Ordering, max, min}, fmt::Debug,
            borrow::Borrow, slice, iter, vec, ops::Bound
        };

        // until we get 128 bit machines with exabytes of memory
        const MAX_DEPTH : usize = 64;

        #[derive(PartialEq)]
        enum Loc {
            InRight,
            InLeft,            
            NotPresent(usize),
            Here(usize)
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
        const SIZE: usize = $chunksize;

        #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
        struct Elts<K: Ord + Clone + Debug, V: Clone + Debug> {
            keys: Vec<K>,
            vals: Vec<V>
        }

        enum UpdateChunk<K: Ord + Clone + Debug, V: Clone + Debug, D> {
            UpdateLeft(Vec<(K, D)>),
            UpdateRight(Vec<(K, D)>),
            Created {
                elts: Elts<K, V>,
                len: usize
            },
            Updated {
                elts: Elts<K, V>,
                len: usize,
                update_left: Vec<(K, D)>,
                update_right: Vec<(K, D)>,
                overflow_right: Vec<(K, V)>
            },
        }

        enum Update<K: Ord + Clone + Debug, V: Clone + Debug, D> {
            UpdateLeft(K, D),
            UpdateRight(K, D),
            Updated {
                elts: Elts<K, V>,
                len: usize,
                overflow: Option<(K, V)>,
                previous: Option<(K, V)>
            }
        }

        impl<K,V> Elts<K,V> where K: Ord + Clone + Debug, V: Clone + Debug {
            fn singleton(k: K, v: V) -> Self {
                let mut t = Elts::with_capacity(1);
                t.keys.push(k);
                t.vals.push(v);
                t
            }

            fn empty() -> Self { Elts {keys: Vec::new(), vals: Vec::new()} }

            fn with_capacity(n: usize) -> Self {
                Elts { keys: Vec::with_capacity(n), vals: Vec::with_capacity(n) }
            }
            
            fn get<Q: ?Sized + Ord>(&self, k: &Q) -> Loc where K: Borrow<Q> {
                let len = self.len();
                if len == 0 { Loc::NotPresent(0) }
                else {
                    let first = k.cmp(&self.keys[0].borrow());
                    let last = k.cmp(&self.keys[len - 1].borrow());
                    match (first, last) {
                        (Ordering::Equal, _) => Loc::Here(0),
                        (_, Ordering::Equal) => Loc::Here(len - 1),
                        (Ordering::Less, _) => Loc::InLeft,
                        (_, Ordering::Greater) => Loc::InRight,
                        (Ordering::Greater, Ordering::Less) =>
                            match self.keys.binary_search_by_key(&k, |k| k.borrow()) {
                                Result::Ok(i) => Loc::Here(i),
                                Result::Err(i) => Loc::NotPresent(i)
                            }
                    }
                }
            }

            fn get_noedge<Q: ?Sized + Ord>(&self, k: &Q) -> Loc where K: Borrow<Q> {
                match self.keys.binary_search_by_key(&k, |k| k.borrow()) {
                    Result::Ok(i) => Loc::Here(i),
                    Result::Err(i) => Loc::NotPresent(i)
                }
            }

            // chunk must be sorted
            fn update_chunk<D, F>(
                &self,
                mut chunk: Vec<(K, D)>,
                len: usize,
                leaf: bool,
                f: &mut F
            ) -> UpdateChunk<K, V, D>
            where F: FnMut(&K, D, Option<&V>) -> Option<V>,
            {
                assert!(chunk.len() <= SIZE && chunk.len() > 0);
                if self.len() == 0 {
                    let mut elts = Elts::empty();
                    let (keys, vals) : (Vec<_>, Vec<_>) =
                        chunk.drain(0..)
                        .filter_map(|(k, d)| f(&k, d, None).map(move |v| (k, v)))
                        .unzip();
                    elts.keys = keys;
                    elts.vals = vals;
                    let len = len + elts.len();
                    UpdateChunk::Created { elts, len }
                } else {
                    let full = !leaf || self.len() >= SIZE;
                    let in_left = self.get(&chunk[chunk.len() - 1].0) == Loc::InLeft;
                    let in_right = self.get(&chunk[0].0) == Loc::InRight;
                    if full && in_left { UpdateChunk::UpdateLeft(chunk) }
                    else if full && in_right { UpdateChunk::UpdateRight(chunk) }
                    else if leaf && in_left {
                        let mut elts = Elts::empty();
                        let (keys, vals) : (Vec<_>, Vec<_>) =
                            chunk.drain(0..)
                            .filter_map(|(k, d)| f(&k, d, None).map(move |v| (k, v)))
                            .unzip();
                        elts.keys = keys;
                        elts.vals = vals;
                        elts.keys.extend_from_slice(&self.keys);
                        elts.vals.extend_from_slice(&self.vals);
                        let overflow_right = {
                            if elts.len() <= SIZE { Vec::new() }
                            else {
                                elts.keys.split_off(SIZE).into_iter()
                                    .zip(elts.vals.split_off(SIZE).into_iter())
                                    .collect::<Vec<_>>()
                            }
                        };
                        elts.keys.shrink_to_fit();
                        elts.vals.shrink_to_fit();
                        let len = len + (elts.len() - self.len());
                        UpdateChunk::Updated {
                            elts, len,
                            update_left: Vec::new(),
                            update_right: Vec::new(),
                            overflow_right
                        }
                    } else {
                        let mut elts =
                            Elts::with_capacity(min(SIZE, self.len() + chunk.len()));
                        elts.clone_from(&self);
                        let mut update_left = Vec::new();
                        let mut update_right = Vec::new();
                        let mut overflow_right = Vec::new();
                        for (k, d) in chunk.drain(0..) {
                            match elts.get(&k) {
                                Loc::Here(i) => {
                                    if let Some(v) = f(&k, d, Some(&elts.vals[i])) {
                                        elts.keys[i] = k;
                                        elts.vals[i] = v;
                                    }
                                },
                                Loc::NotPresent(i) =>
                                    if elts.len() < SIZE {
                                        if let Some(v) = f(&k, d, None) {
                                            elts.keys.insert(i, k);
                                            elts.vals.insert(i, v);
                                        }
                                    } else {
                                        if let Some(v) = f(&k, d, None) {
                                            overflow_right.push(
                                                (elts.keys.pop().unwrap(),
                                                 elts.vals.pop().unwrap())
                                            );
                                            elts.keys.insert(i, k);
                                            elts.vals.insert(i, v);
                                        }
                                    },
                                Loc::InLeft =>
                                    if leaf && elts.keys.len() < SIZE {
                                        if let Some(v) = f(&k, d, None) {
                                            elts.keys.insert(0, k);
                                            elts.vals.insert(0, v);
                                        }
                                    } else {
                                        update_left.push((k, d))
                                    },
                                Loc::InRight =>
                                    if leaf && elts.len() < SIZE {
                                        if let Some(v) = f(&k, d, None) {
                                            elts.keys.push(k);
                                            elts.vals.push(v);
                                        }
                                    } else {
                                        update_right.push((k, d))
                                    }
                            }
                        }
                        overflow_right.reverse();
                        let len = len + (elts.len() - self.len());
                        UpdateChunk::Updated {
                            elts, len, update_left, update_right, overflow_right
                        }
                    }
                }
            }

            fn update<D, F>(
                &self, k: K, d: D, len: usize, leaf: bool, f: &mut F
            ) -> Update<K, V, D>
            where F: FnMut(&K, D, Option<&V>) -> Option<V> {
                match self.get(&k) {
                    Loc::Here(i) => {
                        let mut elts = Elts::with_capacity(self.len());
                        elts.keys.extend_from_slice(&self.keys[0..i]);
                        elts.vals.extend_from_slice(&self.vals[0..i]);
                        if let Some(v) = f(&k, d, Some(&self.vals[i])) {
                            elts.keys.push(k);
                            elts.vals.push(v);
                        }
                        if i + 1 < self.len() {
                            elts.keys.extend_from_slice(&self.keys[i+1..self.len()]);
                            elts.vals.extend_from_slice(&self.vals[i+1..self.len()]);
                        }
                        let len = len + (elts.len() - self.len());
                        Update::Updated {
                            elts, len, overflow: None,
                            previous: Some((self.keys[i].clone(), self.vals[i].clone()))
                        }
                    },
                    Loc::NotPresent(i) => {
                        let mut elts = Elts::with_capacity(self.len() + 1);
                        elts.keys.extend_from_slice(&self.keys[0..i]);
                        elts.vals.extend_from_slice(&self.vals[0..i]);
                        if let Some(v) = f(&k, d, None) {
                            elts.keys.push(k);
                            elts.vals.push(v);
                        }
                        elts.keys.extend_from_slice(&self.keys[i..self.len()]);
                        elts.vals.extend_from_slice(&self.vals[i..self.len()]);
                        let overflow = {
                            if elts.len() <= SIZE { None }
                            else {
                                elts.keys.pop()
                                    .and_then(|k| elts.vals.pop().map(move |v| (k, v)))
                            }
                        };
                        let len = len + (elts.len() - self.len());
                        Update::Updated { elts, len, overflow, previous: None }
                    },
                    loc @ Loc::InLeft | loc @ Loc::InRight => {
                        if !leaf || self.len() == SIZE {
                            match loc {
                                Loc::InLeft => Update::UpdateLeft(k, d),
                                Loc::InRight => Update::UpdateRight(k, d),
                                Loc::Here(..) | Loc::NotPresent(..) => unreachable!()
                            }
                        } else {
                            let mut elts = Elts::with_capacity(self.len() + 1);
                            match loc {
                                Loc::InLeft => {
                                    if let Some(v) = f(&k, d, None) {
                                        elts.keys.push(k);
                                        elts.vals.push(v);
                                    }
                                    elts.keys.extend_from_slice(&self.keys[0..self.len()]);
                                    elts.vals.extend_from_slice(&self.vals[0..self.len()]);
                                },
                                Loc::InRight => {
                                    elts.keys.extend_from_slice(&self.keys[0..self.len()]);
                                    elts.vals.extend_from_slice(&self.vals[0..self.len()]);
                                    if let Some(v) = f(&k, d, None) {
                                        elts.keys.push(k);
                                        elts.vals.push(v);
                                    }
                                },
                                _ => unreachable!("bug")
                            };
                            let len = len + (elts.len() - self.len());
                            Update::Updated { elts, len, overflow: None, previous: None }
                        }
                    }
                }
            }

            fn remove_elt_at(&self, i: usize) -> Self {
                let mut elts = Elts::with_capacity(self.len() - 1);
                if self.len() == 0 { panic!("can't remove from an empty chunk") }
                else if self.len() == 1 { assert_eq!(i, 0); elts }
                else if i == 0 {
                    elts.keys.extend_from_slice(&self.keys[1..self.len()]);
                    elts.vals.extend_from_slice(&self.vals[1..self.len()]);
                    elts
                } else if i == self.len() - 1 {
                    elts.keys.extend_from_slice(&self.keys[0..self.len() - 1]);
                    elts.vals.extend_from_slice(&self.vals[0..self.len() - 1]);
                    elts
                } else {
                    elts.keys.extend_from_slice(&self.keys[0..i]);
                    elts.keys.extend_from_slice(&self.keys[i+1..self.len()]);
                    elts.vals.extend_from_slice(&self.vals[0..i]);
                    elts.vals.extend_from_slice(&self.vals[i+1..self.len()]);
                    elts
                }
            }

            fn min_max_key(&self) -> Option<(K, K)> {
                if self.len() == 0 { None }
                else {
                    Some((self.keys[0].clone(), self.keys[self.len() - 1].clone()))
                }
            }

            fn min_elt<'a>(&'a self) -> Option<(&'a K, &'a V)> {
                if self.len() == 0 { None }
                else { Some((&self.keys[0], &self.vals[0])) }
            }

            fn max_elt<'a>(&'a self) -> Option<(&'a K, &'a V)> {
                if self.len() == 0 { None }
                else {
                    let last = self.len() - 1;
                    Some((&self.keys[last], &self.vals[last]))
                }
            }

            fn len(&self) -> usize { self.keys.len() }
        }

        impl<K, V> IntoIterator for Elts<K, V>
        where K: Ord + Clone + Debug, V: Clone + Debug
        {
            type Item = (K, V);
            type IntoIter = iter::Zip<vec::IntoIter<K>, vec::IntoIter<V>>;
            fn into_iter(self) -> Self::IntoIter {
                self.keys.into_iter().zip(self.vals)
            }
        }

        impl<'a, K, V> IntoIterator for &'a Elts<K, V>
        where K: 'a + Ord + Clone + Debug, V: 'a + Clone + Debug
        {
            type Item = (&'a K, &'a V);
            type IntoIter = iter::Zip<slice::Iter<'a, K>, slice::Iter<'a, V>>;
            fn into_iter(self) -> Self::IntoIter {
                (&self.keys).into_iter().zip(&self.vals)
            }
        }

        #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub(crate) struct Node<K: Ord + Clone + Debug, V: Clone + Debug> {
            elts: $ptyp<Elts<K, V>>,
            min_key: K,
            max_key: K,
            left: Tree<K, V>,
            right: Tree<K, V>,
            height: u16,
        }

        #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub(crate) enum Tree<K: Ord + Clone + Debug, V: Clone + Debug> {
            Empty,
            Node($ptyp<Node<K,V>>)
        }

        #[derive(Debug)]
        pub struct Iter<'a, Q, K, V>
        where
            Q: Ord,
            K: 'a + Borrow<Q> + Ord + Clone + Debug,
            V: 'a + Clone + Debug
        {
            ubound: Bound<Q>,
            lbound: Bound<Q>,
            stack: ArrayVec<[(bool, &'a Node<K,V>); MAX_DEPTH]>,
            elts: Option<iter::Zip<slice::Iter<'a, K>, slice::Iter<'a, V>>>,
            current: Option<&'a K>,
            stack_rev: ArrayVec<[(bool, &'a Node<K,V>); MAX_DEPTH]>,
            elts_rev: Option<iter::Zip<slice::Iter<'a, K>, slice::Iter<'a, V>>>,
            current_rev: Option<&'a K>,
        }

        impl<'a, Q, K, V> Iter<'a, Q, K, V>
        where
            Q: Ord,
            K: 'a + Borrow<Q> + Ord + Clone + Debug,
            V: 'a + Clone + Debug
        {
            // is at least one element of the chunk in bounds
            fn any_elts_above_lbound(&self, n: &'a Node<K, V>) -> bool {
                let l = n.elts.keys.len();
                match self.lbound {
                    Bound::Unbounded => true,
                    Bound::Included(ref bound) =>
                        l == 0 || n.elts.keys[l - 1].borrow() >= bound,
                    Bound::Excluded(ref bound) =>
                        l == 0 || n.elts.keys[l - 1].borrow() > bound
                }
            }

            fn any_elts_below_ubound(&self, n: &'a Node<K, V>) -> bool {
                let l = n.elts.keys.len();
                match self.ubound {
                    Bound::Unbounded => true,
                    Bound::Included(ref bound) =>
                        l == 0 || n.elts.keys[0].borrow() <= bound,
                    Bound::Excluded(ref bound) =>
                        l == 0 || n.elts.keys[0].borrow() < bound
                }
            }

            fn any_elts_in_bounds(&self, n: &'a Node<K, V>) -> bool {
                self.any_elts_above_lbound(n) && self.any_elts_below_ubound(n)
            }

            fn above_lbound(&self, k: &'a K) -> bool {
                match self.lbound {
                    Bound::Unbounded => true,
                    Bound::Included(ref bound) => k.borrow() >= bound,
                    Bound::Excluded(ref bound) => k.borrow() > bound
                }
            }

            fn below_ubound(&self, k: &'a K) -> bool {
                match self.ubound {
                    Bound::Unbounded => true,
                    Bound::Included(ref bound) => k.borrow() <= bound,
                    Bound::Excluded(ref bound) => k.borrow() < bound
                }
            }
        }

        impl<'a, Q, K, V> Iterator for Iter<'a, Q, K, V>
        where
            Q: Ord,
            K: 'a + Borrow<Q> + Ord + Clone + Debug,
            V: 'a + Clone + Debug
        {
            type Item = (&'a K, &'a V);
            fn next(&mut self) -> Option<Self::Item> {
                loop {
                    loop {
                        let (k, v) =
                            match &mut self.elts {
                                &mut None => break,
                                &mut Some(ref mut s) =>
                                    match s.next() {
                                        None => break,
                                        Some((k, v)) => (k, v)
                                    }
                            };
                        if let Some(back) = self.current_rev {
                            if k >= back { return None }
                        }
                        if !self.below_ubound(k) { return None }
                        self.current = Some(k);
                        if self.above_lbound(k) {
                            return Some((k, v))
                        }
                    };
                    if self.stack.is_empty() { return None }
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
            K: 'a + Borrow<Q> + Ord + Clone + Debug,
            V: 'a + Clone + Debug
        {
            fn next_back(&mut self) -> Option<Self::Item> {
                loop {
                    loop {
                        let (k, v) =
                            match &mut self.elts_rev {
                                &mut None => break,
                                &mut Some(ref mut s) =>
                                    match s.next_back() {
                                        None => break,
                                        Some((k, v)) => (k, v)
                                    }
                            };
                        if let Some(front) = self.current {
                            if k <= front { return None }
                        }
                        if !self.above_lbound(k) { return None }
                        self.current_rev = Some(k);
                        if self.below_ubound(k) {
                            return Some((k, v))
                        }
                    };
                    if self.stack_rev.is_empty() { return None }
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
                    }
                    else {
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
            K: 'a + Borrow<K> + Ord + Clone + Debug,
            V: 'a + Clone + Debug
        {
            type Item = (&'a K, &'a V);
            type IntoIter = Iter<'a, K, K, V>;
            fn into_iter(self) -> Self::IntoIter {
                self.range(Bound::Unbounded, Bound::Unbounded)
            }
        }

        impl<K,V> Tree<K,V> where K: Ord + Clone + Debug, V: Clone + Debug {
            pub(crate) fn new() -> Self { Tree::Empty }

            pub(crate) fn range<'a, Q>(
                &'a self, lbound: Bound<Q>, ubound: Bound<Q>
            ) -> Iter<'a, Q, K, V>
            where Q: Ord, K: Borrow<Q>
            {
                match self {
                    &Tree::Empty =>
                        Iter {
                            lbound, ubound,
                            stack: ArrayVec::<[_; MAX_DEPTH]>::new(),
                            elts: None, current: None,
                            stack_rev: ArrayVec::<[_; MAX_DEPTH]>::new(),
                            elts_rev: None, current_rev: None
                        },
                    &Tree::Node(ref n) => {
                        let mut stack =
                            ArrayVec::<[(bool, &'a Node<K, V>); MAX_DEPTH]>::new();
                        let mut stack_rev =
                            ArrayVec::<[(bool, &'a Node<K, V>); MAX_DEPTH]>::new();
                        stack.push((false, n));
                        stack_rev.push((false, n));
                        Iter {
                            lbound, ubound, stack, elts: None,
                            current: None, stack_rev, elts_rev: None,
                            current_rev: None
                        }
                    }
                }
            }

            fn is_empty(&self) -> bool {
                match self {
                    Tree::Empty => true,
                    Tree::Node(..) => false
                }
            }
            
            fn height(&self) -> u16 {
                match self {
                    &Tree::Empty => 0,
                    &Tree::Node(ref n) => n.height
                }
            }

            fn create(l: &Tree<K, V>, elts: &$ptyp<Elts<K, V>>, r: &Tree<K, V>) -> Self {
                let (min_key, max_key) = elts.min_max_key().unwrap();
                let n =
                    Node { elts: elts.clone(),
                           min_key: min_key,
                           max_key: max_key,
                           left: l.clone(), right: r.clone(),
                           height: 1 + max(l.height(), r.height()) };
                Tree::Node($pinit(n))
            }

            fn bal(l: &Tree<K, V>, elts: &$ptyp<Elts<K, V>>, r: &Tree<K, V>) -> Self {
                let (hl, hr) = (l.height(), r.height());
                if hl > hr + 1 {
                    match *l {
                        Tree::Empty => panic!("tree heights wrong"),
                        Tree::Node(ref ln) =>
                            if ln.left.height() >= ln.right.height() {
                                Tree::create(
                                    &ln.left, &ln.elts, &Tree::create(&ln.right, elts, r)
                                )
                            } else {
                                match ln.right {
                                    Tree::Empty => panic!("tree heights wrong"),
                                    Tree::Node(ref lrn) =>
                                        Tree::create(
                                            &Tree::create(&ln.left, &ln.elts, &lrn.left),
                                            &lrn.elts,
                                            &Tree::create(&lrn.right, elts, r)
                                        )
                                }
                            }
                    }
                } else if hr > hl + 1 {
                    match *r {
                        Tree::Empty => panic!("tree heights are wrong"),
                        Tree::Node(ref rn) =>
                            if rn.right.height() >= rn.left.height() {
                                Tree::create(
                                    &Tree::create(l, elts, &rn.left), &rn.elts, &rn.right
                                )
                            } else {
                                match rn.left {
                                    Tree::Empty => panic!("tree heights are wrong"),
                                    Tree::Node(ref rln) =>
                                        Tree::create(
                                            &Tree::create(l, elts, &rln.left),
                                            &rln.elts,
                                            &Tree::create(&rln.right, &rn.elts, &rn.right)
                                        )
                                }
                            }
                    }
                } else {
                    Tree::create(l, elts, r)
                }
            }

            fn update_chunk<D, F>(
                &self,
                len: usize,
                chunk: Vec<(K, D)>,
                f: &mut F,
            ) -> (Self, usize)
            where F: FnMut(&K, D, Option<&V>) -> Option<V>
            {
                if chunk.len() == 0 { return (self.clone(), len) }
                match self {
                    &Tree::Empty => {
                        let (elts, len) = {
                            let t = Elts::empty();
                            match t.update_chunk(chunk, len, true, f) {
                                UpdateChunk::Created {elts, len} => (elts, len),
                                UpdateChunk::Updated {..} => unreachable!(),
                                UpdateChunk::UpdateLeft(_) => unreachable!(),
                                UpdateChunk::UpdateRight(_) => unreachable!()
                            }
                        };
                        (Tree::create(&Tree::Empty, &$pinit(elts), &Tree::Empty), len)
                    },
                    &Tree::Node(ref tn) => {
                        let leaf =
                            match (&tn.left, &tn.right) {
                                (&Tree::Empty, &Tree::Empty) => true,
                                (_, _) => false
                            };
                        match tn.elts.update_chunk(chunk, len, leaf, f) {
                            UpdateChunk::Created { elts, len } =>
                                (Tree::create(&tn.left, &$pinit(elts), &tn.right), len),
                            UpdateChunk::Updated {
                                elts, len, update_left, update_right, overflow_right
                            } => {
                                if update_left.len() == 0 &&
                                    update_right.len() == 0 &&
                                    overflow_right.len() == 0
                                {
                                    if elts.len() == 0 {
                                        (Tree::concat(&tn.left, &tn.right), len)
                                    } else {
                                        (Tree::create(&tn.left, &$pinit(elts), &tn.right),
                                         len)
                                    }
                                } else {
                                    let (l, len) =
                                        tn.left.update_chunk(len, update_left, f);
                                    let (r, len) =
                                        tn.right.insert_chunk(len, overflow_right);
                                    let (r, len) =
                                        r.update_chunk(len, update_right, f);
                                    if elts.len() == 0 {
                                        (Tree::concat(&l, &r), len)
                                    } else {
                                        (Tree::bal(&l, &$pinit(elts), &r), len)
                                    }
                                }
                            },
                            UpdateChunk::UpdateLeft(chunk) => {
                                let (l, len) = tn.left.update_chunk(len, chunk, f);
                                (Tree::bal(&l, &tn.elts, &tn.right), len)
                            },
                            UpdateChunk::UpdateRight(chunk) => {
                                let (r, len) = tn.right.update_chunk(len, chunk, f);
                                (Tree::bal(&tn.left, &tn.elts, &r), len)
                            }
                        }
                    }
                }
            }

            fn insert_chunk(&self, len: usize, chunk: Vec<(K, V)>) -> (Self, usize) {
                self.update_chunk(len, chunk, &mut |_, v, _| Some(v))
            }

            pub(crate) fn update_many<D, E, F>(
                &self, len: usize, elts: E, f: &mut F,
            ) -> (Self, usize)
            where E: IntoIterator<Item=(K, D)>,
                  F: FnMut(&K, D, Option<&V>) -> Option<V> {
                let mut t = (self.clone(), len);
                let mut chunk = Vec::new();
                let mut elts = elts.into_iter();
                match elts.next() {
                    None => t,
                    Some((k, d)) => {
                        let mut prev = (k, d);
                        for (k, d) in elts {
                            match k.cmp(&prev.0) {
                                Ordering::Equal => prev = (k, d),
                                Ordering::Greater => {
                                    chunk.push(prev);
                                    prev = (k, d);
                                    if chunk.len() >= SIZE {
                                        t = t.0.update_chunk(t.1, chunk, f);
                                        chunk = Vec::new();
                                    }
                                },
                                Ordering::Less => {
                                    if chunk.len() > 0 {
                                        if chunk.len() < SIZE / 8 {
                                            for (k, d) in chunk.drain(0..) {
                                                let (z, l, _) = t.0.update(t.1, k, d, f);
                                                t = (z, l);
                                            }
                                        } else {
                                            t = t.0.update_chunk(t.1, chunk, f);
                                            chunk = Vec::new();
                                        }
                                    }
                                    let (z, len, _) = t.0.update(t.1, prev.0, prev.1, f);
                                    t = (z, len);
                                    prev = (k, d)
                                }
                            }
                        }
                        if chunk.len() > 0 {
                            chunk.push(prev);
                            t.0.update_chunk(t.1, chunk, f)
                        } else {
                            let (z, len, _) = t.0.update(t.1, prev.0, prev.1, f);
                            (z, len)
                        }
                    }
                }
            }

            pub(crate) fn insert_many<E: IntoIterator<Item=(K, V)>>(
                &self, len: usize, elts: E
            ) -> (Self, usize) {
                self.update_many(len, elts, &mut |_, v, _| Some(v))
            }

            pub(crate) fn update<D, F>(
                &self, len: usize, k: K, d: D, f: &mut F
            ) -> (Self, usize, Option<(K, V)>)
            where F: FnMut(&K, D, Option<&V>) -> Option<V> {
                match self {
                    &Tree::Empty =>
                        match f(&k, d, None) {
                            None => (self.clone(), len, None),
                            Some(v) =>
                                (Tree::create(
                                    &Tree::Empty,
                                    &$pinit(Elts::singleton(k, v)), &Tree::Empty),
                                 len + 1, None)
                        },
                    &Tree::Node(ref tn) => {
                        let leaf =
                            match (&tn.left, &tn.right) {
                                (&Tree::Empty, &Tree::Empty) => true,
                                (_, _) => false
                            };
                        match tn.elts.update(k, d, len, leaf, f) {
                            Update::UpdateLeft(k, d) => {
                                let (l, len, prev) = tn.left.update(len, k, d, f);
                                (Tree::bal(&l, &tn.elts, &tn.right), len, prev)
                            },
                            Update::UpdateRight(k, d) => {
                                let (r, len, prev) = tn.right.update(len, k, d, f);
                                (Tree::bal(&tn.left, &tn.elts, &r), len, prev)
                            },
                            Update::Updated {elts, len, overflow, previous} => {
                                match overflow {
                                    None => {
                                        if elts.len() == 0 {
                                            (Tree::concat(&tn.left, &tn.right), len,
                                             previous)
                                        } else {
                                            (Tree::create(
                                                &tn.left, &$pinit(elts), &tn.right),
                                             len, previous)
                                        }
                                    },
                                    Some((ovk, ovv)) => {
                                        let (r, len, _) = tn.right.insert(len, ovk, ovv);
                                        if elts.len() == 0 {
                                            (Tree::concat(&tn.left, &r), len, previous)
                                        } else {
                                            (Tree::bal(&tn.left, &$pinit(elts), &r),
                                             len, previous)
                                        }
                                    }
                                }
                            },
                        }
                    }
                }
            }

            pub(crate) fn insert(
                &self, len: usize, k: K, v: V
            ) -> (Self, usize, Option<(K, V)>) {
                self.update(len, k, v, &mut |_, v, _| Some(v))
            }

            fn min_elts<'a>(&'a self) -> Option<&'a $ptyp<Elts<K,V>>> {
                match self {
                    &Tree::Empty => None,
                    &Tree::Node(ref tn) =>
                        match tn.left {
                            Tree::Empty => Some(&tn.elts),
                            Tree::Node(_) => tn.left.min_elts()
                        }
                }
            }

            fn remove_min_elts(&self) -> Self {
                match self {
                    &Tree::Empty => panic!("remove min elt"),
                    &Tree::Node(ref tn) =>
                        match tn.left {
                            Tree::Empty => tn.right.clone(),
                            Tree::Node(_) =>
                                Tree::bal(&tn.left.remove_min_elts(), &tn.elts, &tn.right)
                        }
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

            pub(crate) fn remove<Q: ?Sized + Ord>(
                &self, len: usize, k: &Q
            ) -> (Self, usize) where K: Borrow<Q> {
                match self {
                    &Tree::Empty => (Tree::Empty, len),
                    &Tree::Node(ref tn) =>
                        match tn.elts.get(k) {
                            Loc::NotPresent(_) => (self.clone(), len),
                            Loc::Here(i) => {
                                let elts = tn.elts.remove_elt_at(i);
                                let len = len - 1;
                                if elts.len() == 0 {
                                    (Tree::concat(&tn.left, &tn.right), len)
                                } else {
                                    (Tree::create(&tn.left, &$pinit(elts), &tn.right), len)
                                }
                            }
                            Loc::InLeft => {
                                let (l, len) = tn.left.remove(len, k);
                                (Tree::bal(&l, &tn.elts, &tn.right), len)
                            }
                            Loc::InRight => {
                                let (r, len) = tn.right.remove(len, k);
                                (Tree::bal(&tn.left, &tn.elts, &r), len)
                            }
                        }
                }
            }

            pub(crate) fn get<'a, Q: ?Sized + Ord + Debug>(
                &'a self, k: &Q
            ) -> Option<&'a V> where K: Borrow<Q> {
                match self {
                    &Tree::Empty => None,
                    &Tree::Node(ref tn) =>
                        match (k.cmp(tn.min_key.borrow()), k.cmp(tn.max_key.borrow())) {
                            (Ordering::Less, _) => tn.left.get(k),
                            (_, Ordering::Greater) => tn.right.get(k),
                            (_, _) =>
                                match tn.elts.get_noedge(k) {
                                    Loc::Here(i) => Some(&tn.elts.vals[i]),
                                    Loc::NotPresent(_) => None,
                                    Loc::InLeft => unreachable!("bug"),
                                    Loc::InRight => unreachable!("bug")
                                }
                        }
                }
            }

            #[allow(dead_code)]
            pub(crate) fn invariant(&self, len: usize) -> () {
                fn in_range<K,V>(
                    lower: Option<&K>, upper: Option<&K>, elts: &Elts<K,V>
                ) -> bool
                where K: Ord + Clone + Debug, V: Clone + Debug {
                    (match lower {
                        None => true,
                        Some(lower) =>
                            (&elts.keys).into_iter().all(|k| {
                                lower.cmp(k) == Ordering::Less
                            })
                    }) && (match upper {
                        None => true,
                        Some(upper) =>
                            (&elts.keys).into_iter().all(|k| {
                                upper.cmp(k) == Ordering::Greater
                            })
                    })
                }

                fn sorted<K,V>(elts: &Elts<K,V>) -> bool
                where K: Ord + Clone + Debug, V: Clone + Debug
                {
                    if elts.keys.len() == 1 { true }
                    else {
                        for i in 0..(elts.len() - 1) {
                            match elts.keys[i].cmp(&elts.keys[i + 1]) {
                                Ordering::Greater => return false,
                                Ordering::Less => (),
                                Ordering::Equal => panic!("duplicates found: {:?}", elts)
                            }
                        }
                        true
                    }
                }

                fn check<K,V>(
                    t: &Tree<K,V>, lower: Option<&K>, upper: Option<&K>, len: usize
                ) -> (u16, usize)
                where K: Ord + Clone + Debug, V: Clone + Debug {
                    match *t {
                        Tree::Empty => (0, len),
                        Tree::Node(ref tn) => {
                            if !in_range(lower, upper, &tn.elts) {
                                panic!("tree invariant violated lower {:?} upper {:?} elts {:?}, tree {:?}",
                                       lower, upper, &tn.elts, t)
                            };
                            if !sorted(&tn.elts) { panic!("elements isn't sorted") };
                            let (thl, len) =
                                check(&tn.left, lower,
                                      tn.elts.min_elt().map(|(k, _)| k), len);
                            let (thr, len) =
                                check(&tn.right,
                                      tn.elts.max_elt().map(|(k, _)| k), upper, len);
                            let th = 1 + max(thl, thr);
                            let (hl, hr) = (tn.left.height(), tn.right.height());
                            let ub = max(hl, hr) - min(hl, hr);
                            if thl != hl { panic!("left node height is wrong") };
                            if thr != hr { panic!("right node height is wrong") };
                            let h = t.height();
                            if th != h { panic!("node height is wrong {} vs {}", th, h) };
                            if ub > 2 {
                                panic!("tree is unbalanced {:?} tree: {:?}", ub, t)
                            };
                            (th, len + tn.elts.len())
                        }
                    }
                }

                //println!("{:?}", self);
                let (_height, tlen) = check(self, None, None, 0);
                if len != tlen { panic!("len is wrong {} vs {}", len, tlen) }
            }
        }
    };
}
