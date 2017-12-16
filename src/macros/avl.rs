macro_rules! avltree {
  ($pimport:path, $ptyp:ident, $pinit:path, $chunksize:expr) => {
    use $pimport;
    use std::cmp::{Ord, Ordering, max, min};
    use std::fmt::Debug;
    use std::borrow::Borrow;
    use std::slice;
    use std::iter;
    use std::vec;

    #[derive(Debug)]
    enum Dir {
      InRight,
      InLeft
    }

    #[derive(PartialEq)]
    enum Loc {
      InRight,
      InLeft,
      NotPresent(usize), // the index in the array where the element would be if it was present
      Here(usize) // the index in the array where the equal element is
    }

    impl Loc {
      fn to_dir(&self) -> Dir {
        match self {
          &Loc::InLeft => Dir::InLeft,
          &Loc::InRight => Dir::InRight,
          &Loc::NotPresent(_) | &Loc::Here(_) => panic!("invalid dir")
        }
      }
    }

    /* 
      elts is a sorted array of pairs, increasing the SIZE has several effects; 
      -- decreases the height of the tree for a given number of elements, decreasing the amount of 
          indirection necessary to get to any given key. 
      -- decreases the number of objects allocated on the heap each time a key is added or removed
      -- increases the size of each allocation
      -- icreases the overall amount of memory allocated for each change to the tree
    */
    const SIZE: usize = $chunksize;

    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    struct Elts<K: Ord + Clone + Debug, V: Clone + Debug> {
      keys: Vec<K>,
      vals: Vec<V>
    }

    impl<K,V> Elts<K,V> where K: Ord + Clone + Debug, V: Clone + Debug {
      fn singleton(k: &K, v: &V) -> Self {
        let mut keys = Vec::<K>::new();
        let mut vals = Vec::<V>::new();
        keys.push(k.clone());
        vals.push(v.clone());
        Elts { keys: keys, vals: vals }
      }

      fn empty() -> Self { Elts {keys: Vec::<K>::new(), vals: Vec::<V>::new()} }

      fn find<Q: ?Sized + Ord>(&self, k: &Q) -> Loc where K: Borrow<Q>, Q: Sized {
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

      fn find_noedge<Q: ?Sized + Ord>(&self, k: &Q) -> Loc where K: Borrow<Q>, Q: Sized {
        match self.keys.binary_search_by_key(&k, |k| k.borrow()) {
          Result::Ok(i) => Loc::Here(i),
          Result::Err(i) => Loc::NotPresent(i)
        }
      }

      // chunk must be sorted
      fn add_chunk(&self, chunk: &mut Vec<(K, V)>, len: usize, leaf: bool) 
        -> Result<(Self, usize, usize), Dir>
      {
        assert!(chunk.len() <= SIZE);
        if chunk.len() == 0 { Result::Ok((self.clone(), len, 0)) }
        else if self.len() == 0 {
          let mut t = Elts::empty();
          let n = chunk.len();
          for _ in 0..n {
            let (k, v) = chunk.pop().unwrap();
            t.keys.push(k);
            t.vals.push(v);
          }
          t.keys.reverse();
          t.vals.reverse();
          Result::Ok((t, len + n, 0))
        } else {
          let full = !leaf || self.len() == SIZE;
          if full && self.find(&chunk[chunk.len() - 1].0) == Loc::InLeft { 
            Result::Err(Dir::InLeft)
          } else if full && self.find(&chunk[0].0) == Loc::InRight { 
            Result::Err(Dir::InRight)
          } else {
            let mut t = self.clone();
            let mut len = len;
            let n = chunk.len();
            for _ in 0..n {
              let (k, v) = chunk.pop().unwrap();
              match t.find(&k) {
                Loc::Here(i) => {
                  t.keys[i] = k;
                  t.vals[i] = v;
                }, 
                Loc::NotPresent(i) =>
                  if t.len() < SIZE {
                    t.keys.insert(i, k);
                    t.vals.insert(i, v);
                    len = len + 1;
                  } else {
                    chunk.insert(0, (t.keys.pop().unwrap(), t.vals.pop().unwrap()));
                    t.keys.insert(i, k);
                    t.vals.insert(i, v);
                  },
                Loc::InLeft =>
                  if leaf && t.keys.len() < SIZE { 
                    t.keys.insert(0, k);
                    t.vals.insert(0, v);
                    len = len + 1;
                  } else {
                    chunk.insert(0, (k, v))
                  },
                Loc::InRight =>
                  if leaf && t.len() < SIZE {
                    t.keys.push(k);
                    t.vals.push(v);
                    len = len + 1;
                  } else {
                    chunk.insert(0, (k, v))
                  }
              }
            }
            if chunk.len() > 0 { 
              chunk.sort_unstable_by(|&(ref k1, _), &(ref k2, _)| k1.cmp(k2)); 
            }
            let mut i = 0;
            while i < chunk.len() && chunk[i].0 < t.keys[0] { i = i + 1; }
            Result::Ok((t, len, i))
          }
        }
      }

      // add to T, if possible. Otherwise say where in the tree the
      // element should be added. If add places the element in the middle 
      // of a full vector, then there will be overflow that must
      // be added right
      fn add(&self, k: &K, v: &V, len: usize, leaf: bool) -> Result<(Self, Option<(K,V)>, usize), Dir> {
        match self.find(k) {
          Loc::Here(i) => {
            let mut t = self.clone();
            t.keys[i] = k.clone();
            t.vals[i] = v.clone();
            Result::Ok((t, Option::None, len))
          }
          Loc::NotPresent(i) => 
            if self.len() < SIZE {
              let mut t = self.clone();
              t.keys.insert(i, k.clone());
              t.vals.insert(i, v.clone());
              Result::Ok((t, Option::None, len + 1))
            } else {
              // we need to add it here, but to do that we have
              // to take an element out, so we return that overflow element
              let mut t = self.clone();
              let overflow = (t.keys.pop().unwrap(), t.vals.pop().unwrap());
              t.keys.insert(i, k.clone());
              t.vals.insert(i, v.clone());
              Result::Ok((t, Option::Some(overflow), len))
            },
          loc @ Loc::InLeft | loc @ Loc::InRight =>
            if !leaf || self.len() == SIZE { Result::Err(loc.to_dir()) } 
            else {
              let mut t = self.clone();
              match loc {
                Loc::InLeft => {
                  t.keys.insert(0, k.clone());
                  t.vals.insert(0, v.clone());
                },
                Loc::InRight => {
                  t.keys.push(k.clone());
                  t.vals.push(v.clone());
                },
                _ => unreachable!("bug")
              };
              Result::Ok((t, Option::None, len + 1))
            }
        }
      }

      fn remove_elt_at(&self, i: usize) -> Self {
        let mut t = self.clone();
        t.keys.remove(i);
        t.vals.remove(i);
        t
      }

      fn min_max_key(&self) -> Option<(K, K)> {
        if self.len() == 0 { Option::None }
        else { Option::Some((self.keys[0].clone(), self.keys[self.len() - 1].clone())) }
      }

      fn min_elt<'a>(&'a self) -> Option<(&'a K, &'a V)> {
        if self.len() == 0 { Option::None }
        else { Option::Some((&self.keys[0], &self.vals[0])) }
      }
      
      fn max_elt<'a>(&'a self) -> Option<(&'a K, &'a V)> {
        if self.len() == 0 { Option::None }
        else { 
          let last = self.len() - 1;
          Option::Some((&self.keys[last], &self.vals[last])) 
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
      fn into_iter(self) -> Self::IntoIter { (&self.keys).into_iter().zip(&self.vals) }
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

    pub struct Iter<'a, K: 'a + Ord + Clone + Debug, V: 'a + Clone + Debug> {
      stack: Vec<(bool, &'a Node<K,V>)>,
      elts: Option<iter::Zip<slice::Iter<'a, K>, slice::Iter<'a, V>>>
    }

    impl<'a, K, V> Iterator for Iter<'a, K, V>
      where K: 'a + Ord + Clone + Debug, V: 'a + Clone + Debug
    {
      type Item = (&'a K, &'a V);
      fn next(&mut self) -> Option<Self::Item> {
        loop {
          match &mut self.elts {
            &mut Option::None => (),
            &mut Option::Some(ref mut s) => 
              match s.next() {
                Option::None => (),
                res @ Option::Some(_) => return res
              }
          };
          if self.stack.is_empty() { return None }
          self.elts = Option::None;
          let top = self.stack.len() - 1;
          let (visited, current) = self.stack[top];
          if visited {
            self.elts = Option::Some((&(*current.elts)).into_iter());
            self.stack.pop();
            match current.right {
              Tree::Empty => (),
              Tree::Node(ref n) => self.stack.push((false, n))
            };
          }
          else {
            self.stack[top].0 = true;
            match current.left {
              Tree::Empty => (),
              Tree::Node(ref n) => self.stack.push((false, n))
            }
          }
        }
      }
    }

    impl<'a, K, V> IntoIterator for &'a Tree<K, V> 
      where K: 'a + Ord + Clone + Debug, V: 'a + Clone + Debug
    {
      type Item = (&'a K, &'a V);
      type IntoIter = Iter<'a, K, V>;
      fn into_iter(self) -> Self::IntoIter {
        match self {
          &Tree::Empty => Iter { stack: Vec::new(), elts: Option::None },
          &Tree::Node(ref n) => {
            let mut stack = Vec::<(bool, &'a Node<K,V>)>::with_capacity((n.height + 2) as usize);
            stack.push((false, n));
            Iter {stack: stack, elts: Option::None}
          }
        }
      }
    }

    impl<K,V> Tree<K,V> where K: Ord + Clone + Debug, V: Clone + Debug {
      pub(crate) fn new() -> Self { Tree::Empty }

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
                Tree::create(&ln.left, &ln.elts, &Tree::create(&ln.right, elts, r))
              } else {
                match ln.right {
                  Tree::Empty => panic!("tree heights wrong"),
                  Tree::Node(ref lrn) =>
                    Tree::create(&Tree::create(&ln.left, &ln.elts, &lrn.left),
                                 &lrn.elts,
                                 &Tree::create(&lrn.right, elts, r))
                }
              }
          }
        } else if hr > hl + 1 {
          match *r {
            Tree::Empty => panic!("tree heights are wrong"),
            Tree::Node(ref rn) =>
              if rn.right.height() >= rn.left.height() {
                Tree::create(&Tree::create(l, elts, &rn.left), &rn.elts, &rn.right)
              } else {
                match rn.left {
                  Tree::Empty => panic!("tree heights are wrong"),
                  Tree::Node(ref rln) =>
                    Tree::create(&Tree::create(l, elts, &rln.left),
                                 &rln.elts,
                                 &Tree::create(&rln.right, &rn.elts, &rn.right))
                }
            }
          }
        } else {
          Tree::create(l, elts, r)
        }
      }

      fn add_chunk(&self, len: usize, chunk: &mut Vec<(K, V)>, tmp: &mut Vec<(K, V)>)
        -> (Self, usize) 
      {
        match self {
          &Tree::Empty =>
            if chunk.len() == 0 { (Tree::Empty, len) }
            else {
              let (elts, len, _) = Elts::empty().add_chunk(chunk, len, true).unwrap();
              (Tree::create(&Tree::Empty, &$pinit(elts), &Tree::Empty), len)
            },
          &Tree::Node(ref tn) => {
            let leaf = 
              match (&tn.left, &tn.right) {
                (&Tree::Empty, &Tree::Empty) => true,
                (_, _) => false
              };
            match tn.elts.add_chunk(chunk, len, leaf) {
              Result::Ok((elts, len, split)) =>
                if chunk.len() == 0 {
                  (Tree::create(&tn.left, &$pinit(elts), &tn.right), len)
                } else {
                  let n = chunk.len() - split;
                  for _ in 0..n { tmp.push(chunk.pop().unwrap()); }
                  let (l, len) = tn.left.add_chunk(len, chunk, tmp);
                  for _ in 0..n { chunk.push(tmp.pop().unwrap()) };
                  (Tree::bal(&l, &$pinit(elts), &tn.right), len)
                },
              Result::Err(Dir::InLeft) => {
                let (l, len) = tn.left.add_chunk(len, chunk, tmp);
                (Tree::bal(&l, &tn.elts, &tn.right), len)
              },
              Result::Err(Dir::InRight) => {
                let (r, len) = tn.right.add_chunk(len, chunk, tmp);
                (Tree::bal(&tn.left, &tn.elts, &r), len)
              }
            }
          }
        }
      }

      pub(crate) fn add_sorted(&self, len: usize, elts: &[(&K, &V)]) -> (Self, usize) {
        let mut t = (self.clone(), len);
        let mut chunk = Vec::<(K, V)>::new();
        let mut tmp = Vec::<(K, V)>::new();
        let mut i = 0;
        while i < elts.len() || chunk.len() > 0 {
          if i < elts.len() && chunk.len() < SIZE {
            chunk.push((elts[i].0.clone(), elts[i].1.clone()));
            i = i + 1;
          } else {
            chunk.sort_unstable_by(|&(ref k0, _), &(ref k1, _)| k0.cmp(k1));
            chunk.dedup_by(|&mut (ref k0, _), &mut (ref k1, _)| k0 == k1);
            while chunk.len() > 0 { t = t.0.add_chunk(t.1, &mut chunk, &mut tmp); }
            assert_eq!(tmp.len(), 0)
          }
        }
        t
      }

      pub(crate) fn add(&self, len: usize, k: &K, v: &V) -> (Self, usize) {
        match self {
          &Tree::Empty => 
            (Tree::create(&Tree::Empty, &$pinit(Elts::singleton(k, v)), &Tree::Empty), len + 1),
          &Tree::Node(ref tn) => {
            let leaf = 
              match (&tn.left, &tn.right) {
                (&Tree::Empty, &Tree::Empty) => true,
                (_, _) => false
              };
            match tn.elts.add(k, v, len, leaf) {
              Result::Ok((elts, Option::None, len)) => 
                (Tree::create(&tn.left, &$pinit(elts), &tn.right), len),
              Result::Ok((elts, Option::Some((ovk, ovv)), len)) => {
                let (r, len) = tn.right.add(len, &ovk, &ovv);
                (Tree::bal(&tn.left, &$pinit(elts), &r), len)
              }
              Result::Err(Dir::InLeft) => {
                let (l, len) = tn.left.add(len, k, v);
                (Tree::bal(&l, &tn.elts, &tn.right), len)
              }
              Result::Err(Dir::InRight) => {
                let (r, len) = tn.right.add(len, k, v);
                (Tree::bal(&tn.left, &tn.elts, &r), len)
              }
            }
          }
        }
      }

      fn min_elts<'a>(&'a self) -> Option<&'a $ptyp<Elts<K,V>>> {
        match self {
          &Tree::Empty => Option::None,
          &Tree::Node(ref tn) => 
            match tn.left {
              Tree::Empty => Option::Some(&tn.elts),
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

      pub(crate) fn remove<Q: Sized + Ord>(&self, len: usize, k: &Q) -> (Self, usize) 
        where K: Borrow<Q>
      {
        match self {
          &Tree::Empty => (Tree::Empty, len),
          &Tree::Node(ref tn) =>
            match tn.elts.find(k) {
              Loc::NotPresent(_) => 
                (Tree::create(&tn.left, &tn.elts, &tn.right), len),
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

      pub(crate) fn find<'a, Q: Sized + Ord + Debug>(&'a self, k: &Q) -> Option<&'a V> 
        where K: Borrow<Q>
      {
        match self {
          &Tree::Empty => Option::None,
          &Tree::Node(ref tn) =>
            match (k.cmp(tn.min_key.borrow()), k.cmp(tn.max_key.borrow())) {
              (Ordering::Less, _) => tn.left.find(k),
              (_, Ordering::Greater) => tn.right.find(k),
              (_, _) =>
                match tn.elts.find_noedge(k) {
                  Loc::Here(i) => Option::Some(&tn.elts.vals[i]),
                  Loc::NotPresent(_) => Option::None,
                  Loc::InLeft => unreachable!("bug"),
                  Loc::InRight => unreachable!("bug")
                }
            }
        }
      }

      #[allow(dead_code)]
      pub(crate) fn invariant(&self, len: usize) -> () {
        fn in_range<K,V>(lower: Option<&K>, upper: Option<&K>, elts: &Elts<K,V>) 
          -> bool
          where K: Ord + Clone + Debug, V: Clone + Debug
        {
          (match lower {
            Option::None => true,
            Option::Some(lower) =>
              (&elts.keys).into_iter().all(|k| lower.cmp(k) == Ordering::Less) })
            && (match upper {
              Option::None => true,
              Option::Some(upper) =>
                (&elts.keys).into_iter().all(|k| upper.cmp(k) == Ordering::Greater) })
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

        fn check<K,V>(t: &Tree<K,V>, lower: Option<&K>, upper: Option<&K>, len: usize) 
          -> (u16, usize)
          where K: Ord + Clone + Debug, V: Clone + Debug
        {
          match *t {
            Tree::Empty => (0, len),
            Tree::Node(ref tn) => {
              if !in_range(lower, upper, &tn.elts) { 
                panic!("tree invariant violated lower {:?} upper {:?} elts {:?}, tree {:?}", 
                  lower, upper, &tn.elts, t)
              };
              if !sorted(&tn.elts) { panic!("elements isn't sorted") };
              let (thl, len) = 
                check(&tn.left, lower, tn.elts.min_elt().map(|(k, _)| k), len);
              let (thr, len) = 
                check(&tn.right, tn.elts.max_elt().map(|(k, _)| k), upper, len);
              let th = 1 + max(thl, thr);
              let (hl, hr) = (tn.left.height(), tn.right.height());
              let ub = max(hl, hr) - min(hl, hr);
              if thl != hl { panic!("left node height is wrong") };
              if thr != hr { panic!("right node height is wrong") };
              let h = t.height();
              if th != h { panic!("node height is wrong {} vs {}", th, h) };
              if ub > 2 { panic!("tree is unbalanced {:?} tree: {:?}", ub, t) };
              (th, len + tn.elts.len())
            }
          }
        }

        //println!("{:?}", self);
        let (_height, tlen) = check(self, Option::None, Option::None, 0);
        if len != tlen { panic!("len is wrong {} vs {}", len, tlen) }
      }
    }
  };
}
