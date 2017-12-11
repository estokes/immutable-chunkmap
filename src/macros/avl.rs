macro_rules! avltree {
  ($pimport:path, $ptyp:ident, $pinit:path, $chunksize:expr) => {
    extern crate arrayvec;
    use $pimport;
    use std::cmp::{Ord, Ordering, max, min};
    use std::fmt::Debug;
    use std::borrow::Borrow;
    use std::slice;
    use self::arrayvec::ArrayVec;

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
    struct Elts<K: Ord + Clone + Debug, V: Clone + Debug>(pub ArrayVec<[(K, V); SIZE]>);

    impl<K,V> Elts<K,V> where K: Ord + Clone + Debug, V: Clone + Debug {
      fn singleton(k: &K, v: &V) -> Self {
        let mut t = ArrayVec::<[(K,V); SIZE]>::new();
        t.push((k.clone(), v.clone()));
        Elts(t)
      }

      fn empty() -> Self { Elts(ArrayVec::<[(K,V); SIZE]>::new()) }

      #[allow(dead_code)]
      fn is_empty(&self) -> bool { self.0.len() == 0 }

      #[allow(dead_code)]
      fn is_full(&self) -> bool { self.0.len() == SIZE }

      fn find<Q: ?Sized + Ord>(&self, k: &Q) -> Loc where K: Borrow<Q> {
        let len = self.0.len();
        if len == 0 { Loc::NotPresent(0) } 
        else {
          let first = k.cmp(&self.0[0].0.borrow());
          let last = k.cmp(&self.0[len - 1].0.borrow());
          match (first, last) {
            (Ordering::Equal, _) => Loc::Here(0),
            (_, Ordering::Equal) => Loc::Here(len - 1),
            (Ordering::Less, _) => Loc::InLeft,
            (_, Ordering::Greater) => Loc::InRight,
            (_, _) =>
              match self.0.binary_search_by(|&(ref k1, _)| k1.borrow().cmp(k)) {
                Result::Ok(i) => Loc::Here(i),
                Result::Err(i) => Loc::NotPresent(i)
              }
          }
        }
      }

      fn ordering(k0: &(K, V), k1: &(K, V)) -> Ordering { k0.0.cmp(&k1.0) }

      // chunk must be sorted
      #[allow(dead_code)]
      fn add_chunk(&self, chunk: &mut ArrayVec<[(K, V); SIZE]>, len: usize, leaf: bool) 
        -> Result<(Self, usize), Dir>
      {
        if chunk.len() == 0 { Result::Ok((self.clone(), len)) }
        else if self.0.len() == 0 {
          let mut t = self.clone();
          let n = chunk.len();
          for _ in 0..n { t.0.push(chunk.pop().unwrap()); }
          Result::Ok((t, len + n))
        } else {
          let full = !leaf || self.0.len() == SIZE;
          if full && self.find(&chunk[chunk.len() - 1].0) == Loc::InLeft { 
            Result::Err(Dir::InLeft) 
          } else if full && self.find(&chunk[0].0) == Loc::InRight { 
            Result::Err(Dir::InRight) 
          } else {
            let mut t = self.clone();
            let mut len = len;
            let n = chunk.len();
            for _ in 0..n {
              let kv = chunk.pop().unwrap();
              match t.find(&kv.0) {
                Loc::Here(i) => t.0[i] = kv,
                Loc::NotPresent(i) =>
                  if t.0.len() < SIZE {
                    t.0.insert(i, kv);
                    len = len + 1;
                  } else {
                    chunk.insert(0, t.0.pop().unwrap());
                    t.0.insert(i, kv)
                  },
                Loc::InLeft =>
                  if t.0.len() < SIZE { 
                    t.0.insert(0, kv);
                    len = len + 1;
                  } else {
                    chunk.insert(0, kv)
                  },
                Loc::InRight =>
                  if t.0.len() < SIZE {
                    t.0.push(kv);
                    len = len + 1;
                  } else {
                    chunk.insert(0, kv)
                  }
              }
            }
            if chunk.len() > 0 { 
              chunk.sort_unstable_by(|&(ref k1, _), &(ref k2, _)| k1.cmp(k2)); 
            }
            Result::Ok((t, len))
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
            t.0[i] = (k.clone(), v.clone());
            Result::Ok((t, Option::None, len))
          }
          Loc::NotPresent(i) => 
            if self.0.len() < SIZE {
              let mut t = self.clone();
              t.0.insert(i, (k.clone(), v.clone()));
              Result::Ok((t, Option::None, len + 1))
            } else {
              // we need to add it here, but to do that we have
              // to take an element out, so we return that overflow element
              let mut t = self.clone();
              let overflow = t.0.pop().unwrap().clone();
              t.0.insert(i, (k.clone(), v.clone()));
              Result::Ok((t, Option::Some(overflow), len))
            },
          loc @ Loc::InLeft | loc @ Loc::InRight =>
            if !leaf || self.0.len() == SIZE { Result::Err(loc.to_dir()) } 
            else {
              let mut t = self.clone();
              match loc {
                Loc::InLeft => t.0.insert(0, (k.clone(), v.clone())),
                Loc::InRight => t.0.push((k.clone(), v.clone())),
                _ => unreachable!("bug")
              };
              Result::Ok((t, Option::None, len + 1))
            }
        }
      }

      fn remove_elt_at(&self, i: usize) -> Self {
        let mut t = self.clone();
        t.0.pop_at(i);
        t
      }

      fn min_elt<'a>(&'a self) -> Option<&'a (K,V)> { self.0.first() }
      fn max_elt<'a>(&'a self) -> Option<&'a (K,V)> { self.0.last() }
    }

    impl<K, V> IntoIterator for Elts<K, V> 
      where K: Ord + Clone + Debug, V: Clone + Debug 
    {
      type Item = (K, V);
      type IntoIter = arrayvec::IntoIter<[(K, V); SIZE]>;
      fn into_iter(self) -> Self::IntoIter { self.0.into_iter() }
    }

    impl<'a, K, V> IntoIterator for &'a Elts<K, V>
      where K: 'a + Ord + Clone + Debug, V: 'a + Clone + Debug
    {
      type Item = &'a (K, V);
      type IntoIter = slice::Iter<'a, (K, V)>;
      fn into_iter(self) -> Self::IntoIter { (&self.0).into_iter() }
    }

    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub(crate) struct Node<K: Ord + Clone + Debug, V: Clone + Debug> {
      elts: $ptyp<Elts<K, V>>,
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
      elts: Option<slice::Iter<'a, (K, V)>>
    }

    impl<'a, K, V> Iterator for Iter<'a, K, V>
      where K: 'a + Ord + Clone + Debug, V: 'a + Clone + Debug
    {
      type Item = &'a (K, V);
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
      type Item = &'a (K, V);
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
        let n = 
          Node { elts: elts.clone(), 
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

      fn add_chunk(&self, len: usize, chunk: &mut ArrayVec<[(K, V); SIZE]>)
        -> (Self, usize) 
      {
        match self {
          &Tree::Empty => {
            let (elts, len) = Elts::empty().add_chunk(chunk, len).unwrap();
            (Tree::create(&Tree::Empty, &$pinit(elts), &Tree::Empty), len)
          },
          &Tree::Node(ref tn) => {
            let leaf = 
              match (&tn.left, &tn.right) {
                (&Tree::Empty, &Tree::Empty) => true,
                (_, _) => false
              };
            match tn.elts.add_chunk(chunk, len, leaf) {
              Result::Ok((elts, len)) =>
                (Tree::create(&tn.left, &$pinit(elts), &tn.right), len),
              Result::Err(Dir::InLeft) => {
                let (l, len) = tn.left.add_chunk(len, chunk);
                (Tree::bal(&l, &tn.elts, &tn.right), len)
              },
              Result::Err(Dir::InRight) => {
                let (r, len) = tn.right.add_chunk(len, chunk);
                (Tree::bal(&tn.left, &tn.elts, &r), len)
              }
            }
          }
        }
      }

      pub(crate) fn add_multi(&self, len: usize, elts: &[(&K, &V)]) -> (Self, usize) {
        let mut t = (self.clone(), len);
        let mut chunk = ArrayVec<[(K, V); SIZE]>::new();
        let mut i = 0;
        while i < elts.len() || chunk.len() > 0 {
          if i < elts.len() && chunk.len() < SIZE {
            chunk.push((elts[i].0.clone(), elts[i].1.clone()));
            i = i + 1;
          } else {
            chunk.sort_unstable_by(|&(ref k0, _), &(ref k1, _)| k0.cmp(k1));
            while chunk.len() > 0 { t = t.0.add_chunk(t.1, chunk); }
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

      pub(crate) fn remove<Q: ?Sized + Ord>(&self, len: usize, k: &Q) -> (Self, usize) 
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
                if elts.0.len() == 0 {
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

      pub(crate) fn find<'a, Q: ?Sized + Ord>(&'a self, k: &Q) -> Option<&'a V> 
        where K: Borrow<Q>
      {
        match self {
          &Tree::Empty => Option::None,
          &Tree::Node(ref tn) =>
            match tn.elts.find(k) {
              Loc::Here(i) => Option::Some(&tn.elts.0[i].1),
              Loc::NotPresent(_) => Option::None,
              Loc::InLeft => tn.left.find(k),
              Loc::InRight => tn.right.find(k)
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
              (&elts.0).into_iter().all(|&(ref k, _)| lower.cmp(k) == Ordering::Less) })
            && (match upper {
              Option::None => true,
              Option::Some(upper) =>
                (&elts.0).into_iter().all(|&(ref k, _)| upper.cmp(k) == Ordering::Greater) })
        }

        fn sorted<K,V>(elts: &Elts<K,V>) -> bool 
          where K: Ord + Clone + Debug, V: Clone + Debug
        {
          if elts.0.len() < 2 { true }
          else {
            for i in 0..(elts.0.len() - 1) {
              match Elts::ordering(&elts.0[i], &elts.0[i + 1]) {
                Ordering::Greater => return false,
                Ordering::Less | Ordering::Equal => ()
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
                check(&tn.left, lower, tn.elts.min_elt().map(|&(ref k, _)| k), len);
              let (thr, len) = 
                check(&tn.right, tn.elts.max_elt().map(|&(ref k, _)| k), upper, len);
              let th = 1 + max(thl, thr);
              let (hl, hr) = (tn.left.height(), tn.right.height());
              let ub = max(hl, hr) - min(hl, hr);
              if thl != hl { panic!("left node height is wrong") };
              if thr != hr { panic!("right node height is wrong") };
              let h = t.height();
              if th != h { panic!("node height is wrong {} vs {}", th, h) };
              if ub > 2 { panic!("tree is unbalanced {:?} tree: {:?}", ub, t) };
              (th, len + tn.elts.0.len())
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
