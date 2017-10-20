extern crate arrayvec;
use std::rc::Rc;
use std::cmp::{Ordering, max, min};
use std::fmt::Debug;
use self::arrayvec::ArrayVec;

pub enum Loc {
  InRight,
  InLeft,
  NotPresent(usize), // the index in the array where the element would be if it was present
  Here(usize) // the index in the array where the equal element is
}


/* 
   elts is a sorted sparse array of pairs, increasing the SIZE has several effects; 
   -- decreases the height of the tree for a given number of elements, decreasing the amount of 
      indirection necessary to get to any given key. 
   -- decreases the number of objects allocated on the heap each time a key is added or removed
   -- increases the size of each allocation
   -- icreases the overall amount of memory allocated for each change to the tree
*/
pub const SIZE: usize = 8;

#[derive(Clone, Debug)]
struct Elts<K: Ord + Clone + Debug, V: Clone + Debug>(pub ArrayVec<[(K, V); SIZE]>);

impl<K,V> Elts<K,V> where K: Ord + Clone + Debug, V: Clone + Debug {
  fn singleton(k: &K, v: &V) -> Self {
    let mut t = ArrayVec::<[(K,V); SIZE]>::new();
    t.push((k.clone(), v.clone()));
    Elts(t)
  }

  // This is faster than binary search because processors are really good
  // at scanning lineraly through contiguous memory. Since SIZE is a constant
  // the algorithm is still log(N), we're just playing with constants.
  fn find(&self, k: &K) -> Loc {
    let len = self.0.len();
    match k.cmp(&self.0[len - 1].0) {
      Ordering::Greater => Loc::InRight,
      Ordering::Equal => Loc::Here(len - 1),
      Ordering::Less => {
        for i in 0..(len - 1) {
          match k.cmp(&self.0[i].0) {
            Ordering::Equal => return Loc::Here(i),
            Ordering::Greater => (),
            Ordering::Less =>
              if i == 0 { return Loc::InLeft }
              else { return Loc::NotPresent(i) }
          }
        }
        panic!("already checked the last element!")
      }
    }
  }

  fn ordering(k0: &(K, V), k1: &(K, V)) -> Ordering { k0.0.cmp(&k1.0) }

  // add to T, if possible. Otherwise say where in the tree the
  // element should be added. If add places the element in the middle 
  // of a full vector, then there will be overflow that must
  // be added right
  fn add(&self, k: &K, v: &V, len: usize) -> Result<(Self, Option<(K,V)>, usize), Loc> {
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
        if self.0.len() == SIZE { Result::Err(loc) } 
        else {
          let mut t = self.clone();
          match loc {
            Loc::InLeft => t.0.insert(0, (k.clone(), v.clone())),
            Loc::InRight => t.0.push((k.clone(), v.clone())),
            _ => panic!("impossible")
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

#[derive(Clone, Debug)]
pub(crate) struct Node<K: Ord + Clone + Debug, V: Clone + Debug> {
  elts: Elts<K, V>,
  left: Tree<K, V>,
  right: Tree<K, V>,
  height: u16
}

#[derive(Clone, Debug)]
pub(crate) enum Tree<K: Ord + Clone + Debug, V: Clone + Debug> {
  Empty,
  Node(Rc<Node<K,V>>)
}

impl<K,V> Tree<K,V> where K: Ord + Clone + Debug, V: Clone + Debug {
  pub(crate) fn new() -> Self { Tree::Empty }

  fn height(&self) -> u16 {
    match self {
      &Tree::Empty => 0,
      &Tree::Node(ref n) => n.height
    }
  }

  fn create(l: &Tree<K, V>, elts: &Elts<K, V>, r: &Tree<K, V>) -> Self {
    let n = 
      Node { elts: elts.clone(), 
            left: l.clone(), right: r.clone(), 
            height: 1 + max(l.height(), r.height()) };
    Tree::Node(Rc::new(n))
  }

  fn bal(l: &Tree<K, V>, elts: &Elts<K, V>, r: &Tree<K, V>) -> Self {
    let (hl, hr) = (l.height(), r.height());
    if hl > hr + 2 {
      match *l {
        Tree::Empty => panic!("tree heights wrong"),
        Tree::Node(ref ln) =>
          if ln.left.height() >= ln.right.height() {
            Tree::create(&ln.left, &ln.elts, &Tree::create(&ln.right, &elts, r))
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
    } else if hr > hl + 2 {
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

  pub(crate) fn add(&self, len: usize, k: &K, v: &V) -> (Self, usize) {
    match self {
      &Tree::Empty => 
        (Tree::create(&Tree::Empty, &Elts::singleton(k, v), &Tree::Empty), len + 1),
      &Tree::Node(ref tn) =>
        match tn.elts.add(k, v, len) {
          Result::Ok((elts, Option::None, len)) => 
            (Tree::create(&tn.left, &elts, &tn.right), len),
          Result::Ok((elts, Option::Some((ovk, ovv)), len)) => {
            let (r, len) = tn.right.add(len, &ovk, &ovv);
            (Tree::bal(&tn.left, &elts, &r), len)
          }
          Result::Err(Loc::NotPresent(_)) => panic!("add failed but key not present"),
          Result::Err(Loc::Here(_)) => panic!("add failed but key is here"),
          Result::Err(Loc::InLeft) => {
            let (l, len) = tn.left.add(len, k, v);
            (Tree::bal(&l, &tn.elts, &tn.right), len)
          }
          Result::Err(Loc::InRight) => {
            let (r, len) = tn.right.add(len, k, v);
            (Tree::bal(&tn.left, &tn.elts, &r), len)
          }
        }
    }
  }

  fn min_elts<'a>(&'a self) -> Option<&'a Elts<K,V>> {
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

  pub(crate) fn remove(&self, len: usize, k: &K) -> (Self, usize) {
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
              (Tree::create(&tn.left, &elts, &tn.right), len)
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

  pub(crate) fn find<'a>(&'a self, k: &K) -> Option<&'a V> {
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
            panic!("tree invariant violated lower {:?} upper {:?} elts {:?}", 
              lower, upper, &tn.elts)
          };
          if !sorted(&tn.elts) { panic!("elements isn't sorted") };
          let (thl, len) = 
            check(&tn.left, lower, tn.elts.max_elt().map(|&(ref k, _)| k), len);
          let (thr, len) = 
            check(&tn.right, tn.elts.min_elt().map(|&(ref k, _)| k), upper, len);
          let th = 1 + max(thl, thr);
          let (hl, hr) = (tn.left.height(), tn.right.height());
          if max(hl, hr) - min(hl, hr) > 2 { panic!("tree is unbalanced") };
          if thl != hl { panic!("left node height is wrong") };
          if thr != hr { panic!("right node height is wrong") };
          let h = t.height();
          if th != h { panic!("node height is wrong {} vs {}", th, h) };
          (th, len + tn.elts.0.len())
        }
      }
    }

    //println!("{:?}", t);
    let (_height, tlen) = check(self, Option::None, Option::None, 0);
    if len != tlen { panic!("len is wrong {} vs {}", len, tlen) }
  }
}