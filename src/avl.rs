use std::rc::Rc;
use std::cmp::{Ordering, max, min};
use std::fmt::Debug;

/* 
   elts is a sorted sparse array of pairs, increasing the size has several effects; 
   -- decreases the height of the tree for a given number of elements, decreasing the amount of 
      indirection necessary to get to any given key. 
   -- decreases the number of objects allocated on the heap each time a key is added or removed
   -- increases the size of each allocation
   -- icreases the overall amount of memory allocated for each change to the tree

   holes are not allowed; the None elements are always at the end.
*/
mod elts {
  extern crate arrayvec;
  use std::cmp::{Ordering};
  use std::fmt::Debug;
  use self::arrayvec::ArrayVec;

  pub(crate) const SIZE: usize = 8;

  #[derive(Clone, Debug)]
  pub(crate) struct T<K: Ord + Clone + Debug, V: Clone + Debug>(pub ArrayVec<[(K, V); SIZE]>);

  pub(super) fn singleton<K, V>(k: &K, v: &V) -> T<K,V>
    where K: Ord + Clone + Debug, V: Clone + Debug
  {
    let mut t = ArrayVec::<[(K,V); SIZE]>::new();
    t.push((k.clone(), v.clone()));
    T(t)
  }

  pub(super) enum Loc {
    InRight,
    InLeft,
    NotPresent(usize), // the index in the array where the element would be if it was present
    Here(usize) // the index in the array where the equal element is
  }

  /*
  pub(super) fn find<K, V>(t: &T<K,V>, k: &K) -> Loc 
    where K: Ord + Clone + Debug, V: Clone + Debug
  {
    match t.0.binary_search_by(|&(ref tk, _)| tk.cmp(k)) {
      Result::Ok(i) => Loc::Here(i),
      Result::Err(i) =>
        if i == 0 { Loc::InLeft }
        else if i >= t.0.len() { Loc::InRight }
        else { Loc::NotPresent(i) }
    }
  }
  */

  pub(super) fn find<K, V>(t: &T<K,V>, k: &K) -> Loc 
    where K: Ord + Clone + Debug, V: Clone + Debug
  {
    for i in 0..t.0.len() {
      match k.cmp(&t.0[i].0) {
        Ordering::Equal => return Loc::Here(i),
        Ordering::Greater => (),
        Ordering::Less =>
          if i == 0 { return Loc::InLeft }
          else { return Loc::NotPresent(i) }
      }
    }
    Loc::InRight
  }

  pub(super) fn ordering<K,V>(k0: &(K, V), k1: &(K, V)) -> Ordering
    where K: Ord + Clone + Debug, V: Clone + Debug
  { k0.0.cmp(&k1.0) }

  // add to T, if possible. Otherwise say where in the tree the
  // element should be added. Possibly if add places the element in
  // the middle of a full vector, then there will be overflow that must
  // be added right
  pub(super) fn add<K,V>(t: &T<K,V>, k: &K, v: &V, len: usize) 
     -> Result<(T<K,V>, Option<(K,V)>, usize), Loc>
    where K: Ord + Clone + Debug, V: Clone + Debug
  {
    match find(t, k) {
      Loc::Here(i) => {
        let mut t = t.clone();
        t.0[i] = (k.clone(), v.clone());
        Result::Ok((t, Option::None, len))
      }
      Loc::NotPresent(i) => 
        if t.0.len() < SIZE {
          let mut t = t.clone();
          t.0.insert(i, (k.clone(), v.clone()));
          Result::Ok((t, Option::None, len + 1))
        } else {
          // we need to add it here, but to do that we have
          // to take an element out, so we return that
          let mut t = t.clone();
          let overflow = t.0.pop().unwrap().clone();
          t.0.insert(i, (k.clone(), v.clone()));
          Result::Ok((t, Option::Some(overflow), len))
        },
      loc @ Loc::InLeft | loc @ Loc::InRight =>
        if t.0.len() == SIZE { Result::Err(loc) } 
        else {
          let mut t = t.clone();
          match loc {
            Loc::InLeft => t.0.insert(0, (k.clone(), v.clone())),
            Loc::InRight => t.0.push((k.clone(), v.clone())),
            _ => panic!("impossible")
          };
          Result::Ok((t, Option::None, len + 1))
        }
    }
  }

  pub(super) fn remove_elt_at<K,V>(t: &T<K,V>, i: usize) -> T<K,V> 
    where K: Ord + Clone + Debug, V: Clone + Debug
  {
    let mut t = t.clone();
    t.0.pop_at(i);
    t
  }

  pub(super) fn min_elt<'a,K,V>(t: &'a T<K,V>) -> Option<&'a (K,V)> 
    where K: Ord + Clone + Debug, V: Clone + Debug
  { t.0.first() }
  pub(super) fn max_elt<'a,K,V>(t: &'a T<K,V>) -> Option<&'a (K,V)> 
    where K: Ord + Clone + Debug, V: Clone + Debug
  { t.0.last() }
}

#[derive(Clone, Debug)]
pub(crate) struct Node<K: Ord + Clone + Debug, V: Clone + Debug> {
  elts: elts::T<K, V>,
  left: Tree<K, V>,
  right: Tree<K, V>,
  height: u16
}

#[derive(Clone, Debug)]
pub(crate) enum Tree<K: Ord + Clone + Debug, V: Clone + Debug> {
  Empty,
  Node(Rc<Node<K,V>>)
}

pub(crate) fn empty<K, V>() -> Tree<K, V> 
  where K: Ord + Clone + Debug, V: Clone + Debug
{ Tree::Empty }

fn height<K,V>(t: &Tree<K,V>) -> u16
  where K: Ord + Clone + Debug, V: Clone + Debug
{
  match *t {
    Tree::Empty => 0,
    Tree::Node(ref n) => n.height
  }
}

fn create<K, V>(l: &Tree<K, V>, elts: &elts::T<K, V>, r: &Tree<K, V>) -> Tree<K, V>
  where K: Ord + Clone + Debug, V: Clone + Debug
{
  let n = 
    Node { elts: elts.clone(), 
           left: l.clone(), right: r.clone(), 
           height: 1 + max(height(l), height(r)) };
  Tree::Node(Rc::new(n))
}

fn bal<K, V>(l: &Tree<K, V>, elts: &elts::T<K, V>, r: &Tree<K, V>) -> Tree<K, V>
  where K: Ord + Clone + Debug, V: Clone + Debug
{
  let (hl, hr) = (height(l), height(r));
  if hl > hr + 2 {
    match *l {
      Tree::Empty => panic!("tree heights wrong"),
      Tree::Node(ref ln) =>
        if height(&ln.left) >= height(&ln.right) {
          create(&ln.left, &ln.elts, &create(&ln.right, &elts, r))
        } else {
          match ln.right {
            Tree::Empty => panic!("tree heights wrong"),
            Tree::Node(ref lrn) =>
              create(&create(&ln.left, &ln.elts, &lrn.left),
                     &lrn.elts,
                     &create(&lrn.right, elts, r))
          }
        }
    }
  } else if hr > hl + 2 {
    match *r {
      Tree::Empty => panic!("tree heights are wrong"),
      Tree::Node(ref rn) =>
        if height(&rn.right) >= height(&rn.left) {
          create(&create(l, elts, &rn.left), &rn.elts, &rn.right)
        } else {
          match rn.left {
            Tree::Empty => panic!("tree heights are wrong"),
            Tree::Node(ref rln) =>
              create(&create(l, elts, &rln.left),
                     &rln.elts,
                     &create(&rln.right, &rn.elts, &rn.right))
          }
      }
    }
  } else {
    create(l, elts, r)
  }
}

pub(crate) fn add<K, V>(t: &Tree<K, V>, len: usize, k: &K, v: &V) -> (Tree<K, V>, usize)
  where K: Ord + Clone + Debug, V: Clone + Debug
{
  match *t {
    Tree::Empty => (create(&Tree::Empty, &elts::singleton(k, v), &Tree::Empty), len + 1),
    Tree::Node(ref tn) =>
      match elts::add(&tn.elts, k, v, len) {
        Result::Ok((elts, Option::None, len)) => 
          (create(&tn.left, &elts, &tn.right), len),
        Result::Ok((elts, Option::Some((ovk, ovv)), len)) => {
          let (r, len) = add(&tn.right, len, &ovk, &ovv);
          (bal(&tn.left, &elts, &r), len)
        }
        Result::Err(elts::Loc::NotPresent(_)) => panic!("add failed but key not present"),
        Result::Err(elts::Loc::Here(_)) => panic!("add failed but key is here"),
        Result::Err(elts::Loc::InLeft) => {
          let (l, len) = add(&tn.left, len, k, v);
          (bal(&l, &tn.elts, &tn.right), len)
        }
        Result::Err(elts::Loc::InRight) => {
          let (r, len) = add(&tn.right, len, k, v);
          (bal(&tn.left, &tn.elts, &r), len)
        }
      }
  }
}

pub(crate) fn min_elts<'a, K, V>(t: &'a Tree<K, V>) -> Option<&'a elts::T<K,V>>
  where K: Ord + Clone + Debug, V: Clone + Debug
{
  match *t {
    Tree::Empty => Option::None,
    Tree::Node(ref tn) => 
      match tn.left {
        Tree::Empty => Option::Some(&tn.elts),
        Tree::Node(_) => min_elts(&tn.left)
      }
  }
}

fn remove_min_elts<K, V>(t: &Tree<K,V>) -> Tree<K,V>
  where K: Ord + Clone + Debug, V: Clone + Debug
{
  match *t {
    Tree::Empty => panic!("remove min elt"),
    Tree::Node(ref tn) =>
      match tn.left {
        Tree::Empty => tn.right.clone(),
        Tree::Node(_) => bal(&remove_min_elts(&tn.left), &tn.elts, &tn.right)
      }
  }
}

fn concat<K, V>(l: &Tree<K, V>, r: &Tree<K, V>) -> Tree<K, V>
  where K: Ord + Clone + Debug, V: Clone + Debug
{
  match (l, r) {
    (&Tree::Empty, _) => r.clone(),
    (_, &Tree::Empty) => l.clone(),
    (_, _) => {
      let elts = min_elts(r).unwrap();
      bal(l, elts, &remove_min_elts(r))
    }
  }
}

pub(crate) fn remove<K, V>(t: &Tree<K,V>, len: usize, k: &K) -> (Tree<K,V>, usize)
  where K: Ord + Clone + Debug, V: Clone + Debug
{
  match *t {
    Tree::Empty => (Tree::Empty, len),
    Tree::Node(ref tn) =>
      match elts::find(&tn.elts, k) {
        elts::Loc::NotPresent(_) => (create(&tn.left, &tn.elts, &tn.right), len),
        elts::Loc::Here(i) => {
          let elts = elts::remove_elt_at(&tn.elts, i);
          let len = len - 1;
          if elts.0.len() == 0 {
            (concat(&tn.left, &tn.right), len)
          } else {
            (create(&tn.left, &elts, &tn.right), len)
          }
        }
        elts::Loc::InLeft => {
          let (l, len) = remove(&tn.left, len, k);
          (bal(&l, &tn.elts, &tn.right), len)
        }
        elts::Loc::InRight => {
          let (r, len) = remove(&tn.right, len, k);
          (bal(&tn.left, &tn.elts, &r), len)
        }
      }
  }
}

pub(crate) fn find<'a, K, V>(t: &'a Tree<K, V>, k: &K) -> Option<&'a V>
  where K: Ord + Clone + Debug, V: Clone + Debug
{
  match *t {
    Tree::Empty => Option::None,
    Tree::Node(ref tn) =>
      match elts::find(&tn.elts, k) {
        elts::Loc::Here(i) => Option::Some(&tn.elts.0[i].1),
        elts::Loc::NotPresent(_) => Option::None,
        elts::Loc::InLeft => find(&tn.left, k),
        elts::Loc::InRight => find(&tn.right, k)
      }
  }
}

#[allow(dead_code)]
pub(crate) fn invariant<K,V>(t: &Tree<K,V>, len: usize) -> ()
  where K: Ord + Clone + Debug, V: Clone + Debug
{
  fn in_range<K, V>(lower: Option<&K>, upper: Option<&K>, elts: &elts::T<K,V>) -> bool
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

  fn sorted<K, V>(elts: &elts::T<K,V>) -> bool 
    where K: Ord + Clone + Debug, V: Clone + Debug
  {
    if elts.0.len() < 2 { true }
    else {
      for i in 0..(elts.0.len() - 1) {
        match elts::ordering(&elts.0[i], &elts.0[i + 1]) {
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
          check(&tn.left, lower, elts::max_elt(&tn.elts).map(|&(ref k, _)| k), len);
        let (thr, len) = 
          check(&tn.right, elts::min_elt(&tn.elts).map(|&(ref k, _)| k), upper, len);
        let th = 1 + max(thl, thr);
        let (hl, hr) = (height(&tn.left), height(&tn.right));
        if max(hl, hr) - min(hl, hr) > 2 { panic!("tree is unbalanced") };
        if thl != hl { panic!("left node height is wrong") };
        if thr != hr { panic!("right node height is wrong") };
        let h = height(t);
        if th != h { panic!("node height is wrong {} vs {}", th, h) };
        (th, len + tn.elts.0.len())
      }
    }
  }

  //println!("{:?}", t);
  let (_height, tlen) = check(t, Option::None, Option::None, 0);
  if len != tlen { panic!("len is wrong {} vs {}", len, tlen) }
}