use std::rc::Rc;
use std::cmp::{Ordering, max, min};

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
  const size 4;

  type t<K, V> = [Option<(K, V)>; size]

  fn singleton<K: Ord + Clone, V: Clone>(k: &K, v: &V) -> t<K,V>
  {
    let mut t = [Option::None; size];
    t[0] = Option::Some((k.clone(), v.clone()));
    t
  }

  enum Loc {
    InRight,
    InLeft,
    NotPresent,
    Here(usize) // the index in the array where the equal element is
  }

  fn find<K: Ord, V>(t: &t<K,V>, k: &K) -> Loc {
    let res =
      t.binary_search_by(|kv| {
        match *kv {
          Option::None => Ordering::Less,
          Option::Some((ref tk), _) => k.cmp(tk)
        }
      });
    match res {
      Result::Ok(i) => Loc::Here(i),
      Result::Err(i) =>
        if i == 0 { Loc::InLeft }
        else if i >= size { Loc::InRight }
        else { Loc::NotPresent }
    }
  }

  fn ordering<K: Ord,V>(k0: (&K, &V), k1: (&K, &V)) -> Ordering {
    match (k0, k1) {
      (&Option::None, &Option::Some(_)) => Ordering::Greater,
      (&Option::Some(_), &Option::None) => Ordering::Less,
      (&Option::None, &Option::None) => Ordering::Equal,
      (&Option::Some((k0, _)), &Option::Some((k1, _))) => k0.cmp(k1)
    }
  }

  fn add<K,V>(t: &t<K,V>, k: &K, v: &v, len: usize) 
     -> Option<(t<K,V>, usize)>
    where K: Ord + Clone, V: Clone
  {
    match find(t, k) {
      Loc::Here(i) => {
        let mut t = t.clone();
        t[i] = Option::Some((k.clone(), v.clone()));
        Option::Some(t, len)
      }
      Loc::NotPresent | Loc::InLeft | Loc::InRight =>
        if !has_space(&t) { Option::None } 
        else {
          let mut t = t.clone();
          t[size - 1] = Option::Some((k.clone(), v.clone()))
          t.sort_unstable_by(ordering);
          Option::Some((t, len + 1))
        }
    }
  }

  fn has_space(t: &t<_,_>) -> bool {
    match t[size - 1] {
      Option::None => true,
      Option::Some(_) => false
    }
  }

  fn is_empty(t: &t<_,_>) -> bool {
    match t[0] {
      Option::None => true,
      Option::Some(_) => false
    }
  }

  fn remove_elt_at<K,V>(t: &t<K,V>, i: usize) -> t<K,V> 
    where K: Ord + Clone, V: Clone
  {
    if i < 0 || i >= size { panic!("elts::remove_elt_at: index out of bounds") };
    let mut res = t.clone();
    res[i] = Option::None;
    res.sort_unstable_by(ordering);
    res
  }
}

#[derive (Clone)]
pub(crate) struct Node<K: Ord + Clone, V: Clone> {
  elts: elts::t<K, V>,
  left: Tree<K, V>,
  right: Tree<K, V>,
  height: u16
}

#[derive (Clone)]
pub(crate) enum Tree<K: Ord + Clone, V: Clone> {
  Empty,
  Node(Rc<Node>)
}

pub(crate) fn empty<K: Ord + Clone, V: Clone>() -> Tree<K, V> { Tree::Empty }

fn height(t: Tree<K,V>) {
  match t {
    Tree::Empty => 0,
    Tree::Node(ref n) => n.height
  }
}

fn create<K, V>(l: &Tree<K, V>, elts: &elts::t<K, V>, r: &Tree<K, V>) -> Tree<K, V>
  where K: Ord + Clone, V: Clone
{
  let n = 
    Node { elts: elts.clone(), 
           left: l.clone(), right: r.clone(), 
           height: 1 + max(height(l), height(r) };
  Tree::Node(Rc::new(n))
}

fn bal<K, V>(l: &Tree<K, V>, elts: &elts::t<K, V>, r: &Tree<K, V>) -> Tree<K, V>
  where K: Ord + Clone, V: Clone
{
  let (hl, hr) = (height(l), height(r));
  if hl > hr + 2 {
    match *l {
      Tree::Empty => panic!("tree heights wrong"),
      Tree::Node(ref ln) =>
        if height(&ln.left) >= height(&ln.right) {
          create(&ln.left, &ln.elts, &create(&ln.right, &elts, r))
        } else {
          match *l.right {
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
  where K: Ord + Clone, V: Clone
{
  match *t {
    Tree::Empty => create(&Tree::Empty, elts::singleton(k, v), &Tree::Empty),
    Tree::Node(ref tn) => {
      let res = elts::find(&t.elts, k);
      match elts::add(&t.elts, k, v, res, len) {
        Option::Some(elts, len) => create(&tn.left, &elts, &tn.right),
        Option::None => {
          match elts::localize(res) {
            Loc::NotPresent => panic!("add failed but key not present"),
            Loc::InLeft => {
              let (l, len) = add(&tn.left, len, k, v);
              (bal(&l, &tn.k, &tn.v, &tn.right), len)
            }
            Loc:InRight => {
              let (r, len) = add(&tn.right, len, k, v);
              (bal(&tn.left, &tn.k, &tn.v, &r), len)
            }
          }
        }
      }
    }
  }
}

pub(crate) fn min_elts<'a, K, V>(t: &'a Tree<K, V>) -> Option<&'a elts::t<K,V>>
  where K: Ord + Clone, V: Clone
{
  match *t {
    Tree::Empty => Option::None,
    Tree::Node(ref tn) => 
      match tn.left {
        Tree::Empty => Option::Some(&tn.elts),
        Tree::Node(_) => min_elt(&tn.left)
      }
  }
}

fn remove_min_elts<K, V>(t: &Tree<K,V>) -> Tree<K,V>
  where K: Ord + Clone, V: Clone
{
  match *t {
    Tree::Empty => panic!("remove min elt"),
    Tree::Node(ref tn) =>
      match tn.left {
        Tree::Empty => tn.right.clone(),
        Tree::Node(_) => bal(&remove_min_elts(&tn.left), &tn.k, &tn.v, &tn.right)
      }
  }
}

fn concat<K, V>(l: &Tree<K, V>, r: &Tree<K, V>) -> Tree<K, V>
  where K: Ord + Clone, V: Clone
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
  where K: Ord + Clone, V: Clone
{
  match *t {
    Tree::Empty => (Tree::Empty, len),
    Tree::Node(ref tn) =>
      match elts::localize(elts::index_of(&tn.elts, k)) {
        elts::Loc::NotPresent => create(&tn.left, &tn.elts, &tn.right),
        elts::Loc::Here(i) => {
          let elts = elts::remove_elt_at(&tn.elts, i);
          if elts::is_empty(&elts) {
            (concat(&tn.left, &tn.right), len - 1)
          } else {
            create(&tn.left, &elts, &tn.right)
          }
        }
        elts::Loc::InLeft => {
          let (l, len) = remove(&tn.left, len, k);
          (bal(&l, &tn.k, &tn.v, &tn.right), len)
        }
        elts::Loc::InRight => {
          let (r, len) = remove(&tn.right, len, k);
          (bal(&tn.left, &tn.k, &tn.v, &r), len)
        }
      }
  }
}

pub(crate) fn find<'a, K, V>(t: &'a Tree<K, V>, k: &K) -> Option<&'a V>
  where K: Ord + Clone, V: Clone
{
  match *t {
    Tree::Empty => Option::None,
    Tree::Node(ref tn) =>
      match elts::find(&tn.elts, k) {
        elts::Loc::Here(i) => Option::Some(&tn.elts[i]),
        elts::Loc::NotPresent => Option::None,
        elts::Loc::InLeft => find(&tn.left, k),
        elts::Loc::InRight => find(&tn.right, k)
      }
  }
}

#[allow(dead_code)]
pub(crate) fn invariant<K,V>(t: &Tree<K,V>, len: usize) -> ()
  where K: Ord + Clone, V: Clone
{
  fn in_range<K: Ord>(lower: Option<&K>, upper: Option<&K>, k: &K) -> bool {
    (match lower {
      Option::None => true,
      Option::Some(lower) => lower.cmp(k) == Ordering::Less })
      && (match upper {
        Option::None => true,
        Option::Some(upper) => upper.cmp(k) == Ordering::Greater })
  }

  fn check<K,V>(t: &Tree<K,V>, lower: Option<&K>, upper: Option<&K>, len: usize)
                -> (u16, usize)
    where K: Ord + Clone, V: Clone
  {
    match *t {
      Tree::Empty => (0, len),
      Tree::Leaf(ref k, _) => {
        if !in_range(lower, upper, k) { panic!("tree invariant violated") };
        (1, len + 1)
      }
      Tree::Node(ref tn) => {
        if !in_range(lower, upper, &tn.k) { panic!("tree invariant violated") };
        let (thl, len) = check(&tn.left, lower, Option::Some(&tn.k), len);
        let (thr, len) = check(&tn.right, Option::Some(&tn.k), upper, len);
        let th = 1 + max(thl, thr);
        let (hl, hr) = (height(&tn.left), height(&tn.right));
        if max(hl, hr) - min(hl, hr) > 2 { panic!("tree is unbalanced") };
        if thl != hl { panic!("left node height is wrong") };
        if thr != hr { panic!("right node height is wrong") };
        let h = height(t);
        if th != h { panic!("node height is wrong {} vs {}", th, h) };
        (th, len + 1)
      }
    }
  }

  let (_height, tlen) = check(t, Option::None, Option::None, 0);
  if len != tlen { panic!("len is wrong {} vs {}", len, tlen) }
}
