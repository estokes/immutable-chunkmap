use std::rc::Rc;
use std::cmp::{Ordering, max, min};

#[derive (Clone)]
pub(crate) struct Node<K: Ord + Clone, V: Clone> {
  k: K,
  v: V,
  left: Tree<K, V>,
  right: Tree<K, V>,
  height: u16
}

#[derive (Clone)]
pub(crate) enum Tree<K: Ord + Clone, V: Clone> {
  Empty,
  Leaf(K, V),
  Node(Rc<Node<K,V>>)
}

fn height<K: Ord + Clone, V: Clone>(t: &Tree<K,V>) -> u16 {
  match *t {
    Tree::Empty => 0,
    Tree::Leaf(_, _) => 1,
    Tree::Node(ref n) => n.height
  }
}

pub(crate) fn empty<K: Ord + Clone, V: Clone>() -> Tree<K,V> { Tree::Empty }


fn create<K, V>(l: &Tree<K, V>, k: &K, v: &V, r: &Tree<K, V>) -> Tree<K, V>
  where K: Ord + Clone, V: Clone
{
  let (hl, hr) = (height(l), height(r));
  if hl == 0 && hr == 0 { Tree::Leaf(k.clone(), v.clone()) }
  else {
    Tree::Node(Rc::new(Node {k: k.clone(), v: v.clone(),
                             left: l.clone(), right: r.clone(),
                             height: 1 + max(hl, hr)}))
  }
}

fn bal<K, V>(l: &Tree<K, V>, k: &K, v: &V, r: &Tree<K, V>) -> Tree<K, V>
  where K: Ord + Clone, V: Clone
{
  let (hl, hr) = (height(l), height(r));
  if hl > hr + 2 {
    match *l {
      Tree::Empty | Tree::Leaf(_, _) => panic!("tree heights are wrong"),
      Tree::Node(ref ln) =>
        if height(&ln.left) >= height(&ln.right) {
          create(&ln.left, &ln.k, &ln.v, &create(&ln.right, k, v, r))
        } else {
          match ln.right {
            Tree::Empty => panic!("tree heights wrong"),
            Tree::Leaf(ref lrk, ref lrv) =>
              create(&create(&ln.left, &ln.k, &ln.v, &empty()),
                     lrk, lrv,
                     &create(&empty(), k, v, r)),
            Tree::Node(ref lrn) =>
              create(&create(&ln.left, &ln.k, &ln.v, &lrn.left),
                     &lrn.k, &lrn.v,
                     &create(&lrn.right, k, v, r))
          }
        }
    }
  } else if hr > hl + 2 {
    match *r {
      Tree::Empty | Tree::Leaf(_,_) => panic!("tree heights are wrong"),
      Tree::Node(ref rn) =>
        if height(&rn.right) >= height(&rn.left) {
          create(&create(l, k, v, &rn.left), &rn.k, &rn.v, &rn.right)
        } else {
          match rn.left {
            Tree::Empty => panic!("tree heights are wrong"),
            Tree::Leaf(ref rlk, ref rlv) =>
              create(&create(l, k, v, &empty()),
                     rlk, rlv,
                     &create(&empty(), &rn.k, &rn.v, &rn.right)),
            Tree::Node(ref rln) =>
              create(&create(l, k, v, &rln.left),
                     &rln.k, &rln.v,
                     &create(&rln.right, &rn.k, &rn.v, &rn.right))
          }
      }
    }
  } else {
    create(l, k, v, r)
  }
}

pub(crate) fn add<K, V>(t: &Tree<K, V>, len: usize, k: &K, v: &V) -> (Tree<K, V>, usize)
  where K: Ord + Clone, V: Clone
{
  match *t {
    Tree::Empty => (Tree::Leaf(k.clone(), v.clone()), len + 1),
    Tree::Leaf(ref tk, ref tv) =>
      match k.cmp(tk) {
        Ordering::Equal => (Tree::Leaf(k.clone(), v.clone()), len),
        Ordering::Less => {
          let n = Node { left: Tree::Leaf(k.clone(), v.clone()),
                         k: tk.clone(), v: tv.clone(),
                         right: Tree::Empty,
                         height: 2 };
          (Tree::Node(Rc::new(n)), len + 1)
        },
        Ordering::Greater => {
          let n = Node {left: Tree::Empty,
                        k: tk.clone(), v: tv.clone(),
                        right: Tree::Leaf(k.clone(), v.clone()),
                        height: 2 };
          (Tree::Node(Rc::new(n)), len + 1)
        }
      },
    Tree::Node(ref tn) =>
      match k.cmp(&tn.k) {
        Ordering::Equal => (create(&tn.left, k, v, &tn.right), len),
        Ordering::Less => {
          let (l, len) = add(&tn.left, len, k, v);
          (bal(&l, &tn.k, &tn.v, &tn.right), len)
        },
        Ordering::Greater => {
          let (r, len) = add(&tn.right, len, k, v);
          (bal(&tn.left, &tn.k, &tn.v, &r), len)
        }
      }
  }
}

pub(crate) fn min_elt<'a, K, V>(t: &'a Tree<K, V>) -> Option<(&'a K, &'a V)>
  where K: Ord + Clone, V: Clone
{
  match *t {
    Tree::Empty => Option::None,
    Tree::Leaf(ref k, ref v) => Option::Some((k, v)),
    Tree::Node(ref tn) => min_elt(&tn.left)
  }
}

fn remove_min_elt<K, V>(t: &Tree<K,V>) -> Tree<K,V>
  where K: Ord + Clone, V: Clone
{
  match *t {
    Tree::Empty => panic!("remove min elt"),
    Tree::Leaf(_, _) => Tree::Empty,
    Tree::Node(ref tn) =>
      match *tn.left {
        Tree::Empty => tn.right,
        Tree::Leaf(_, _) => bal(Tree::Empty, &tn.k, &tn.v, &tn.right),
        Tree::Node(_) => bal(&remove_min_elt(&tn.left), &tn.k, &tn.v, &tn.right)
      }
  }
}

/*
pub(crate) fn max_elt<'a, K, V>(t: &'a Tree<K,V>) -> Option<(&'a K, &'a V)>
  where K: Ord + Clone, V: Clone
{
  match *t {
    Tree::Empty => Option::None,
    Tree::Leaf(ref k, ref d) => Option::Some((k, d)),
    Tree::Node(ref tn) => max_elt(&tn.right)
  }
}
*/

fn concat<K, V>(l: &Tree<K, V>, r: &Tree<K, V>) -> Tree<K, V>
  where K: Ord + Clone, V: Clone
{
  match (l, r) {
    (&Tree::Empty, _) => r.clone(),
    (_, &Tree::Empty) => l.clone(),
    (_, _) => {
      let (k, v) = min_elt(r).unwrap();
      bal(l, k, v, &remove_min_elt(r))
    }
  }
}

pub(crate) fn remove<K, V>(t: &Tree<K,V>, len: usize, k: &K) -> (Tree<K,V>, usize)
  where K: Ord + Clone, V: Clone
{
  match *t {
    Tree::Empty => (Tree::Empty, len),
    Tree::Leaf(ref tk, _) =>
      match k.cmp(tk) {
        Ordering::Equal => (Tree::Empty, len - 1),
        Ordering::Greater | Ordering::Less => (t.clone(), len)
      },
    Tree::Node(ref tn) =>
      match k.cmp(&tn.k) {
        Ordering::Equal => (concat(&tn.left, &tn.right), len - 1),
        Ordering::Less => {
          let (l, len) = remove(&tn.left, len, k);
          (bal(&l, &tn.k, &tn.v, &tn.right), len)
        },
        Ordering::Greater => {
          let (r, len) = remove(&tn.right, len, k);
          (bal(&tn.left, &tn.k, &tn.v, &r), len)
        }
      }
  }
}

pub(crate) fn find<'a, K, V>(t: &'a Tree<K,V>, k: &K) -> Option<&'a V>
  where K: Ord + Clone, V: Clone
{
  match *t {
    Tree::Empty => Option::None,
    Tree::Leaf(ref tk, ref tv) =>
      if *k == *tk { Option::Some(tv) } else { Option::None },
    Tree::Node(ref tn) =>
      match k.cmp(&tn.k) {
        Ordering::Equal => Option::Some(&tn.v),
        Ordering::Less => find(&tn.left, k),
        Ordering::Greater => find(&tn.right, k)
      }
  }
}

#[allow(dead_code)]
pub(crate) fn invariant<K,V>(t: &Tree<K,V>, len: Option<usize>) -> ()
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
  match len {
    Option::None => (),
    Option::Some(len) =>
      if len != tlen { panic!("len is wrong {} vs {}", len, tlen) }
  }
}
