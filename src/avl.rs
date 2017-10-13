use std::rc::Rc;
use std::cmp::Ordering;

#[derive (Clone)]
struct Node<K: Ord + Clone, V: Clone> {
  k: K,
  v: V,
  left: Tree<K, V>,
  right: Tree<K, V>,
  height: u16
}

#[derive (Clone)]
enum Tree<K: Ord + Clone, V: Clone> {
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

fn em<K: Ord + Clone, V: Clone>() -> Tree<K,V> { Tree::Empty }


fn create<K, V>(l: &Tree<K, V>, k: &K, v: &V, r: &Tree<K, V>) -> Tree<K, V>
  where K: Ord + Clone, V: Clone
{
  let (hl, hr) = (height(l), height(r));
  if hl == 0 && hr == 0 { Tree::Leaf(k.clone(), v.clone()) }
  else {
    let h = if hl >= hr { hl } else { hr };
    Tree::Node(Rc::new(Node {k: k.clone(), v: v.clone(),
                             left: l.clone(), right: r.clone(),
                             height: h}))
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
              create(&create(&ln.left, &ln.k, &ln.v, &em()),
                     lrk, lrv,
                     &create(&em(), k, v, r)),
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
              create(&create(l, k, v, &em()),
                     rlk, rlv,
                     &create(&em(), &rn.k, &rn.v, &rn.right)),
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

fn add<K, V>(t: &Tree<K, V>, len: usize, k: &K, v: &V) -> (Tree<K, V>, usize)
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
          (bal(&l, k, v, &tn.right), len)
        },
        Ordering::Greater => {
          let (r, len) = add(&tn.right, len, k, v);
          (bal(&tn.left, k, v, &r), len)
        }
      }
  }
}

/*
fn min_elt<'a, K: Ord, V>(t: &'a Tree<K,V>) -> Option<(&'a Rc<K>, &'a Rc<V>)> {
  match *t {
    Tree::Empty => Option::None,
    Tree::Leaf(ref k, ref d) => Option::Some(k, d),
    Tree::Node(Node {left: ref l, ..}) => min_elt(l)
  }
}

fn remove_min_elt<K: Ord, V>(t: &Rc<Tree<K,V>>) -> Rc<Tree<K,V>> {
  match **t {
    Tree::Empty => t.clone(),
    Tree::Leaf(_, _) => em(),
    Tree::Node(Node {left: ref l, key: ref x, val: ref d, right: ref r}) =>
      bal(remove_min_elt(l), x, d, r)
  }
}

fn max_elt<'a, K: Ord, V>(t: &'a Tree<K,V>) -> Option<(&'a Rc<K>, &'a Rc<V>)> {
  match *t {
    Tree::Empty => Option::None,
    Tree::Leaf(ref k, ref d) => Option::Some(k, d),
    Tree::Node(Node {right: ref r, ..}) => max_elt(r)
  }
}

/*
fn concat<K: Ord, V>(t1: &Rc<Tree<K,V>>, t2: &Rc<Tree<K,V>>) -> Rc<Tree<K,V>> {
  match (*t1, *t2) {
    (Tree::Empty, _) => t2.clone(),
    (_, Tree::Empty) => t1.clone(),
    (_, _) =>
      let
  }
}

fn remove<K: Ord, V>(t: &Rc<Tree<K,V>>, len: u64, x: &K) -> (Rc<Tree<K,V>>, u64) {
  match **t {
    Tree::Empty => (t.clone(), len),
    Tree::Leaf(ref v, _) =>
      match x.cmp(v) {
        Ordering::Equal => (em(), len - 1),
        Ordering::Greater | Ordering::Less => (t.clone(), len)
      }
    Tree::Node(Node {left: ref l, key: ref k, val: ref d, right: ref r, ..}) =>
      match x.cmp(k) {
        Ordering::Equal => 
      }
  }
}
*/
fn find<'a, K: Ord, V>(t: &'a Tree<K,V>, x: &K) -> Option<&'a Rc<V>> {
  match *t {
    Tree::Empty => Option::None,
    Tree::Leaf(ref v, ref d) => if *x == **v { Option::Some(d) } else { Option::None },
    Tree::Node(Node {left: ref l, key: ref v, val: ref d, right: ref r, ..}) =>
      match x.cmp(v) {
        Ordering::Equal => Option::Some(d),
        Ordering::Less => find(l, x),
        Ordering::Greater => find(r, x)
      }
  }
}

*/
