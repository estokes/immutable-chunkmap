use std::rc::Rc;

pub struct Node<K: Ord, V> {
  key: Rc<K>,
  val: Rc<V>,
  left: Rc<Tree<K, V>>,
  right: Rc<Tree<K, V>>,
  height: u64
}

pub enum Tree<K: Ord, V> {
  Empty,
  Leaf(Rc<K>, Rc<V>),
  Node(Node<K,V>)
}

pub fn height<K: Ord,V>(t: &Tree<K,V>) -> u64 {
  match t {
    &Tree::Empty => 0,
    &Tree::Leaf(_, _) => 1,
    &Tree::Node(Node {height, ..}) => height
  }
}

fn em<K: Ord, V>() -> Rc<Tree<K,V>> {
  Rc::new(Tree::Empty)
}

pub fn singleton<K: Ord, V>(k: &Rc<K>, v: &Rc<V>) -> Rc<Tree<K, V>> {
  Rc::new(Tree::Leaf(k.clone(), v.clone()))
}

pub fn create<K: Ord, V>(l: &Rc<Tree<K,V>>,
                         k: &Rc<K>, v: &Rc<V>,
                         r: &Rc<Tree<K,V>>)
                         -> Rc<Tree<K,V>> {
  let (hl, hr) = (height(l), height(r));
  if hl == 0 && hr == 0 { Rc::new(Tree::Leaf(k.clone(), v.clone())) }
  else {
    let h = if hl >= hr { hl } else { hr };
    let t =
      Tree::Node(Node {key: k.clone(), val: v.clone(),
                       left: l.clone(), right: r.clone(),
                       height: h});
    Rc::new(t)
  }
}

fn bal<K: Ord, V>(l: &Rc<Tree<K,V>>, x: &Rc<K>, d: &Rc<V>, r: &Rc<Tree<K,V>>)
                  -> Rc<Tree<K,V>>  {
  let hl = height(l);
  let hr = height(r);
  if hl > hr + 2 {
    match **l {
      Tree::Empty | Tree::Leaf(_, _) => panic!("tree heights are wrong"),
      Tree::Node(Node {left:ref ll, key:ref lv, val:ref ld, right:ref lr, ..}) => {
        if height(ll) >= height(lr) {
          create(ll, lv, ld, &create(lr, x, d, r))
        } else {
          match **lr {
            Tree::Empty => panic!("tree heights wrong"),
            Tree::Leaf(ref lrv, ref lrd) =>
              create(&create(ll, lv, ld, &em()), lrv, lrd, &create(&em(), x, d, r)),
            Tree::Node(Node {left:ref lrl, key: ref lrv,
                             val: ref lrd, right: ref lrr, ..}) =>
              create(&create(ll, lv, ld, lrl), lrv, lrd, &create(lrr, x, d, r))
          }
        }
      }
    }
  } else if hr > hl + 2 {
    match **r {
      Tree::Empty | Tree::Leaf(_,_) => panic!("tree heights are wrong"),
      Tree::Node(Node {left:ref rl, key: ref rv, val: ref rd, right:ref rr, ..}) => {
        if height(rr) >= height(rl) {
          create(&create(l, x, d, rl), rv, rd, rr)
        } else {
          match **rl {
            Tree::Empty => panic!("tree heights are wrong"),
            Tree::Leaf(ref rlv, ref rld) =>
              create(&create(l, x, d, &em()), rlv, rld, &create(&em(), rv, rd, rr)),
            Tree::Node(Node {left: ref rll, key: ref rlv,
                             val: ref rld, right:ref rlr, ..}) =>
              create(&create(l, x, d, rll), rlv, rld, &create(rlr, rv, rd, rr))
          }
        }
      }
    }
  } else {
    create(l, x, d, r)
  }
}

#[cfg(test)]
mod tests {
  #[test]
  fn it_works() {
  }
}
