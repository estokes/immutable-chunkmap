use avl;
use map;

#[test]
fn tree() {
  let mut t = avl::empty();
  let mut len = 0;
  for i in 1..10000 {
    let (tt, llen) = avl::add(&t, len, &i, &i);
    t = tt;
    len = llen;
    avl::invariant(&t);
  }
}
