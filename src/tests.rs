extern crate rand;
use avl;
use std::iter::Iterator;

fn add<I, T>(r: I) -> avl::Tree<T, T>
  where I: Iterator<Item=T>, T: Ord + Clone
{
  let mut t = avl::empty();
  let mut len = 0;
  for i in r {
    let (tt, tlen) = avl::add(&t, len, &i, &i);
    t = tt;
    len = tlen;
    avl::invariant(&t, Option::Some(len));
  }
  t
}

#[test]
fn test_add_int_seq_asc() {
  add(1..10000); ()
}

#[test]
fn test_add_int_seq_dec() {
  add(10000..1); ()
}
