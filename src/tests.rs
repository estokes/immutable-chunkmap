extern crate rand;
use avl;
use tests::rand::{random, Rand};
use std::iter::{IntoIterator};
use std::vec::{Vec};

fn add<I, T>(r: I) -> (avl::Tree<T, T>, usize)
  where I: IntoIterator<Item=T>, T: Ord + Clone
{
  let mut t = avl::empty();
  let mut len = 0;
  for i in r {
    let (tt, tlen) = avl::add(&t, len, &i, &i);
    t = tt;
    len = tlen;
    avl::invariant(&t, Option::Some(len));
  }
  (t, len)
}

fn randvec<T: Rand>(len: usize) -> Vec<T> {
  let mut v: Vec<T> = Vec::new();
  for _ in 0..len { v.push(random()) }
  v
}

#[test]
fn test_add_int_seq_asc() {
  let (_, len) = add(0..10000);
  if len != 10000 { panic!("length is wrong expected 10000 got {}", len) }
}

#[test]
fn test_add_int_seq_dec() {
  let (_, len) = add((0..10000).rev());
  if len != 10000 {panic!("length is wrong expected 10000 got {}", len)}
}

#[test]
fn test_add_int_rand() {
  add(randvec::<i32>(10000)); ()
}

#[test]
fn test_find_int_rand() {
  let v = randvec::<i32>(10000);
  let (t, _) = add(&v);
  for k in &v {
    assert_eq!(*avl::find(&t, &k).unwrap(), k);
  }
}

#[test]
fn test_int_add_remove_rand() {
  let v = randvec::<i32>(10000);
  let (mut t, mut len) = add(&v);
  for k in &v {
    assert_eq!(*avl::find(&t, &k).unwrap(), k);
    let (tt, tlen) = avl::remove(&t, len, &k);
    t = tt;
    len = tlen;
    avl::invariant(&t, Option::Some(len));
    assert_eq!(avl::find(&t, &k), Option::None);
  }
}
