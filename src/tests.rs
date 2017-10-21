extern crate rand;
use avl;
use map;
use tests::rand::{random, Rand};
use std::iter::{IntoIterator};
use std::vec::{Vec};
use std::fmt::Debug;

fn add<I, T>(r: I) -> (avl::Tree<T, T>, usize)
  where I: IntoIterator<Item=T>, T: Ord + Clone + Debug
{
  let mut t = avl::Tree::new();
  let mut len = 0;
  for i in r {
    let (tt, tlen) = t.add(len, &i, &i);
    t = tt;
    len = tlen;
    t.invariant(len);
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
  let size = 10000;
  let (_, len) = add(0..size);
  if len != size { panic!("length is wrong expected 10000 got {}", len) }
}

#[test]
fn test_add_int_seq_dec() {
  let size = 10000;
  let (_, len) = add((0..size).rev());
  if len != size {panic!("length is wrong expected 10000 got {}", len)}
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
    assert_eq!(*t.find(&k).unwrap(), k);
  }
}

#[test]
fn test_int_add_remove_rand() {
  let v = randvec::<i32>(7000);
  let (mut t, mut len) = add(&v);
  for k in &v {
    assert_eq!(*t.find(&k).unwrap(), k);
    let (tt, tlen) = t.remove(len, &k);
    t = tt;
    len = tlen;
    t.invariant(len);
    assert_eq!(t.find(&k), Option::None);
  }
}

#[test]
fn test_int_map_rand() {
  let v = randvec::<i32>(2000);
  let mut t = map::Map::new();
  let mut i = 0;
  for k in &v {
    t = t.add(&k, &k);
    t.invariant();
    i = i + 1;
    for k in &v[0..i] { 
      assert_eq!(*t.find(&k).unwrap(), k);
    }
  }
  
  i = 0;
  for k in &v {
    t = t.remove(&k);
    t.invariant();
    i = i + 1;
    for k in &v[0..i] {
      assert_eq!(t.find(&k), Option::None);
    }
  }
}
