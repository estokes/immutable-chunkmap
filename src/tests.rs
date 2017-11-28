extern crate rand;
use avl;
use map;
use tests::rand::Rng;
use std::iter::{IntoIterator};
use std::vec::{Vec};
use std::fmt::Debug;

const STRSIZE: usize = 80;

trait Rand: Sized {
  fn rand<R: Rng>(r: &mut R) -> Self;
}

impl Rand for String {
  fn rand<R: Rng>(r: &mut R) -> Self {
    let mut s = String::new();
    for _ in 0..STRSIZE { s.push(r.gen()) }
    s
  }
}

impl Rand for i32 {
  fn rand<R: Rng>(r: &mut R) -> Self { r.gen() }
}

fn random<T: Rand>() -> T {
  let mut rng = rand::thread_rng();
  T::rand(&mut rng)
}

fn randvec<T: Rand>(len: usize) -> Vec<T> {
  let mut v: Vec<T> = Vec::new();
  for _ in 0..len { v.push(random()) }
  v
}

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

/*
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

fn test_find_rand<T: Ord + Clone + Debug + Rand>() {
  let v = randvec::<T>(10000);
  let (t, _) = add(&v);
  for k in &v {
    assert_eq!(*t.find(&k).unwrap(), k);
  }
}

#[test]
fn test_find_int_rand() { test_find_rand::<i32>() }

#[test]
fn test_find_str_rand() { test_find_rand::<String>() }

fn test_add_remove_rand<T: Ord + Clone + Debug + Rand>() {
  let v = randvec::<T>(7000);
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
fn test_int_add_remove_rand() { test_add_remove_rand::<i32>() }

#[test]
fn test_str_add_remove_rand() { test_add_remove_rand::<String>() }

fn test_map_rand<T: Ord + Clone + Debug + Rand>() {
  let v = randvec::<T>(2000);
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

#[test]
fn test_int_map_rand() { test_map_rand::<i32>() }

#[test]
fn test_str_map_rand() { test_map_rand::<String>() }
*/

fn test_map_iter<T: Ord + Clone + Debug + Rand>() {
  let mut v = randvec::<i32>(4000);
  let mut t = map::Map::new();
  for k in &v { t = t.add(&k, &k) };
  t.invariant();
  let mut vs = v.clone(); 
  vs.sort_unstable();
  let mut i = 0;
  for &(k0, k1) in &t {
    assert_eq!(*k0, *k1);
    assert_eq!(*k0, vs[i]);
    i = i + 1;
  }
}

#[test]
fn test_int_map_iter() { test_map_iter::<i32>() }

//#[test]
//fn test_string_map_iter() { test_map_iter::<String>() }
