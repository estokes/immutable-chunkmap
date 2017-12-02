extern crate rand;
use std::vec::{Vec};
use rand::{random, Rand};

fn randvec<T: Rand>(len: usize) -> Vec<T> {
  let mut v: Vec<T> = Vec::new();
  for _ in 0..len { v.push(random()) }
  v
}
