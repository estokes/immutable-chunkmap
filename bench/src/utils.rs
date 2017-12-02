extern crate rand;
use std::time::Duration;
use std::vec::{Vec};
use self::rand::{random, Rand};

pub(crate) fn randvec<T: Rand>(len: usize) -> Vec<T> {
  let mut v: Vec<T> = Vec::new();
  for _ in 0..len { v.push(random()) }
  v
}

pub(crate) fn to_ms(t: Duration) -> u64 {
  t.as_secs() * 1000 + ((t.subsec_nanos() / 1000000) as u64)
}
