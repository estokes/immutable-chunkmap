extern crate immutable_avl;
extern crate rand;
use immutable_avl::map;
use std::time::{Duration, Instant};
use rand::{random, Rand};
use std::env;
use std::str;
use std::iter::FromIterator;
use std::vec::{Vec};

fn randvec<T: Rand>(len: usize) -> Vec<T> {
  let mut v: Vec<T> = Vec::new();
  for _ in 0..len { v.push(random()) }
  v
}

fn bench_add(len: usize) -> (map::Map<i32, i32>, Vec<i32>, Duration) {
    let mut m = map::empty();
    let data = randvec::<i32>(len);
    let begin = Instant::now();
    for kv in &data {
        m = map::add(&m, kv, kv);
    }
    (m, data, begin.elapsed())
}

fn bench_find(m: &map::Map<i32, i32>, d: &Vec<i32>) -> Duration {
    let begin = Instant::now();
    for kv in d {
        map::find(m, &kv).unwrap();
    }
    begin.elapsed()
}

fn bench_remove(m: map::Map<i32, i32>, d: &Vec<i32>) -> Duration {
    let mut m = m;
    let begin = Instant::now();
    for kv in d {
        m = map::remove(&m, &kv);
    }
    begin.elapsed()
}

fn to_ms(t: Duration) -> u64 {
    t.as_secs() * 1000 + ((t.subsec_nanos() / 1000000) as u64)
}

fn main() {
    let args = Vec::from_iter(env::args());
    let size =
        if args.len() == 2 { args[1].parse::<usize>().unwrap() }
        else { 10000 };
    let (m, d, add) = bench_add(size);
    let find = bench_find(&m, &d);
    let rm = bench_remove(m, &d);
    println!("add: {}, find: {}, remove: {}", 
        to_ms(add), to_ms(find), to_ms(rm));
}
