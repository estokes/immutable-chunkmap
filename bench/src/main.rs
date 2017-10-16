extern crate immutable_avl;
use map;
use std::time::{Duration, Instant};
use rand::{random, Rand};
use std::env;
use std::str::FromStr;

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
        m = map::add(&kv, &kv);
    }
    let end = Instant::now();
    (m, data, begin.elapsed());
}

fn bench_find(m: &map::Map<i32, i32>, d: &Vec<i32>) -> Duration {
    let begin = Instant::now();
    for kv in d {
        map::find(m, &kv); ()
    }
    let end = Instant::now();
    end.duration_since(begin);
}

fn bench_remove(m: map::Map<i32, i32>, d: &Vec<i32>) -> Duration {
    let mut m = m;
    let begin = Instant::now();
    for kv in d {
        m = map::remove(&m, &kv);
    }
    begin.elapsed();
}

fn main() {
    let args = env::args();
    let size =
        if args.count() = 2 { args.nth(1).unwrap().parse::<i32>().unwrap(); }
        else { 10000 };
    let (m, d, add) = bench_add(size);
    let find = bench_find(&m, &d);
    let rm = bench_remove(m, &d):
    println!("add: {}, find: {}, remove: {}", add, find, rm);
}
