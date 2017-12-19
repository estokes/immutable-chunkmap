extern crate immutable_map;
use immutable_map::TreeMap;
use std::time::{Duration, Instant};
use rand::{random, Rand};
use std::env;
use std::str;
use std::iter::FromIterator;
use std::vec::{Vec};
use utils;

fn bench_add(len: usize) -> (TreeMap<i64, i64>, Vec<i64>, Duration) {
    let mut m = TreeMap::new();
    let data = randvec::<i64>(len);
    let begin = Instant::now();
    for kv in &data { m = m.insert(*kv, *kv) }
    (m, data, begin.elapsed())
}

fn bench_find(m: &TreeMap<i64, i64>, d: &Vec<i64>) -> Duration {
    let begin = Instant::now();
    for kv in d { m.get(&kv).unwrap(); }
    begin.elapsed()
}

fn bench_remove(m: TreeMap<i64, i64>, d: &Vec<i64>) -> Duration {
    let mut m = m;
    let begin = Instant::now();
    for kv in d {
        match m.remove(&kv) {
            Option::None => (),
            Option::Some((r, _)) => m = r
        }
    }
    begin.elapsed()
}

fn to_ms(t: Duration) -> u64 {
    t.as_secs() * 1000 + ((t.subsec_nanos() / 1000000) as u64)
}

fn run(size: usize) {
  let (m, d, add) = bench_add(size);
  let find = bench_find(&m, &d);
  let rm = bench_remove(m, &d);
  println!("add: {}ns, find: {}ns, remove: {}ns", 
      utils::to_ns_per(add, size), 
      utils::to_ns_per(find, size), 
      to_ns_per(rm, size));
}
