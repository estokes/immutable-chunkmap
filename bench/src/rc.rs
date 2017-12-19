extern crate immutable;
use self::immutable::rc::map::Map;
use std::time::{Duration, Instant};
use std::vec::{Vec};
use utils;

fn bench_add_sorted(len: usize) -> (Map<i64, i64>, Vec<i64>, Duration) {
  let mut m = Map::new();
  let data = utils::randvec::<i64>(len);
  let elapsed = {
    let mut pairs : Vec<(&i64, &i64)> = data.iter().map(|k| (k, k)).collect();
    let begin = Instant::now();
    pairs.sort_unstable_by(|&(k0, _), &(k1, _)| k0.cmp(k1));
    m = m.add_sorted(&pairs);
    begin.elapsed()
  };
  (m, data, elapsed)
}

fn bench_add(data: &Vec<i64>) -> Duration {
  let mut m = Map::new();
  let begin = Instant::now();
  for k in data { m = m.add(k, k); }
  begin.elapsed()
}

fn bench_find(m: &Map<i64, i64>, d: &Vec<i64>) -> Duration {
  let begin = Instant::now();
  for kv in d { m.find(&kv).unwrap(); }
  begin.elapsed()
}

fn bench_remove(m: Map<i64, i64>, d: &Vec<i64>) -> Duration {
  let mut m = m;
  let begin = Instant::now();
  for kv in d { m = m.remove(&kv) }
  begin.elapsed()
}

pub(crate) fn run(size: usize) -> () {
  let (m, d, add_sorted) = bench_add_sorted(size);
  let add = bench_add(&d);
  let find = bench_find(&m, &d);
  let rm = bench_remove(m, &d);
  println!("add: {}ns, adds: {}ns, find: {}ns, remove: {}ns", 
    utils::to_ns_per(add, size), 
    utils::to_ns_per(add_sorted, size),
    utils::to_ns_per(find, size), 
    utils::to_ns_per(rm, size));
}
