extern crate immutable_chunkmap;
use self::immutable_chunkmap::rc::map::Map;
use std::time::{Duration, Instant};
use std::vec::{Vec};
use utils;

fn bench_insert_sorted(len: usize) -> (Map<i64, i64>, Vec<i64>, Duration) {
  let mut m = Map::new();
  let data = utils::randvec::<i64>(len);
  let elapsed = {
    let mut pairs : Vec<(&i64, &i64)> = data.iter().map(|k| (k, k)).collect();
    let begin = Instant::now();
    pairs.sort_unstable_by(|&(k0, _), &(k1, _)| k0.cmp(k1));
    m = m.insert_sorted(&pairs);
    begin.elapsed()
  };
  (m, data, elapsed)
}

fn bench_insert(data: &Vec<i64>) -> Duration {
  let mut m = Map::new();
  let begin = Instant::now();
  for k in data { m = m.insert(k, k); }
  begin.elapsed()
}

fn bench_get(m: &Map<i64, i64>, d: &Vec<i64>) -> Duration {
  let begin = Instant::now();
  for kv in d { m.get(&kv).unwrap(); }
  begin.elapsed()
}

fn bench_remove(m: Map<i64, i64>, d: &Vec<i64>) -> Duration {
  let mut m = m;
  let begin = Instant::now();
  for kv in d { m = m.remove(&kv) }
  begin.elapsed()
}

pub(crate) fn run(size: usize) -> () {
  let (m, d, insert_sorted) = bench_insert_sorted(size);
  let insert = bench_insert(&d);
  let get = bench_get(&m, &d);
  let rm = bench_remove(m, &d);
  println!("{},{},{},{},0,{}",
    size,
    utils::to_ns_per(insert, size),
    utils::to_ns_per(insert_sorted, size),
    utils::to_ns_per(get, size),
    utils::to_ns_per(rm, size));
}
