use std::collections::BTreeMap;
use std::time::{Duration, Instant};
use std::vec::{Vec};
use utils;

fn bench_add(len: usize) -> (BTreeMap<i64, i64>, Vec<i64>, Duration) {
  let mut m = BTreeMap::new();
  let data = utils::randvec::<i64>(len);
  let begin = Instant::now();
  for k in &data { m.insert(*k, *k); }
  (m, data, begin.elapsed())
}

fn bench_find(m: &BTreeMap<i64, i64>, d: &Vec<i64>) -> Duration {
  let begin = Instant::now();
  for k in d { m.get(k).unwrap(); }
  begin.elapsed()
}

fn bench_remove(m: &mut BTreeMap<i64, i64>, d: &Vec<i64>) -> Duration {
  let begin = Instant::now();
  for k in d { m.remove(k).unwrap(); }
  begin.elapsed()
}

pub(crate) fn run(size: usize) -> () {
  let (mut m, d, add) = bench_add(size);
  let find = bench_find(&m, &d);
  let rm = bench_remove(&mut m, &d);
  println!("add: {}, find: {}, remove: {}", 
    utils::to_ms(add), utils::to_ms(find), utils::to_ms(rm));
}
