extern crate immutable;
use self::immutable::rc::map::Map;
use std::time::{Duration, Instant};
use std::vec::{Vec};
use utils;

fn bench_add(len: usize) -> (Map<i64, i64>, Vec<i64>, Duration) {
  let mut m = Map::new();
  let data = utils::randvec::<i64>(len);
  let elapsed = {
    let pairs : Vec<(&i64, &i64)> = data.iter().map(|k| (k, k)).collect();
    let begin = Instant::now();
    m = m.add_multi(&pairs);
    begin.elapsed()
  };
  //for kv in &data { m = m.add(kv, kv) }
  (m, data, elapsed)
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
  let (m, d, add) = bench_add(size);
  let find = bench_find(&m, &d);
  let rm = bench_remove(m, &d);
  println!("add: {}, find: {}, remove: {}", 
    utils::to_ms(add), utils::to_ms(find), utils::to_ms(rm));
}
