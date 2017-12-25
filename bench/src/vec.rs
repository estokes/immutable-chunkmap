use std::time::{Duration, Instant};
use std::vec::Vec;
use utils;

fn bench_get(m: &Vec<i64>) -> (i64, Duration) {
  let order = utils::permute::<usize>(&(0..m.len()).collect());
  let mut tot = 0;
  let begin = Instant::now();
  for i in order { tot = tot + (m[i] >> 16); }
  (tot, begin.elapsed())
}

fn bench_get_seq(m: &Vec<i64>) -> (i64, Duration) {
  let mut tot = 0;
  let begin = Instant::now();
  for i in m { tot = tot + (i >> 16) }
  (tot, begin.elapsed())
}

pub(crate) fn run(size: usize) -> () {
  let m = utils::randvec::<i64>(size);
  let tot0 = {
    let mut c = 0;
    for v in &m { c = c + (v >> 16) }
    c
  };
  let (tot1, get) = bench_get(&m);
  let (tot2, gets) = bench_get_seq(&m);
  assert_eq!(tot0, tot1);
  assert_eq!(tot0, tot2);
  println!("{},0,0,{},{},0", 
    size,
    utils::to_ns_per(get, size),
    utils::to_ns_per(gets, size));
}
