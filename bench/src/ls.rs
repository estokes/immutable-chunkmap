extern crate num_cpus;
use std::sync::Arc;
use std::time::{Duration, Instant};
use std::vec::Vec;
use std::thread;
use std::cmp::min;
use utils;

fn find(k: i64, data: &Arc<Vec<i64>>) -> Option<i64> {
  for i in 0..data.len() {
    if data[i] == k { return Option::Some(data[i]) }
  }
  Option::None
}

fn bench_find(d: &Arc<Vec<i64>>) -> Duration {
  let n = num_cpus::get();
  let chunk = d.len() / n;
  let mut threads = Vec::new();
  let begin = Instant::now();
  for i in 0 .. n {
    let d = d.clone();
    let th = 
      thread::spawn(move || {
        let p = i * chunk;
        for j in p .. min(d.len() - 1, p + chunk) {
          assert_eq!(find(d[j], &d).unwrap(), d[j])
        }
      });
    threads.push(th);
  }
  for th in threads { th.join().unwrap(); }
  begin.elapsed()
}

fn bench_find_seq(d: &Arc<Vec<i64>>) -> Duration {
  let begin = Instant::now();
  for k in d.iter() {
    assert_eq!(find(*k, d).unwrap(), *k)
  }
  begin.elapsed()
}

pub(crate) fn run(size: usize) -> () {
  let data = Arc::new(utils::randvec::<i64>(size));
  let find_par = bench_find(&data);
  let find = bench_find_seq(&data);
  println!("find: {}ns, find_par: {}ns", 
    utils::to_ns_per(find, size), 
    utils::to_ns_per(find_par, size));
}
