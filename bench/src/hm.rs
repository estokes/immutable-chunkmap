
extern crate num_cpus;
use std::sync::{Arc, RwLock};
use std::collections::HashMap;
use std::time::{Duration, Instant};
use std::vec::{Vec};
use std::thread;
use std::cmp::min;
use utils;

fn bench_add(len: usize) -> (Arc<RwLock<HashMap<i64, i64>>>, Arc<Vec<i64>>, Duration) {
  let mut m = HashMap::new();
  let data = utils::randvec::<i64>(len);
  let begin = Instant::now();
  for k in &data { m.insert(*k, *k); }
  (Arc::new(RwLock::new(m)), Arc::new(data), begin.elapsed())
}

fn bench_find(m: &Arc<RwLock<HashMap<i64, i64>>>, d: &Arc<Vec<i64>>) -> Duration {
  let n = num_cpus::get();
  let chunk = d.len() / n;
  let mut threads = Vec::new();
  let begin = Instant::now();
  for i in 0 .. n {
    let (m, d) = (m.clone(), d.clone());
    let th = 
      thread::spawn(move || {
        let m = m.read().unwrap();
        let p = i * chunk;
        for j in p .. min(d.len() - 1, p + chunk) {
          m.get(&d[j]).unwrap();
        }
      });
    threads.push(th);
  }
  for th in threads { th.join().unwrap(); }
  begin.elapsed()
}

fn bench_find_seq(m: &Arc<RwLock<HashMap<i64, i64>>>, d: &Vec<i64>) -> Duration {
  let begin = Instant::now();
  let m = m.read().unwrap();
  for k in d { m.get(k).unwrap(); }
  begin.elapsed()
}

fn bench_remove(m: &Arc<RwLock<HashMap<i64, i64>>>, d: &Vec<i64>) -> Duration {
  let begin = Instant::now();
  let mut m = m.write().unwrap();
  for k in d { m.remove(k).unwrap(); }
  begin.elapsed()
}

pub(crate) fn run(size: usize) -> () {
  let (mut m, d, add) = bench_add(size);
  let find_par = bench_find(&m, &d);
  let find = bench_find_seq(&m, &d);
  let rm = bench_remove(&mut m, &d);
  println!("add: {}ns, find: {}ns, find_par: {}ns, remove: {}ns", 
    utils::to_ns_per(add, size), 
    utils::to_ns_per(find, size),
    utils::to_ns_per(find_par, size), 
    utils::to_ns_per(rm, size));
}
