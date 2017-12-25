
extern crate num_cpus;
use std::sync::{Arc, RwLock};
use std::collections::HashMap;
use std::time::{Duration, Instant};
use std::vec::{Vec};
use std::thread;
use std::cmp::min;
use utils;

fn bench_insert(len: usize) -> (Arc<RwLock<HashMap<i64, i64>>>, Arc<Vec<i64>>, Duration) {
  let mut m = HashMap::new();
  let data = utils::randvec::<i64>(len);
  let begin = Instant::now();
  for k in &data { m.insert(*k, *k); }
  (Arc::new(RwLock::new(m)), Arc::new(data), begin.elapsed())
}

fn bench_insert_sorted(len: usize) -> (Arc<RwLock<HashMap<i64, i64>>>, Arc<Vec<i64>>, Duration) {
  let mut m = HashMap::new();
  let mut data = utils::randvec::<i64>(len);
  let begin = Instant::now();
  data.sort_unstable();
  for k in &data { m.insert(*k, *k); }
  (Arc::new(RwLock::new(m)), Arc::new(data), begin.elapsed())
}

fn bench_get(m: &Arc<RwLock<HashMap<i64, i64>>>, d: &Arc<Vec<i64>>) -> Duration {
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

fn bench_get_seq(m: &Arc<RwLock<HashMap<i64, i64>>>, d: &Vec<i64>) -> Duration {
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
  let (mut m, d, insert) = bench_insert(size);
  let (_, _, inserts) = bench_insert_sorted(size);
  let get_par = bench_get(&m, &d);
  let get = bench_get_seq(&m, &d);
  let rm = bench_remove(&mut m, &d);
  println!("insert: {}ns, inserts: {}ns, get: {}ns, get_par: {}ns, remove: {}ns",
    utils::to_ns_per(insert, size),
    utils::to_ns_per(inserts, size),
    utils::to_ns_per(get, size),
    utils::to_ns_per(get_par, size),
    utils::to_ns_per(rm, size));
}
