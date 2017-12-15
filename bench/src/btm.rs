extern crate num_cpus;
use std::sync::{Arc, RwLock};
use std::collections::BTreeMap;
use std::time::{Duration, Instant};
use std::vec::{Vec};
use std::thread;
use std::cmp::min;
use utils;

fn bench_add(len: usize) -> (Arc<RwLock<BTreeMap<i64, i64>>>, Arc<Vec<i64>>, Duration) {
  let mut m = BTreeMap::new();
  let data = utils::randvec::<i64>(len);
  let begin = Instant::now();
  for k in &data { m.insert(*k, *k); }
  (Arc::new(RwLock::new(m)), Arc::new(data), begin.elapsed())
}

fn bench_find(m: &Arc<RwLock<BTreeMap<i64, i64>>>, d: &Arc<Vec<i64>>) -> Duration {
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

fn bench_find_seq(m: &Arc<RwLock<BTreeMap<i64, i64>>>, d: &Vec<i64>) -> Duration {
  let begin = Instant::now();
  let m = m.read().unwrap();
  for k in d { m.get(k).unwrap(); }
  begin.elapsed()
}

fn bench_remove(m: &Arc<RwLock<BTreeMap<i64, i64>>>, d: &Vec<i64>) -> Duration {
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
  println!("add: {}, find: {}, find_par: {}, remove: {}", 
    utils::to_ms(add), utils::to_ms(find),
    utils::to_ms(find_par), utils::to_ms(rm));
}
