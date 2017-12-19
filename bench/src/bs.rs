extern crate num_cpus;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};
use std::vec::Vec;
use std::thread;
use std::cmp::min;
use utils;

fn create(len: usize) -> (Arc<RwLock<(Vec<i64>, Vec<i64>)>>, Arc<Vec<i64>>) {
  let data = utils::randvec::<i64>(len);
  let mut keys = data.clone();
  keys.sort_unstable();
  let vals = keys.clone();
  (Arc::new(RwLock::new((keys, vals))), Arc::new(data))
}

#[allow(dead_code)]
fn bench_add(len: usize) -> (Arc<RwLock<(Vec<i64>, Vec<i64>)>>, Arc<Vec<i64>>, Duration) {
  let mut keys = Vec::<i64>::new();
  let mut vals = Vec::<i64>::new();
  let data = utils::randvec::<i64>(len);
  let begin = Instant::now();
  for k in &data {
    match keys.binary_search(k) {
      Ok(i) => { 
        keys[i] = *k;
        vals[i] = *k;
      },
      Err(i) => {
        keys.insert(i, *k);
        vals.insert(i, *k);
      }
    }
  }
  (Arc::new(RwLock::new((keys, vals))), Arc::new(data), begin.elapsed())
}

fn bench_find(m: &Arc<RwLock<(Vec<i64>, Vec<i64>)>>, d: &Arc<Vec<i64>>) -> Duration {
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
          match m.0.binary_search(&d[j]) {
            Ok(i) => assert_eq!(m.1[i], d[j]),
            Err(_) => panic!("lookup failed")
          }
        }
      });
    threads.push(th);
  }
  for th in threads { th.join().unwrap(); }
  begin.elapsed()
}

fn bench_find_seq(m: &Arc<RwLock<(Vec<i64>, Vec<i64>)>>, d: &Vec<i64>) -> Duration {
  let begin = Instant::now();
  let m = m.read().unwrap();
  for k in d {
    match m.0.binary_search(k) {
      Ok(i) => assert_eq!(m.1[i], *k),
      Err(_) => panic!("lookup failed")
    }
  }
  begin.elapsed()
}

#[allow(dead_code)]
fn bench_remove(m: &Arc<RwLock<(Vec<i64>, Vec<i64>)>>, d: &Vec<i64>) -> Duration {
  let begin = Instant::now();
  let mut m = m.write().unwrap();
  for k in d {
    match m.0.binary_search(k) {
      Ok(i) => {
        m.0.remove(i);
        m.1.remove(i);
      },
      Err(_) => panic!("lookup failed")
    }
  }
  begin.elapsed()
}

pub(crate) fn run(size: usize) -> () {
  let (m, d) = create(size);
  let find_par = bench_find(&m, &d);
  let find = bench_find_seq(&m, &d);
  println!("add: {}ns, find: {}ns, find_par: {}ns, remove: {}ns", 
    0, utils::to_ns_per(find, size),
    utils::to_ns_per(find_par, size), 0);
}
