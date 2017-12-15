extern crate immutable;
extern crate num_cpus;
use self::immutable::arc::map::Map;
use std::cmp::min;
use std::thread;
use std::sync::Arc;
use std::time::{Duration, Instant};
use std::vec::{Vec};
use utils;

fn bench_add_sorted(len: usize) -> (Arc<Map<i64, i64>>, Arc<Vec<i64>>, Duration) {
  let mut m = Map::new();
  let data = utils::randvec::<i64>(len);
  let elapsed = {
    let mut pairs : Vec<(&i64, &i64)> = data.iter().map(|k| (k, k)).collect();
    let begin = Instant::now();
    pairs.sort_unstable_by(|&(k0, _), &(k1, _)| k0.cmp(k1));
    m = m.add_sorted(&pairs);
    begin.elapsed()
  };
  (Arc::new(m), Arc::new(data), elapsed)
}

fn bench_add(data: &Arc<Vec<i64>>) -> Duration {
  let mut m = Map::new();
  let begin = Instant::now();
  for k in data.iter() { m = m.add(k, k); }
  begin.elapsed()
}

fn bench_find(m: Arc<Map<i64, i64>>, d: Arc<Vec<i64>>) -> Duration {
  let n = num_cpus::get();
  let chunk = d.len() / n;
  let mut threads = Vec::new();
  let begin = Instant::now();
  for i in 0 .. n {
    let (m, d) = (m.clone(), d.clone());
    let th = 
      thread::spawn(move || {
        let p = i * chunk;
        for j in p .. min(d.len() - 1, p + chunk) {
          m.find(&d[j]).unwrap();
        }
      });
    threads.push(th);
  }
  for th in threads { th.join().unwrap(); }
  begin.elapsed()
}

fn bench_find_seq(m: Arc<Map<i64, i64>>, d: Arc<Vec<i64>>) -> Duration {
  let begin = Instant::now();
  for k in d.iter() { m.find(k).unwrap(); }
  begin.elapsed()
}

fn bench_remove(m: Arc<Map<i64, i64>>, d: Arc<Vec<i64>>) -> Duration {
  let mut m = (*m).clone();
  let begin = Instant::now();
  for kv in d.iter() { m = m.remove(&kv) }
  begin.elapsed()
}

pub(crate) fn run(size: usize) -> () {
  let (m, d, adds) = bench_add_sorted(size);
  let add = bench_add(&d);
  let find_par = bench_find(m.clone(), d.clone());
  let find = bench_find_seq(m.clone(), d.clone());
  let rm = bench_remove(m.clone(), d.clone());
  println!("add: {}, adds: {}, find: {}, find_par: {}, remove: {}", 
    utils::to_ms(add), utils::to_ms(adds), utils::to_ms(find), 
    utils::to_ms(find_par), utils::to_ms(rm));
}
