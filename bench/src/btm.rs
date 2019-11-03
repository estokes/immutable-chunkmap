use std::cmp::{min, max};
use std::collections::BTreeMap;
use std::sync::{Arc, RwLock};
use std::thread;
use std::time::{Duration, Instant};
use std::vec::Vec;
use crate::utils;

const MIN_ITER: usize = 1000000;

fn bench_insert(
    len: usize,
) -> (Arc<RwLock<BTreeMap<i64, i64>>>, Arc<Vec<i64>>, Duration) {
    let mut m = BTreeMap::new();
    let data = utils::randvec::<i64>(len);
    let begin = Instant::now();
    for k in &data {
        m.insert(*k, *k);
    }
    (Arc::new(RwLock::new(m)), Arc::new(data), begin.elapsed())
}

fn bench_insert_sorted(
    len: usize,
) -> (Arc<RwLock<BTreeMap<i64, i64>>>, Arc<Vec<i64>>, Duration) {
    let mut m = BTreeMap::new();
    let mut data = utils::randvec::<i64>(len);
    let begin = Instant::now();
    data.sort_unstable();
    for k in &data {
        m.insert(*k, *k);
    }
    (Arc::new(RwLock::new(m)), Arc::new(data), begin.elapsed())
}

fn bench_get(m: &Arc<RwLock<BTreeMap<i64, i64>>>, d: &Arc<Vec<i64>>, n: usize) -> Duration {
    let chunk = d.len() / n;
    let mut threads = Vec::new();
    let begin = Instant::now();
    for i in 0..n {
        let (m, d) = (m.clone(), d.clone());
        let th = thread::spawn(move || {
            let m = m.read().unwrap();
            let p = i * chunk;
            let mut r = 0;
            while r < MIN_ITER {
                for j in p..min(d.len() - 1, p + chunk) {
                    r += 1;
                    m.get(&d[j]).unwrap();
                }
            }
        });
        threads.push(th);
    }
    for th in threads {
        th.join().unwrap();
    }
    begin.elapsed()
}

fn bench_get_seq(m: &Arc<RwLock<BTreeMap<i64, i64>>>, d: &Vec<i64>) -> Duration {
    let begin = Instant::now();
    let m = m.read().unwrap();
    let mut i = 0;
    while i < MIN_ITER {
        for k in d {
            i += 1;
            m.get(k).unwrap();
        }
    }
    begin.elapsed()
}

fn bench_remove(m: &Arc<RwLock<BTreeMap<i64, i64>>>, d: &Vec<i64>) -> Duration {
    let begin = Instant::now();
    let mut m = m.write().unwrap();
    for k in d {
        m.remove(k).unwrap();
    }
    begin.elapsed()
}

pub(crate) fn run(size: usize) -> () {
    let n = num_cpus::get();
    let (mut m, d, insert) = bench_insert(size);
    let (_, _, inserts) = bench_insert_sorted(size);
    let get_par = bench_get(&m, &d, n);
    let get = bench_get_seq(&m, &d);
    let rm = bench_remove(&mut m, &d);
    let iter = max(MIN_ITER, size);
    let iterp = max(MIN_ITER * n, size);
    println!(
        "{},{:.0},{:.0},{:.0},{:.2},{:.0}",
        size,
        utils::to_ns_per(insert, size),
        utils::to_ns_per(inserts, size),
        utils::to_ns_per(get, iter),
        utils::to_ns_per(get_par, iterp),
        utils::to_ns_per(rm, size)
    );
}
