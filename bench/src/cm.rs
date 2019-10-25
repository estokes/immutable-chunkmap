use immutable_chunkmap::map::Map;
use std::cmp::{max, min};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};
use std::vec::Vec;
use crate::utils;

const MIN_ITER: usize = 1000000;

fn bench_insert_many(len: usize) -> (Arc<Map<i32, i32>>, Arc<Vec<i32>>, Duration) {
    let mut m = Map::new();
    let data = utils::randvec::<i32>(len);
    let begin = Instant::now();
    m = m.insert_many(data.iter().map(|k| (*k, *k)));    
    (Arc::new(m), Arc::new(data), begin.elapsed())
}

fn bench_insert(data: Arc<Vec<i32>>) -> Duration {
    let mut m = Map::new();
    let begin = Instant::now();
    for k in data.iter() {
        m = m.insert(*k, *k).0;
    }
    begin.elapsed()
}

fn bench_get(m: Arc<Map<i32, i32>>, d: Arc<Vec<i32>>, n: usize) -> Duration {
    let begin = Instant::now();
    let n = min(d.len() / 2, n);
    (0..n).into_iter().map(|_| {
        let (m, d) = (m.clone(), d.clone());
        thread::spawn(move || {
            let mut r = 0;
            while r < (MIN_ITER / n) {
                let mut j = n;
                while j < d.len() {
                    m.get(&d[j]).unwrap();
                    j += n;
                    r += 1;
                }
            }
        })
    }).for_each(|th| th.join().unwrap());
    begin.elapsed()
}

fn bench_get_seq(m: Arc<Map<i32, i32>>, d: Arc<Vec<i32>>) -> Duration {
    let begin = Instant::now();
    let mut i = 0;
    while i < MIN_ITER {
        for k in d.iter() {
            i = i + 1;
            m.get(k).unwrap();
        }
    }
    begin.elapsed()
}

fn bench_remove(m: Arc<Map<i32, i32>>, d: Arc<Vec<i32>>) -> Duration {
    let mut m = (*m).clone();
    let begin = Instant::now();
    for kv in d.iter() {
        m = m.remove(&kv).0
    }
    begin.elapsed()
}

pub(crate) fn run(size: usize) -> () {
    let (m, d, inserts) = bench_insert_many(size);
    let n = num_cpus::get();
    let insert = bench_insert(d.clone());
    let get_par = bench_get(m.clone(), d.clone(), n);
    let get = bench_get_seq(m.clone(), d.clone());
    let rm = bench_remove(m.clone(), d.clone());
    let iter = max(MIN_ITER, size);
    let iterp = max(MIN_ITER * n, size);
    println!(
        "{},{:.1},{:.1},{:.1},{:.1},{:.1}",
        size,
        utils::to_ns_per(insert, size),
        utils::to_ns_per(inserts, size),
        utils::to_ns_per(get, iter),
        utils::to_ns_per(get_par, iterp),
        utils::to_ns_per(rm, size)
    );
}
