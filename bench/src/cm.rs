use immutable_chunkmap::cached_map::Map;
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
    let csize = max(1, len / 100);
    let mut chunks = vec![];
    let mut i = 0;
    while i < data.len() {
        let mut cur = vec![];
        while i < data.len() && cur.len() < csize {
            cur.push((data[i], data[i]));
            i += 1;
        }
        chunks.push(cur);
    }
    let begin = Instant::now();
    for chunk in chunks.drain(0..) {
        m = m.insert_many(chunk);
    }
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
    let iter = max(MIN_ITER, d.len());
    let mut threads = vec![];
    for n in 0..n {
        let (m, d) = (m.clone(), d.clone());
        threads.push(thread::spawn(move || {
            let mut r = 0;
            while r < iter {
                let mut j = n;
                while j < d.len() && r < iter {
                    m.get(&d[j]).unwrap();
                    j += n;
                    r += 1;
                }
            }
        }))
    }
    for th in threads {
        th.join().unwrap();
    }
    begin.elapsed()
}

fn bench_get_seq(m: Arc<Map<i32, i32>>, d: Arc<Vec<i32>>) -> Duration {
    let begin = Instant::now();
    let mut i = 0;
    let iter = max(MIN_ITER, d.len()); 
    while i < iter {
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
    let n = min(d.len() / 2, n);
    let insert = bench_insert(d.clone());
    let get_par = bench_get(m.clone(), d.clone(), n);
    let get = bench_get_seq(m.clone(), d.clone());
    let rm = bench_remove(m.clone(), d.clone());
    let iter = max(MIN_ITER, size);
    let iterp = max(MIN_ITER * n, size * n);
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
