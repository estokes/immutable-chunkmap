use immutable_chunkmap::map::Map;
use std::cmp::{min, max};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};
use std::vec::Vec;
use crate::utils;

const MIN_ITER: usize = 1000000;

fn bench_insert_many(len: usize) -> (Arc<Map<i64, i64>>, Arc<Vec<i64>>, Duration) {
    let mut m = Map::new();
    let data = utils::randvec::<i64>(len);
    let nchunks = 100;
    let elapsed = {
        let mut i = 0;
        let mut chunks = Vec::new();
        for _ in 0..nchunks {
            chunks.push(Vec::new());
        }
        for c in 0..nchunks {
            for _ in 0..(len / nchunks) {
                if i < len {
                    chunks[c].push(data[i]);
                }
                i += 1
            }
        }
        let begin = Instant::now();
        for chunk in chunks {
            m = m.insert_many(chunk.iter().map(|k| (*k, *k)));
        }
        begin.elapsed()
    };
    (Arc::new(m), Arc::new(data), elapsed)
}

fn bench_insert(data: &Arc<Vec<i64>>) -> (Arc<Map<i64, i64>>, Duration) {
    let mut m = Map::new();
    let begin = Instant::now();
    for k in data.iter() {
        m = m.insert(k, k).0;
    }
    (m, begin.elapsed())
}

fn bench_get(m: Arc<Map<i64, i64>>, d: Arc<Vec<i64>>, n: usize) -> Duration {
    let chunk = d.len() / n;
    let mut threads = Vec::new();
    let begin = Instant::now();
    for i in 0..n {
        let (m, d) = (m.clone(), d.clone());
        let th = thread::spawn(move || {
            let mut r = 0;
            let p = i * chunk;
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

fn bench_get_seq(m: Arc<Map<i64, i64>>, d: Arc<Vec<i64>>) -> Duration {
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

fn bench_remove(m: Arc<Map<i64, i64>>, d: Arc<Vec<i64>>) -> Duration {
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
    let insert = bench_insert(&d);
    let get_par = bench_get(m.clone(), d.clone(), n);
    let get = bench_get_seq(m.clone(), d.clone());
    let rm = bench_remove(m.clone(), d.clone());
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
