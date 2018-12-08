extern crate immutable_chunkmap;
extern crate num_cpus;
use self::immutable_chunkmap::map::Map;
use std::cmp::min;
use std::thread;
use std::sync::Arc;
use std::time::{Duration, Instant};
use std::vec::{Vec};
use utils;

fn bench_insert_many(len: usize) -> (Arc<Map<i32, i32>>, Arc<Vec<i32>>, Duration) {
    let mut m = Map::new();
    let data = utils::randvec::<i32>(len);
    let chunks = 100;
    let elapsed = {
        let mut i = 0;
        let mut chunk = Vec::with_capacity(len / chunks);
        let begin = Instant::now();
        while i < len {
            chunk.clear();
            for _ in 0..(len / chunks) {
                if i < len { chunk.push(data[i]); }
                i += 1
            }
            //chunk.sort_unstable();
            m = m.insert_many(chunk.iter().map(|k| (*k, *k)));
        }
        begin.elapsed()
    };
    (Arc::new(m), Arc::new(data), elapsed)
}

fn bench_insert(data: &Arc<Vec<i32>>) -> Duration {
    let mut m = Map::new();
    let begin = Instant::now();
    for k in data.iter() { m = m.insert(k, k).0; }
    begin.elapsed()
}

fn bench_get(m: Arc<Map<i32, i32>>, d: Arc<Vec<i32>>) -> Duration {
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
                    m.get(&d[j]).unwrap();
                }
            });
        threads.push(th);
    }
    for th in threads { th.join().unwrap(); }
    begin.elapsed()
}

fn bench_get_seq(m: Arc<Map<i32, i32>>, d: Arc<Vec<i32>>) -> Duration {
    let begin = Instant::now();
    for k in d.iter() { m.get(k).unwrap(); }
    begin.elapsed()
}

fn bench_remove(m: Arc<Map<i32, i32>>, d: Arc<Vec<i32>>) -> Duration {
    let mut m = (*m).clone();
    let begin = Instant::now();
    for kv in d.iter() { m = m.remove(&kv).0 }
    begin.elapsed()
}

pub(crate) fn run(size: usize) -> () {
    let (m, d, inserts) = bench_insert_many(size);
    let insert = bench_insert(&d);
    let get_par = bench_get(m.clone(), d.clone());
    let get = bench_get_seq(m.clone(), d.clone());
    let rm = bench_remove(m.clone(), d.clone());
    println!("{},{},{},{},{},{}",
             size,
             utils::to_ns_per(insert, size),
             utils::to_ns_per(inserts, size),
             utils::to_ns_per(get, size),
             utils::to_ns_per(get_par, size),
             utils::to_ns_per(rm, size));
}
