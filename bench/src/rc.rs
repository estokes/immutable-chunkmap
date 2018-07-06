extern crate immutable_chunkmap;
use self::immutable_chunkmap::rc::map::Map;
use std::time::{Duration, Instant};
use std::vec::{Vec};
use utils;

fn bench_insert_sorted(len: usize) -> (Map<i64, i64>, Vec<i64>, Duration) {
    let mut m = Map::new();
    let data = utils::randvec::<i64>(len);
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
            chunk.sort_unstable();
            m = m.insert_sorted(chunk.iter().map(|k| (*k, *k)));
        }
        begin.elapsed()
    };
    (m, data, elapsed)
}

fn bench_insert(data: &Vec<i64>) -> Duration {
    let mut m = Map::new();
    let begin = Instant::now();
    for k in data { m = m.insert(k, k).0; }
    begin.elapsed()
}

fn bench_get(m: &Map<i64, i64>, d: &Vec<i64>) -> Duration {
    let begin = Instant::now();
    for kv in d { m.get(&kv).unwrap(); }
    begin.elapsed()
}

fn bench_remove(m: Map<i64, i64>, d: &Vec<i64>) -> Duration {
    let mut m = m;
    let begin = Instant::now();
    for kv in d { m = m.remove(&kv) }
    begin.elapsed()
}

pub(crate) fn run(size: usize) -> () {
    let (m, d, insert_sorted) = bench_insert_sorted(size);
    let insert = bench_insert(&d);
    let get = bench_get(&m, &d);
    let rm = bench_remove(m, &d);
    println!("{},{},{},{},0,{}",
             size,
             utils::to_ns_per(insert, size),
             utils::to_ns_per(insert_sorted, size),
             utils::to_ns_per(get, size),
             utils::to_ns_per(rm, size));
}
