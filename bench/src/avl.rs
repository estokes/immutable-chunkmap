use immutable_map::TreeMap;
use std::time::{Duration, Instant};
use std::vec::{Vec};
use crate::utils;

fn bench_insert(len: usize) -> (TreeMap<i64, i64>, Vec<i64>, Duration) {
    let mut m = TreeMap::new();
    let data = utils::randvec::<i64>(len);
    let begin = Instant::now();
    for kv in &data { m = m.insert(*kv, *kv) }
    (m, data, begin.elapsed())
}

fn bench_insert_sorted(len: usize) -> (TreeMap<i64, i64>, Vec<i64>, Duration) {
    let mut m = TreeMap::new();
    let mut data = utils::randvec::<i64>(len);
    let begin = Instant::now();
    data.sort_unstable();
    for kv in &data { m = m.insert(*kv, *kv) }
    (m, data, begin.elapsed())
}

fn bench_get(m: &TreeMap<i64, i64>, d: &Vec<i64>) -> Duration {
    let begin = Instant::now();
    for kv in d { m.get(&kv).unwrap(); }
    begin.elapsed()
}

fn bench_remove(m: TreeMap<i64, i64>, d: &Vec<i64>) -> Duration {
    let mut m = m;
    let begin = Instant::now();
    for kv in d {
        match m.remove(&kv) {
            Option::None => (),
            Option::Some((r, _)) => m = r
        }
    }
    begin.elapsed()
}

pub(crate) fn run(size: usize) {
    let (m, d, insert) = bench_insert(size);
    let (_, _, inserts) = bench_insert_sorted(size);
    let get = bench_get(&m, &d);
    let rm = bench_remove(m, &d);
    println!("{},{},{},{},0,{}",
             size,
             utils::to_ns_per(insert, size),
             utils::to_ns_per(inserts, size),
             utils::to_ns_per(get, size),
             utils::to_ns_per(rm, size));
}
