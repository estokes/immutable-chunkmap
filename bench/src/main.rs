extern crate immutable_avl;
extern crate rand;
use immutable_avl::map;
use std::time::{Duration, Instant};
use rand::{random, Rand};
use std::env;
use std::iter::FromIterator;
use std::vec::{Vec};

fn randvec<T: Rand>(len: usize) -> Vec<T> {
  let mut v: Vec<T> = Vec::new();
  for _ in 0..len { v.push(random()) }
  v
}

fn bench_add(len: usize) -> (map::Map<i64, i64>, Vec<i64>, Duration) {
    let mut m = map::Map::new();
    let data = randvec::<i64>(len);
    let begin = Instant::now();
    for kv in &data { m = m.add(kv, kv) }
    (m, data, begin.elapsed())
}

fn bench_find(m: &map::Map<i64, i64>, d: &Vec<i64>) -> Duration {
    let begin = Instant::now();
    for kv in d { m.find(&kv).unwrap(); }
    begin.elapsed()
}

fn bench_remove(m: map::Map<i64, i64>, d: &Vec<i64>) -> Duration {
    let mut m = m;
    let begin = Instant::now();
    for kv in d { m = m.remove(&kv) }
    begin.elapsed()
}

fn to_ms(t: Duration) -> u64 {
    t.as_secs() * 1000 + ((t.subsec_nanos() / 1000000) as u64)
}

fn main() {
    let args = Vec::from_iter(env::args());
    let size =
        if args.len() == 2 { args[1].parse::<usize>().unwrap() }
        else { 10000 };
    let (m, d, add) = bench_add(size);
    let find = bench_find(&m, &d);
    let rm = bench_remove(m, &d);
    println!("add: {}, find: {}, remove: {}", 
        to_ms(add), to_ms(find), to_ms(rm));
}
