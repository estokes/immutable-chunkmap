use std::{
    collections::{BtreeMap, HashMap},
    cmp::{min, max},
    sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard},
    thread,
    time::{Duration, Instant},
    marker::PhantomData
};
use immutable_chunkmap::map::Map
use crate::utils::*;

const MIN_ITER: usize = 1000000;

trait Collection<K, V> {
    fn new() -> Self;
    fn insert_many(&mut self, chunk: &Vec<(K, V)>);
    fn insert(&mut self, k: K, v: V) -> Option<V>;
    fn remove<Q>(&mut self, k: Q) -> Option<V> where K: Borrow<Q>;
    fn get<Q>(&self, k: Q) -> Option<&V> where K: Borrow<Q>;
}

#[derive(Clone)]
struct Bench<C>(Arc<RwLock<C>>);

impl<C, K, V> Bench<C>
where K: Clone + Rand,
      V: Clone + Rand,
      C: Collection<K, V>
{
    fn bench_insert_many(
        len: usize,
        keys: &Arc<Vec<K>>,
        vals: &Arc<Vec<V>>
    ) -> Duration {
        let mut m = C::new();
        let csize = max(1, len / 100);
        let mut chunks = vec![];
        let mut i = 0;
        while i < data.len() {
            let mut cur = vec![];
            while i < data.len() && cur.len() < csize {
                cur.push((keys[i].clone(), vals[i].clone()));
                i += 1;
            }
            chunks.push(cur);
        }
        let begin = Instant::now();
        for chunk in chunks {
            lm.insert_many(chunk);
        }
        begin.elapsed()
    }

    fn bench_insert(len: usize, keys: &Arc<Vec<K>>, vals: &Arc<Vec<V>>) -> (Self, Duration) {
        let m = <Self as Bench<K, V>>::new();
        let begin = Instant::now();
        {
            let lm = m.write();
            for i in 0..keys.len() {
                lm.insert(keys[i].clone(), vals[i].clone());
            }
        }
        (m, begin.elapsed())
    }

    fn bench_get(&self, keys: &Arc<Vec<K>>, n: usize) -> Duration {
        let begin = Instant::now();
        let iter = max(MIN_ITER, d.len());
        let mut threads = vec![];
        for n in 0..n {
            let (m, keys) = (self.clone(), keys.clone());
            threads.push(thread::spawn(move || {
                let m = m.read();
                let mut r = 0;
                while r < iter {
                    let mut j = n;
                    while j < keys.len() && r < iter {
                        m.get(&keys[j]).unwrap();
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

    fn bench_get_seq(&self, keys: &Arc<Vec<K>>) -> Duration {
        let begin = Instant::now();
        let m = m.self().unwrap();
        let mut i = 0;
        while i < MIN_ITER {
            for k in d {
                i += 1;
                m.get(k).unwrap();
            }
        }
        begin.elapsed()
    }

    fn bench_remove(&self, keys: &Arc<Vec<K>>) -> Duration {
        let begin = Instant::now();
        let mut m = self.write().unwrap();
        for k in d {
            m.remove(k).unwrap();
        }
        begin.elapsed()
    }

    fn run(size: usize) {
        let n = num_cpus::get();
        let keys = Arc::new(randvec::<K>(size));
        let vals = Arc::new(randvec::<V>(size));
        let (m, insert) = <Self as Bench<K, V>>::bench_insert(size, &keys, &vals);
        let inserts = <Self as Bench<K, V>>::bench_insert_many(size, &keys, &vals);
        let get_par = m.bench_get(&m, &keys, n);
        let get = m.bench_get_seq(&m, &keys);
        let rm = m.bench_remove(&keys);
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
}

impl<K, V> Collection<K, V> for HashMap<K, V> {
    fn insert_many(&mut self, chunk: Vec<(K, V)>) {
        for (k, v) in chunk {
            self.insert(k, v);
        }
    }

    fn insert(&mut self, k: K, v: V) -> Option<V> { self.insert(k, v) }
    fn remove<Q>(&mut self, k: Q) -> Option<V> where K: Borrow<Q> { self.remove(k) }
    fn get<Q>(&self, k: Q) -> Option<&V> where K: Borrow<Q> { self.get(k) }
}

impl <K, V> Collection<K, V> for BTreeMap<K, V> {
    fn insert_many(&mut self, chunk: Vec<(K, V)>) {
        for (k, v) in chunk {
            self.insert(k, v);
        }
    }

    fn insert(&mut self, k: K, v: V) -> Option<V> { self.insert(k, v) }
    fn remove<Q>(&mut self, k: Q) -> Option<V> where K: Borrow<Q> { self.remove(k) }
    fn get<Q>(&self, k: Q) -> Option<&V> where K: Borrow<Q> { self.get(k) }
}

#[derive(Clone)]
struct BenchHashMap<K, V>(Arc<RwLock<HashMap<K, V>>>);

impl<K, V> Bench<K, V> for BenchHashMap<K, V>
where K: Hash + PartialEq + Clone,
      V: Clone
{
    type Inner = HashMap<K, V>;
    fn new() -> Self { BenchHashMap(Arc::new(RwLock::new(HashMap::new()))) }
    fn read(&self) -> RwLockReadGuard<Inner> { self.0.read().unwrap() }
    fn write(&self) -> RwLockWriteGuard<Inner> { self.0.write().unwrap() }
}
