mod utils;
use std::{
    env, mem, thread,
    borrow::Borrow,
    cmp::max,
    collections::{BTreeMap, HashMap},
    hash::Hash,
    iter::FromIterator,
    marker::PhantomData,
    sync::{Arc, RwLock, mpsc::channel},
    time::{Duration, Instant},
};
use arccstr::ArcCStr;
use immutable_chunkmap::map::Map;
use crate::utils::Rand;

const MIN_ITER: usize = 1000000;

trait Collection<K, V> {
    fn new() -> Self;
    fn insert_many(&mut self, chunk: Vec<(K, V)>);
    fn insert(&mut self, k: K, v: V) -> Option<V>;
    fn remove<Q>(&mut self, k: &Q) -> Option<V> where Q: Ord + Hash, K: Borrow<Q>;
    fn get<Q>(&self, k: &Q) -> Option<&V> where Q: Ord + Hash, K: Borrow<Q>;
    fn merge_into(&mut self, from: Self);
    fn len(&self) -> usize;
}

fn chunk<K, V>(keys: &Vec<K>, vals: &Vec<V>, denom: usize) -> Vec<Vec<(K, V)>>
where K: Clone,
      V: Clone
{
    let csize = max(1, keys.len() / denom);
    let mut chunks = vec![];
    let mut cur = vec![];
    for (k, v) in keys.into_iter().zip(vals.into_iter()) {
        cur.push((k.clone(), v.clone()));
        if cur.len() >= csize {
            chunks.push(mem::replace(&mut cur, vec![]));
        }
    }
    if cur.len() > 0 {
        chunks.push(cur);
    }
    chunks
}

#[derive(Clone)]
struct Bench<C, K, V>(Arc<RwLock<C>>, PhantomData<K>, PhantomData<V>);

impl<C, K, V> Bench<C, K, V>
where K: Hash + Ord + Clone + Rand + Send + Sync + 'static,
      V: Hash + Ord + Clone + Rand + Send + Sync + 'static,
      C: Collection<K, V> + Send + Sync + 'static,
{
    fn bench_insert_many(
        keys: &Vec<K>,
        vals: &Vec<V>
    ) -> (Self, Duration) {
        let mut m = C::new();
        let chunks = chunk(keys, vals, 100);
        let begin = Instant::now();
        for chunk in chunks {
            m.insert_many(chunk);
        }
        (Bench(Arc::new(RwLock::new(m)), PhantomData, PhantomData), begin.elapsed())
    }

    fn bench_insert_many_par(
        keys: &Vec<K>,
        vals: &Vec<V>,
        n: usize
    ) -> (Self, Duration) {
        let mut chunks = chunk(keys, vals, n - 1);
        let len = chunks.len();
        let (tx, rx) = channel();
        let begin = Instant::now();
        let mine = chunks.pop().unwrap();
        for chunk in chunks {
            let tx = tx.clone();
            thread::spawn(move || {
                let mut t = C::new();
                t.insert_many(chunk);
                tx.send(t).unwrap();
            });
        }
        mem::drop(tx);
        let mut t = C::new();
        let mut i = 0;
        t.insert_many(mine);
        while let Ok(part) = rx.recv() {
            t.merge_into(part);
            i += 1;
        }
        assert_eq!(i, len - 1);
        assert_eq!(t.len(), keys.len());
        (Bench(Arc::new(RwLock::new(t)), PhantomData, PhantomData),
         begin.elapsed())
    }

    fn bench_remove(&self, keys: &Arc<Vec<K>>) -> Duration {
        let begin = Instant::now();
        let mut m = self.0.write().unwrap();
        for i in 0..(keys.len() / 10) {
            m.remove(&keys[i]).unwrap();
        }
        begin.elapsed()
    }

    fn bench_insert(&self, keys: &Vec<K>, vals: &Vec<V>) -> Duration {
        let begin = Instant::now();
        let mut m = self.0.write().unwrap();
        for i in 0..(keys.len() / 10) {
            m.insert(keys[i].clone(), vals[i].clone());
        }
        begin.elapsed()
    }

    fn bench_get(&self, keys: &Arc<Vec<K>>, n: usize) -> Duration {
        let begin = Instant::now();
        let iter = max(MIN_ITER, keys.len());
        let mut threads = vec![];
        for n in 0..n {
            let (m, keys) = (self.0.clone(), keys.clone());
            threads.push(thread::spawn(move || {
                let m = m.read().unwrap();
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
        let m = self.0.read().unwrap();
        let mut i = 0;
        while i < MIN_ITER {
            for k in keys.iter() {
                i += 1;
                m.get(k).unwrap();
            }
        }
        begin.elapsed()
    }

    pub(crate) fn run(size: usize) {
        let n = num_cpus::get();
        let keys = Arc::new(utils::randvec::<K>(size));
        let vals = Arc::new(utils::randvec::<V>(size));
        let (m, insertm) = Self::bench_insert_many(&*keys, &*vals);
        let rm = m.bench_remove(&keys);
        let insert = m.bench_insert(&*keys, &*vals);
        let (m, insertmp) = Self::bench_insert_many_par(&*keys, &*vals, n);
        let get_par = m.bench_get(&keys, n);
        let get = m.bench_get_seq(&keys);
        let iter = max(MIN_ITER, size);
        let iterp = max(MIN_ITER * n, size * n);
        println!(
            "{},{:.0},{:.0},{:.0},{:.0},{:.2},{:.0}",
            size,
            utils::to_ns_per(insert, size / 10),
            utils::to_ns_per(insertm, size),
            utils::to_ns_per(insertmp, size),
            utils::to_ns_per(get, iter),
            utils::to_ns_per(get_par, iterp),
            utils::to_ns_per(rm, size / 10)
        );
    }
}

impl<K, V> Collection<K, V> for HashMap<K, V>
where K: Hash + Ord + Clone + Rand + Send + Sync,
      V: Hash + Ord + Clone + Rand + Send + Sync
{
    fn new() -> Self { HashMap::new() }
    fn insert_many(&mut self, chunk: Vec<(K, V)>) {
        for (k, v) in chunk {
            self.insert(k, v);
        }
    }
    fn insert(&mut self, k: K, v: V) -> Option<V> { self.insert(k, v) }
    fn remove<Q>(&mut self, k: &Q) -> Option<V> where Q: Ord + Hash, K: Borrow<Q> {
        self.remove(k)
    }
    fn get<Q>(&self, k: &Q) -> Option<&V> where Q: Ord + Hash, K: Borrow<Q> {
        self.get(k)
    }
    fn merge_into(&mut self, other: HashMap<K, V>) {
        self.extend(other.into_iter());
    }
    fn len(&self) -> usize { self.len() }
}

impl <K, V> Collection<K, V> for BTreeMap<K, V>
where K: Hash + Ord + Clone + Rand + Send + Sync,
      V: Hash + Ord + Clone + Rand + Send + Sync
{
    fn new() -> Self { BTreeMap::new() }
    fn insert_many(&mut self, chunk: Vec<(K, V)>) {
        for (k, v) in chunk {
            self.insert(k, v);
        }
    }
    fn insert(&mut self, k: K, v: V) -> Option<V> { self.insert(k, v) }
    fn remove<Q>(&mut self, k: &Q) -> Option<V> where Q: Ord + Hash, K: Borrow<Q> {
        self.remove(k)
    }
    fn get<Q>(&self, k: &Q) -> Option<&V> where Q: Ord + Hash, K: Borrow<Q> {
        self.get(k)
    }
    fn merge_into(&mut self, other: BTreeMap<K, V>) {
        self.extend(other.into_iter())
    }
    fn len(&self) -> usize { self.len() }
}

struct CMWrap<K: Ord + Clone, V: Clone>(Map<K, V>);

impl<K, V> Collection<K, V> for CMWrap<K, V>
where K: Hash + Ord + Clone + Rand + Send + Sync,
      V: Hash + Ord + Clone + Rand + Send + Sync
{
    fn new() -> Self { CMWrap(Map::new()) }
    fn insert_many(&mut self, chunk: Vec<(K, V)>) { self.0 = self.0.insert_many(chunk) }
    fn insert(&mut self, k: K, v: V) -> Option<V> {
        let (m, prev) = self.0.insert(k, v);
        self.0 = m;
        prev
    }
    fn remove<Q>(&mut self, k: &Q) -> Option<V> where Q: Ord + Hash, K: Borrow<Q> {
        let (m, prev) = self.0.remove(k);
        self.0 = m;
        prev
    }
    fn get<Q>(&self, k: &Q) -> Option<&V> where Q: Ord + Hash, K: Borrow<Q> {
        self.0.get(k)
    }
    fn merge_into(&mut self, other: CMWrap<K, V>) {
        self.0 = self.0.union(&other.0, |_, _, v| Some(v.clone()))
    }
    fn len(&self) -> usize { self.0.len() }
}

fn usage() {
    println!("usage: <cm|btm|hm> <ptr|str> <size>")
}

type S = ArcCStr;
type P = usize;

fn main() {
    let args = Vec::from_iter(env::args());
    if args.len() != 4 { usage() }
    else {
        let size = args[3].parse::<usize>().unwrap();
        match (args[1].as_ref(), args[2].as_ref()) {
            ("cm", "ptr") => Bench::<CMWrap<P, P>, P, P>::run(size),
            ("cm", "str") => Bench::<CMWrap<S, S>, S, S>::run(size),
            ("btm", "ptr") => Bench::<BTreeMap<P, P>, P, P>::run(size),
            ("btm", "str") => Bench::<BTreeMap<S, S>, S, S>::run(size),
            ("hm", "ptr") => Bench::<HashMap<P, P>, P, P>::run(size),
            ("hm", "str") => Bench::<HashMap<S, S>, S, S>::run(size),
            _ => usage() 
        }
    }
}
