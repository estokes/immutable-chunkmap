use rand::Rng;
use smallvec::SmallVec;
use std::{
    time::Duration,
    sync::{Arc, mpsc::channel},
    collections::HashSet,
    hash::Hash,
    iter::FromIterator,
    thread, mem,
};

pub(crate) const STRSIZE: usize = 32;

pub(crate) trait Rand: Sized {
    fn rand<R: Rng>(r: &mut R) -> Self;
}

impl<T: Rand, U: Rand> Rand for (T, U) {
    fn rand<R: Rng>(r: &mut R) -> Self {
        (T::rand(r), U::rand(r))
    }
}

impl Rand for SmallVec<[u8; STRSIZE]> {
    fn rand<R: Rng>(r: &mut R) -> Self {
        let mut v = SmallVec::<[u8; STRSIZE]>::new();
        for _ in 0..STRSIZE {
            v.push(r.gen())
        }
        v
    }
}

impl Rand for String {
    fn rand<R: Rng>(r: &mut R) -> Self {
        let mut s = String::new();
        for _ in 0..STRSIZE {
            s.push(r.gen())
        }
        s
    }
}

impl Rand for Vec<u8> {
    fn rand<R: Rng>(r: &mut R) -> Self {
        let mut s: Vec<u8> = Vec::with_capacity(STRSIZE);
        for _ in 0..STRSIZE {
            s.push(r.gen())
        }
        s
    }
}

impl<T: Rand> Rand for Arc<T> {
    fn rand<R: Rng>(r: &mut R) -> Self {
        Arc::new(<T as Rand>::rand(r))
    }
}

impl Rand for i32 {
    fn rand<R: Rng>(r: &mut R) -> Self {
        r.gen()
    }
}

impl Rand for usize {
    fn rand<R: Rng>(r: &mut R) -> Self {
        r.gen()
    }
}

pub(crate) fn random<T: Rand>() -> T {
    let mut rng = rand::thread_rng();
    T::rand(&mut rng)
}

pub(crate) fn randvec<T>(n: usize, len: usize) -> Vec<T>
where T: Ord + Clone + Hash + Rand + Send + 'static
{
    let csize = len / n;
    let (tx, rx) = channel();
    for _ in 0..n - 1 {
        let tx = tx.clone();
        thread::spawn(move || {
            let mut v: HashSet<T> = HashSet::with_capacity(csize);
            while v.len() < csize {
                v.insert(random());
            }
            tx.send(v).unwrap()
        });
    }
    mem::drop(tx);
    let mut v: HashSet<T> = HashSet::with_capacity(len);
    while v.len() < csize {
        v.insert(random());
    }
    while let Ok(c) = rx.recv() {
        v.extend(c.into_iter())
    }
    while v.len() < len {
        v.insert(random());
    }
    Vec::from_iter(v.into_iter())
}

#[allow(dead_code)]
pub(crate) fn to_ms(t: Duration) -> u64 {
    t.as_secs() * 1000 + ((t.subsec_nanos() / 1000000) as u64)
}

#[allow(dead_code)]
pub(crate) fn to_us(t: Duration) -> u64 {
    t.as_secs() * 1000000 + ((t.subsec_nanos() / 1000) as u64)
}

pub(crate) fn to_ns(t: Duration) -> u64 {
    t.as_secs() * 1000000000 + (t.subsec_nanos() as u64)
}

pub(crate) fn to_ns_per(t: Duration, n: usize) -> f64 {
    (to_ns(t) as f64) / (n as f64)
}
