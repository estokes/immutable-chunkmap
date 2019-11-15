use rand::Rng;
use std::{
    time::Duration,
    sync::Arc,
    collections::HashSet,
    hash::Hash,
    convert::TryFrom,
};
use arccstr::ArcCStr;

const STRSIZE: usize = 32;

pub(crate) trait Rand: Sized {
    fn rand<R: Rng>(r: &mut R) -> Self;
}

impl<T: Rand, U: Rand> Rand for (T, U) {
    fn rand<R: Rng>(r: &mut R) -> Self {
        (T::rand(r), U::rand(r))
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

impl Rand for Arc<String> {
    fn rand<R: Rng>(r: &mut R) -> Self {
        let mut s = String::new();
        for _ in 0..STRSIZE {
            s.push(r.gen())
        }
        Arc::new(s)
    }
}

impl Rand for ArcCStr {
    fn rand<R: Rng>(r: &mut R) -> Self {
        let mut s: Vec<u8> = Vec::new();
        while s.len() < STRSIZE {
            let v = r.gen();
            if v != 0 {
                s.push(v)
            }
        }
        ArcCStr::try_from(&s[0..]).unwrap()
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

pub(crate) fn randvec<T: Ord + Clone + Hash + Rand>(len: usize) -> Vec<T> {
    let mut v: Vec<T> = Vec::new();
    loop {
        for _ in 0..len {
            v.push(random())
        }
        dedup_with(&mut v, |k| k);
        if v.len() >= len {
            while v.len() > len {
                v.pop();
            }
            break v;
        }
    }
}

fn dedup_with<K, T, F>(v: &mut Vec<T>, f: F)
where F: Fn(&T) -> &K,
      K: Ord + Clone + Hash,
{
    let mut seen = HashSet::new();
    let mut i = 0;
    while i < v.len() {
        if seen.contains(f(&v[i])) {
            v.remove(i);
        } else {
            seen.insert(f(&v[i]).clone());
            i += 1
        }
    }
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
