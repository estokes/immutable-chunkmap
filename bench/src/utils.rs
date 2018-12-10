extern crate rand;
use self::rand::{
    distributions::{Distribution, Standard},
    random,
};
use std::time::Duration;
use std::vec::Vec;

pub(crate) fn randvec<T>(len: usize) -> Vec<T>
where
    Standard: Distribution<T>,
{
    let mut v: Vec<T> = Vec::new();
    for _ in 0..len {
        v.push(random())
    }
    v
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

pub(crate) fn permute<T: Clone>(v: &Vec<T>) -> Vec<T> {
    let pos = randvec::<usize>(v.len());
    let mut res = Vec::new();
    for i in 0..v.len() {
        res.push((pos[i], v[i].clone()));
    }
    res.sort_unstable_by_key(|&(k, _)| k);
    res.iter().map(|&(_, ref v)| v.clone()).collect()
}
