use crate::{avl, map::Map, set::Set};
use rand::Rng;
use std::{
    borrow::Borrow,
    cmp::Ordering,
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    i32,
    iter::{FromIterator, IntoIterator},
    ops::Bound::{Excluded, Included, Unbounded},
    sync::Arc,
    vec::Vec,
};

const STRSIZE: usize = 10;
const SIZE: usize = 500000;
const CHECK: usize = 50000;

macro_rules! make_tests {
    ($name:ident) => {
        $name::<i32, i32>();
        $name::<i32, usize>();
        $name::<usize, i32>();
        $name::<usize, usize>();
        $name::<i32, Arc<String>>();
        $name::<Arc<String>, i32>();
        $name::<usize, (Arc<String>, Arc<String>)>();
        $name::<(Arc<String>, Arc<String>), usize>();
    }
}

trait Rand: Sized {
    fn rand<R: Rng>(r: &mut R) -> Self;
}

impl<T: Rand, U: Rand> Rand for (T, U) {
    fn rand<R: Rng>(r: &mut R) -> Self {
        (T::rand(r), U::rand(r))
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

fn random<T: Rand>() -> T {
    let mut rng = rand::thread_rng();
    T::rand(&mut rng)
}

fn randvec<T: Rand>(len: usize) -> Vec<T> {
    let mut v: Vec<T> = Vec::new();
    for _ in 0..len {
        v.push(random())
    }
    v
}

fn permutation<T: Clone>(v: &Vec<T>) -> Vec<T> {
    let p = randvec::<usize>(v.len());
    let mut p = p.iter().zip(v).collect::<Vec<_>>();
    p.sort_by(|(k0, _), (k1, _)| k0.cmp(k1));
    p.into_iter().map(|(_, v)| v.clone()).collect::<Vec<T>>()
}

fn insert<I, K, V>(r: I) -> avl::Tree<K, V>
where
    I: IntoIterator<Item = (K, V)>,
    K: Ord + Clone + Debug,
    V: Clone + Debug,
{
    let mut t = avl::Tree::new();
    for (k, v) in r {
        t = t.insert(k.clone(), v.clone()).0;
        if t.len() % CHECK == 0 {
            t.invariant();
        }
    }
    t.invariant();
    t
}


#[test]
fn test_insert_int_seq_asc() {
    let t = insert((0..SIZE).into_iter().map(|i| (i, i)));
    let len = t.len();
    if len != SIZE {
        panic!("length is wrong expected 10000 got {}", len)
    }
}

#[test]
fn test_insert_int_seq_dec() {
    let t = insert(((0..SIZE).into_iter().map(|i| (i, i))).rev());
    let len = t.len();
    if len != SIZE {
        panic!("length is wrong expected 10000 got {}", len)
    }
}

#[test]
fn test_insert_int_rand() {
    insert(randvec::<i32>(SIZE).iter().map(|i| (*i, *i)));
    ()
}

fn test_get_rand_gen<K, V>()
where
    K: Ord + Clone + Debug + Rand,
    V: Ord + Clone + Debug + Rand,
{
    let v = randvec::<(K, V)>(SIZE);
    let t = insert(v.iter().cloned());
    for (k, v) in &v {
        assert_eq!(t.get(k).unwrap(), v);
    }
}

#[test]
fn test_get_rand() {
    make_tests!(test_get_rand_gen);
}

fn test_insert_remove_rand_gen<K, V>()
where
    K: Ord + Clone + Debug + Rand + Hash,
    V: Ord + Clone + Debug + Rand + Hash,
{
    let mut v = randvec::<(K, V)>(SIZE);
    dedup_with(&mut v, |(ref k, _)| k);
    let mut t = avl::Tree::new();
    for (k, v) in &v {
        let (tn, p) = t.insert(k.clone(), v.clone());
        assert_eq!(p, None);
        t = tn;
        assert_eq!(t.get(k).unwrap(), v);
        if t.len() % CHECK == 0 {
            let (tn, p) = t.remove(k);
            assert_eq!(p.as_ref(), Some(v));
            t = tn;
            assert_eq!(t.get(k), Option::None);
            t.invariant();
        }
    }
}

#[test]
fn test_insert_remove_rand() {   
    make_tests!(test_insert_remove_rand_gen);
}

#[test]
fn test_insert_many_small() {
    let v: Vec<i32> = vec![
        1, 9, 16, 11, 7, 12, 8, 12, 12, 11, 9, 12, 9, 7, 16, 9, 1, 9, 1, 1, 22, 112,
    ];
    let mut t = avl::Tree::new().insert_many(v.iter().map(|k| (*k, *k)));
    t.invariant();
    for k in &v {
        assert_eq!(t.get(k).unwrap(), k)
    }
    t = t.remove(&22i32).0;
    t = t.remove(&112i32).0;
    t.invariant();
    for k in &v {
        if *k == 22i32 || *k == 112i32 {
            assert_eq!(t.get(k), Option::None);
        } else {
            assert_eq!(t.get(k), Option::Some(k));
        }
    }
    let v2: Vec<i32> = vec![12i32, 987i32, 19i32, 98i32];
    t = t.insert_many(v2.iter().map(|k| (k.clone(), k.clone())));
    for k in &v2 {
        assert_eq!(t.get(k).unwrap(), k);
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

fn test_insert_many_gen<K, V>()
where
    K: Ord + Clone + Debug + Rand + Hash,
    V: Ord + Clone + Debug + Rand + Hash,
{
    let mut v = randvec::<(K, V)>(SIZE);
    dedup_with(&mut v, |(ref k, _)| k);
    let mut t = avl::Tree::new().insert_many(v.iter().map(|(k, v)| (k.clone(), v.clone())));
    t.invariant();
    for (k, v) in &v {
        assert_eq!(t.get(k).unwrap(), v)
    }
    {
        let mut i = 0;
        for (k, _) in &v {
            if i % CHECK == 0 {
                t = t.remove(k).0;
                t.invariant();
            }
            i = i + 1;
        }
        i = 0;
        for (k, v) in &v {
            if i % CHECK == 0 {
                assert_eq!(t.get(k), None);
            } else {
                assert_eq!(t.get(k), Some(v));
            }
            i = i + 1;
        }
    };
    let mut v2 = randvec::<(K, V)>(SIZE);
    dedup_with(&mut v2, |(ref k, _)| k);
    t = t.insert_many(v2.iter().map(|(k, v)| (k.clone(), v.clone())));
    t.invariant();
    {
        let mut i = 0;
        for (k, v) in &v {
            if i % CHECK != 0 {
                assert_eq!(t.get(k), Some(v));
            }
            i += 1
        }
    }
    for (k, v) in &v2 {
        assert_eq!(t.get(k), Some(v));
    }
    let mut i = 0;
    t = t.update_many(v2.iter().map(|(k, v)| (k.clone(), v.clone())), &mut |k, v, cur| {
        i += 1;
        assert_eq!(cur, Some((&k, &v)));
        None
    });
    t.invariant();
    assert_eq!(i, v2.len());
    for (k, _) in &v2 {
        assert_eq!(t.get(k), None)
    }
}

#[test]
fn test_insert_many() {
    make_tests!(test_insert_many_gen);
}

fn test_map_rand_gen<K, V>()
where
    K: Ord + Clone + Debug + Rand + Hash,
    V: Ord + Clone + Debug + Rand + Hash,
{
    let mut vals = randvec::<(K, V)>(SIZE);
    dedup_with(&mut vals, |(ref k, _)| k);
    let mut t = Map::new();
    let mut i = 0;
    for (k, v) in &vals {
        t = t.insert(k.clone(), v.clone()).0;
        assert_eq!(t.get(k).unwrap(), v);
        if i % CHECK == 0 {
            t.invariant();
            for (k, v) in &vals[0..i] {
                assert_eq!(t.get(k).unwrap(), v);
            }
        }
        i = i + 1;
    }

    i = 0;
    for (k, _) in &vals {
        t = t.remove(k).0;
        if i % CHECK == 0 {
            t.invariant();
            for (k, _) in &vals[0..i] {
                assert_eq!(t.get(k), Option::None);
            }
        }
        i = i + 1;
    }
}

#[test]
fn test_map_rand() {
    make_tests!(test_map_rand_gen);
}

fn test_map_iter_gen<K, V>()
where
    K: Ord + Clone + Debug + Rand + Hash,
    V: Ord + Clone + Debug + Rand + Hash,
{
    let mut vals = randvec::<(K, V)>(SIZE);
    vals.sort_unstable_by(|t0, t1| t0.0.cmp(&t1.0));
    dedup_with(&mut vals, |(ref k, _)| k);
    let t = Map::new().insert_many(vals.iter().cloned());
    t.invariant();
    let mut i = 0;
    for (k, v) in &t {
        let (k_, v_) = (&vals[i].0, &vals[i].1);
        assert_eq!(k, k_);
        assert_eq!(v, v_);
        i = i + 1;
    }
}

#[test]
fn test_map_iter() {
    make_tests!(test_map_iter_gen);
}

#[test]
fn test_map_range_small() {
    let mut v = Vec::new();
    v.extend((-5000..5000).into_iter());
    let t = Map::new().insert_many(v.iter().map(|x| (*x, *x)));
    t.invariant();
    assert_eq!(t.len(), 10000);
    {
        let mut i = 0;
        for e in &t {
            assert_eq!(e.0, e.1);
            assert_eq!(&v[i], e.0);
            assert!(i < 10000);
            i += 1
        }
        assert_eq!(i, 10000)
    }
    {
        let mut i = 5000;
        for e in t.range(Included(0), Excluded(100)) {
            assert_eq!(e.0, e.1);
            assert_eq!(&v[i], e.0);
            assert!(i < 5100);
            i += 1
        }
        assert_eq!(i, 5100)
    }
    {
        let mut i = 5000;
        for e in t.range(Excluded(0), Included(100)) {
            assert_eq!(e.0, e.1);
            assert_eq!(&v[i + 1], e.0);
            assert!(i < 5100);
            i += 1
        }
        assert_eq!(i, 5100)
    }
    {
        let mut i = 7300;
        for e in t.range(Included(2300), Excluded(3500)) {
            assert_eq!(e.0, e.1);
            assert_eq!(&v[i], e.0);
            assert!(i < 8500);
            i += 1
        }
        assert_eq!(i, 8500)
    }
    {
        let mut i = 7900;
        for e in t.range(Included(2900), Unbounded) {
            assert_eq!(e.0, e.1);
            assert_eq!(&v[i], e.0);
            assert!(i < 10000);
            i += 1
        }
        assert_eq!(i, 10000)
    }
    {
        let mut i = 0;
        for e in t.range(Included(-5000), Excluded(-4000)) {
            assert_eq!(e.0, e.1);
            assert_eq!(&v[i], e.0);
            assert!(i < 1000);
            i += 1
        }
        assert_eq!(i, 1000)
    }
    {
        let mut i = 0;
        for _ in t.range(Excluded(-5000), Excluded(-4999)) {
            i += 1
        }
        assert_eq!(i, 0)
    }
    {
        let mut i = 0;
        for _ in t.range(Included(1), Included(0)) {
            i += 1
        }
        assert_eq!(i, 0)
    }
}

fn test_map_range_gen<K, V>()
where
    K: Ord + Clone + Debug + Rand + Hash,
    V: Ord + Clone + Debug + Rand + Hash,
{
    let mut vals = randvec::<(K, V)>(SIZE);
    dedup_with(&mut vals, |(ref k, _)| k);
    let mut t: Map<K, V> = Map::new();
    t = t.insert_many(vals.iter().map(|(k, v)| (k.clone(), v.clone())));
    t.invariant();
    vals.sort_unstable_by(|t0, t1| t0.0.cmp(&t1.0));
    let (start, end) = loop {
        let mut r = rand::thread_rng();
        let i = r.gen_range(0, SIZE - 1);
        let j = r.gen_range(0, SIZE - 1);
        if i == j {
            continue;
        } else if i < j {
            break (i, j);
        } else {
            break (j, i);
        }
    };
    println!(
        "start: {:?}:{:?} end {:?}:{:?} len {:?}",
        start,
        vals[start],
        end,
        vals[end],
        vals.len()
    );
    {
        let mut i = start;
        let lbound = Included(vals[i].0.clone());
        let ubound = Excluded(vals[end].0.clone());
        for (k, v) in t.range(lbound, ubound) {
            let (k_, v_) = (&vals[i].0, &vals[i].1);
            assert_eq!(k, k_);
            assert_eq!(v, v_);
            assert!(i < end);
            i += 1;
        }
        assert_eq!(i, end);
    }
    {
        let mut i = start;
        let lbound = Excluded(vals[i].0.clone());
        let ubound = Included(vals[end].0.clone());
        for (k, v) in t.range(lbound, ubound) {
            let (k_, v_) = (&vals[i].0, &vals[i].1);
            assert_eq!(k, k_);
            assert_eq!(v, v_);
            assert!(i < end);
            i += 1;
        }
        assert_eq!(i, end);
    }
    {
        let mut i = 0;
        let lbound = Unbounded;
        let ubound = Excluded(vals[end].0.clone());
        for (k, v) in t.range(lbound, ubound) {
            let (k_, v_) = (&vals[i].0, &vals[i].1);
            assert_eq!(k, k_);
            assert_eq!(v, v_);
            assert!(i < end);
            i += 1;
        }
        assert_eq!(i, end);
    }
    {
        let mut i = end - 1;
        let lbound = Included(vals[start].0.clone());
        let ubound = Excluded(vals[end].0.clone());
        let mut r = t.range(lbound, ubound);
        while let Some((k, v)) = r.next_back() {
            let (k_, v_) = (&vals[i].0, &vals[i].1);
            assert_eq!(k, k_);
            assert_eq!(v, v_);
            assert!(i >= start);
            i -= 1;
        }
        assert_eq!(start - 1, i);
    }
}

#[test]
fn test_map_range() {
    make_tests!(test_map_range_gen);
}

fn test_set_gen<T: Borrow<T> + Ord + Clone + Debug + Rand + Hash>() {
    let mut v = randvec::<T>(SIZE);
    dedup_with(&mut v, |k| k);
    let mut t = Set::new();
    let mut i = 0;
    for k in &v {
        let (tn, p) = t.insert(k.clone());
        t = tn;
        assert_eq!(p, false);
        assert_eq!(t.contains(k), true);
        if i % CHECK == 0 {
            for j in 0..i {
                assert_eq!(t.contains(&v[j]), true)
            }
            t.invariant()
        }
        i += 1
    }
    i = 0;
    for k in &v {
        let (tn, p) = t.remove(k);
        t = tn;
        assert_eq!(p, true);
        if i % CHECK == 0 {
            for j in 0..i {
                assert_eq!(t.contains(&v[j]), false);
            }
            for j in (i + 1)..v.len() {
                assert_eq!(t.get(&v[j]), Some(&v[j]));
            }
            t.invariant()
        }
        i += 1
    }
}

#[test]
fn test_set() {
    test_set_gen::<i32>();
    test_set_gen::<usize>();
    test_set_gen::<Arc<String>>();
    test_set_gen::<(i32, Arc<String>)>();
}

#[test]
fn test_ord() {
    let v0 = randvec::<i32>(SIZE);
    let v1 = permutation(&v0);
    let mut v2 = permutation(&v0);
    let mut v3 = permutation(&v0);
    for i in (0..SIZE).rev() {
        if v2[i] < i32::MAX {
            v2[i] += 1;
            break;
        }
    }
    for i in (0..SIZE).rev() {
        if v3[i] > i32::MIN {
            v3[i] -= 1;
            break;
        }
    }
    let s0 = v0.iter().map(|v| v.clone()).collect::<Set<_>>();
    let s1 = v1.iter().map(|v| v.clone()).collect::<Set<_>>();
    let s2 = v2.iter().map(|v| v.clone()).collect::<Set<_>>();
    let s3 = v3.iter().map(|v| v.clone()).collect::<Set<_>>();
    assert!(s0 == s1);
    assert_eq!(s0.cmp(&s1), Ordering::Equal);
    assert!(s0 != s2);
    assert_eq!(s0.cmp(&s2), Ordering::Less);
    assert!(s0 != s3);
    assert_eq!(s0.cmp(&s3), Ordering::Greater);
}

fn test_union_gen<T: Borrow<T> + Ord + Clone + Debug + Rand + Hash>() {
    let mut v0 = randvec::<T>(SIZE);
    let mut v1 = randvec::<T>(SIZE);
    dedup_with(&mut v0, |k| k);
    dedup_with(&mut v1, |k| k);
    let m0 = Map::from_iter(v0.iter().map(|k| (k.clone(), 1)));
    let m1 = Map::from_iter(v1.iter().map(|k| (k.clone(), 1)));
    let m2 = m0.union(&m1, |_, v0, v1| Some(v0 + v1));
    m2.invariant();
    let mut hm = HashMap::new();
    for k in v0.iter().chain(v1.iter()) {
        *hm.entry(k.clone()).or_insert(0) += 1;
    }
    for (k, v) in &hm {
        assert!(m2.get(k).unwrap() == v)
    }
    for (k, v) in &m2 {
        assert!(hm.get(k).unwrap() == v)
    }
}

#[test]
fn test_union() {
    test_union_gen::<i32>();
    test_union_gen::<usize>();
    test_union_gen::<Arc<String>>();
    test_union_gen::<(i32, Arc<String>)>();
}

fn test_intersect_gen<T: Borrow<T> + Ord + Clone + Debug + Rand + Hash>() {
    let mut v0 = randvec::<T>(SIZE);
    let mut v1 = randvec::<T>(SIZE);
    dedup_with(&mut v0, |k| k);
    dedup_with(&mut v1, |k| k);
    let m0 = Map::from_iter(v0.iter().map(|k| (k.clone(), 1)));
    let m1 = Map::from_iter(v1.iter().map(|k| (k.clone(), 1)));
    let m2 = m0.intersect(&m1, |_, v0, v1| Some(v0 + v1));
    m2.invariant();
    let mut hm0 = HashMap::new();
    let mut hm1 = HashMap::new();
    let mut hm2 = HashMap::new();
    let ins = |v: Vec<T>, hm: &mut HashMap<T, i32>| {
        for k in v.iter() {
            *hm.entry(k.clone()).or_insert(0) += 1;
        }
    };
    ins(v0, &mut hm0);
    ins(v1, &mut hm1);
    for (k, v0) in &hm0 {
        match hm1.get(k) {
            None => (),
            Some(v1) => {
                hm2.insert(k.clone(), *v0 + *v1);
            }
        }
    }
    for (k, v) in &hm2 {
        assert_eq!(v, m2.get(k).unwrap())
    }
    for (k, v) in &m2 {
        assert_eq!(v, hm2.get(k).unwrap())
    }
}

#[test]
fn test_intersect() {
    test_intersect_gen::<i32>();
    test_intersect_gen::<usize>();
    test_intersect_gen::<Arc<String>>();
    test_intersect_gen::<(i32, Arc<String>)>();
}

fn test_diff_gen<T: Borrow<T> + Ord + Clone + Debug + Rand + Hash>() {
    let mut v0 = randvec::<T>(SIZE);
    let mut v1 = randvec::<T>(SIZE);
    dedup_with(&mut v0, |k| k);
    dedup_with(&mut v1, |k| k);
    let m0 = Map::from_iter(v0.iter().map(|k| (k.clone(), ())));
    let m1 = Map::from_iter(v1.iter().map(|k| (k.clone(), ())));
    let m2 = m0.diff(&m1, |_, (), ()| None);
    m2.invariant();
    let mut hm = HashMap::new();
    for k in v0.iter() {
        hm.insert(k, ());
    }
    for k in &v1 {
        hm.remove(k);
    }
    for (k, ()) in &hm {
        m2.get(k).unwrap();
    }
    for (k, ()) in &m2 {
        hm.get(k).unwrap();
    }
}

#[test]
fn test_diff() {
    test_diff_gen::<i32>();
    test_diff_gen::<usize>();
    test_diff_gen::<Arc<String>>();
    test_diff_gen::<(i32, Arc<String>)>();
}
