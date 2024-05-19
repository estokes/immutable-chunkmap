use crate::{avl, chunk::DEFAULT_SIZE, map::MapM, set::SetM};
use rand::Rng;
use std::{
    borrow::Borrow,
    cmp::Ordering,
    collections::{BTreeMap, HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    i32,
    iter::{FromIterator, IntoIterator},
    ops::Bound::{Excluded, Included},
    sync::Arc,
    vec::Vec,
};

const STRSIZE: usize = 10;
const SIZE: usize = 500000;
const CHECK: usize = 500;

macro_rules! make_tests {
    ($name:ident) => {
        paste::item! {
            #[test]
            fn [<$name _i32_i32>]() {
                $name::<i32, i32>();
            }
        }

        paste::item! {
            #[test]
            fn [<$name _i32_usize>]() {
                $name::<i32, usize>();
            }
        }

        paste::item! {
            #[test]
            fn [<$name _usize_i32>]() {
                $name::<usize, i32>();
            }
        }

        paste::item! {
            #[test]
            fn [<$name _usize_usize>]() {
                $name::<usize, usize>();
            }
        }

        paste::item! {
            #[test]
            fn [<$name _i32_string>]() {
                $name::<i32, Arc<str>>();
            }
        }

        paste::item! {
            #[test]
            fn [<$name _string_i32>]() {
                $name::<Arc<str>, i32>();
            }
        }

        paste::item! {
            #[test]
            fn [<$name _usize_string_pair>]() {
                $name::<usize, (Arc<str>, Arc<str>)>();
            }
        }

        paste::item! {
            #[test]
            fn [<$name _string_pair_usize>]() {
                $name::<(Arc<str>, Arc<str>), usize>();
            }
        }
    };
}

trait Rand: Sized {
    fn rand<R: Rng>(r: &mut R) -> Self;
}

impl<T: Rand, U: Rand> Rand for (T, U) {
    fn rand<R: Rng>(r: &mut R) -> Self {
        (T::rand(r), U::rand(r))
    }
}

impl Rand for Arc<str> {
    fn rand<R: Rng>(r: &mut R) -> Self {
        let mut s = String::new();
        for _ in 0..STRSIZE {
            s.push(r.gen())
        }
        Arc::from(s.as_str())
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

fn insert<I, K, V>(r: I) -> avl::Tree<K, V, DEFAULT_SIZE>
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
    K: Ord + Clone + Debug + Hash + Rand,
    V: Ord + Clone + Debug + Hash + Rand,
{
    let mut vals = randvec::<(K, V)>(SIZE);
    dedup_with(&mut vals, |(ref k, _)| k);
    let t = insert(vals.iter().cloned());
    for (k, v) in &vals {
        assert_eq!(t.get(k).unwrap(), v);
    }
}

make_tests!(test_get_rand_gen);

fn test_insert_remove_rand_gen<K, V>()
where
    K: Ord + Clone + Debug + Rand + Hash,
    V: Ord + Clone + Debug + Rand + Hash,
{
    let mut v = randvec::<(K, V)>(SIZE);
    dedup_with(&mut v, |(ref k, _)| k);
    let mut t = avl::Tree::<_, _, DEFAULT_SIZE>::new();
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
        }
    }
    t.invariant();
}

make_tests!(test_insert_remove_rand_gen);

fn test_cow_rand_gen<K, V>()
where
    K: Ord + Clone + Debug + Rand + Hash,
    V: Ord + Clone + Debug + Rand + Hash,
{
    let mut model: HashMap<K, V> = HashMap::new();
    let mut v = randvec::<(K, V)>(SIZE);
    let mut o = randvec::<(K, V)>(SIZE);
    dedup_with(&mut v, |(ref k, _)| k);
    dedup_with(&mut o, |(ref k, _)| k);
    let v = v;
    let o = o;
    let t = insert(v.iter().cloned());
    for (k, v) in &v {
        model.insert(k.clone(), v.clone());
    }
    let mut cow = t.clone();
    for (i, (k, v)) in o.iter().enumerate() {
        *cow.get_or_insert_cow(k.clone(), || v.clone()) = v.clone();
        model.insert(k.clone(), v.clone());
        assert_eq!(cow.get(k), Some(v));
        if i > 0 && i % CHECK == 0 {
            loop {
                let j = rand::thread_rng().gen_range(0..i);
                let k = &o[j].0;
                if let Some(v) = model.remove(k) {
                    let p = cow.remove_cow(k);
                    assert_eq!(p.as_ref(), Some(&v));
                    assert_eq!(cow.get(k), Option::None);
                    break;
                }
            }
        }
        if i > 0 && i % CHECK == 1 {
            loop {
                let j = rand::thread_rng().gen_range(0..i);
                let k = &o[j].0;
                if let Some(mv) = model.get_mut(k) {
                    let v: V = random();
                    *cow.get_mut_cow(k).unwrap() = v.clone();
                    *mv = v.clone();
                    assert_eq!(cow.get(k), model.get(k));
                    break;
                }
            }
        }
    }
    cow.invariant();
    t.invariant();
    // check that the original is unchanged after the cow was modified
    assert_eq!(t.len(), v.len());
    for (k, v) in &v {
        assert_eq!(t.get(k), Some(v))
    }
    // check that the cow matches the model
    assert_eq!(model.len(), cow.len());
    for (k, v) in &model {
        assert_eq!(cow.get(k), Some(v))
    }
    for (k, v) in &cow {
        assert_eq!(model.get(k), Some(v))
    }
}

make_tests!(test_cow_rand_gen);

#[test]
fn test_insert_many_small() {
    let v: Vec<i32> = vec![
        1, 9, 16, 11, 7, 12, 8, 12, 12, 11, 9, 12, 9, 7, 16, 9, 1, 9, 1, 1, 22, 112,
    ];
    let mut t =
        avl::Tree::<_, _, DEFAULT_SIZE>::new().insert_many(v.iter().map(|k| (*k, *k)));
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
where
    F: Fn(&T) -> &K,
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
    let mut t = avl::Tree::<_, _, DEFAULT_SIZE>::new()
        .insert_many(v.iter().map(|(k, v)| (k.clone(), v.clone())));
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
    let v2 = {
        let len = v.len();
        v.append(&mut randvec::<(K, V)>(SIZE));
        dedup_with(&mut v, |(ref k, _)| k);
        v.split_off(len)
    };
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
    t = t.update_many(
        v2.iter().map(|(k, v)| (k.clone(), v.clone())),
        &mut |k, v, cur| {
            i += 1;
            assert_eq!(cur, Some((&k, &v)));
            None
        },
    );
    t.invariant();
    assert_eq!(i, v2.len());
    for (k, _) in &v2 {
        assert_eq!(t.get(k), None)
    }
}

make_tests!(test_insert_many_gen);

fn test_map_rand_gen<K, V>()
where
    K: Ord + Clone + Debug + Rand + Hash,
    V: Ord + Clone + Debug + Rand + Hash,
{
    let mut vals = randvec::<(K, V)>(SIZE);
    dedup_with(&mut vals, |(ref k, _)| k);
    let mut t = MapM::new();
    let mut i = 0;
    for (k, v) in &vals {
        t = t.insert(k.clone(), v.clone()).0;
        assert_eq!(t.get(k).unwrap(), v);
        i = i + 1;
    }
    for (k, v) in &vals {
        assert_eq!(t.get(k).unwrap(), v);
    }
    t.invariant();

    i = 0;
    for (k, _) in &vals {
        t = t.remove(k).0;
        i = i + 1;
    }
    for (k, _) in &vals {
        assert_eq!(t.get(k), Option::None);
    }
    t.invariant();
}

make_tests!(test_map_rand_gen);

fn test_map_iter_gen<K, V>()
where
    K: Ord + Clone + Debug + Rand + Hash,
    V: Ord + Clone + Debug + Rand + Hash,
{
    let mut vals = randvec::<(K, V)>(SIZE);
    dedup_with(&mut vals, |(ref k, _)| k);
    let t = MapM::new().insert_many(vals.iter().cloned());
    t.invariant();
    assert_eq!(vals.len(), t.len());
    vals.sort_unstable_by(|t0, t1| t0.0.cmp(&t1.0));
    let mut i = 0;
    for (k, v) in &t {
        let (k_, v_) = (&vals[i].0, &vals[i].1);
        assert_eq!(k, k_);
        assert_eq!(v, v_);
        i = i + 1;
    }
}

make_tests!(test_map_iter_gen);

fn test_map_iter_mut_gen<K, V>()
where
    K: Ord + Clone + Debug + Rand + Hash,
    V: Ord + Clone + Debug + Rand + Hash,
{
    let mut vals = randvec::<(K, V)>(SIZE);
    dedup_with(&mut vals, |(ref k, _)| k);
    let mut model: BTreeMap<K, V> = BTreeMap::from_iter(vals.iter().cloned());
    let model_u: BTreeMap<K, V> = BTreeMap::from_iter(vals.iter().cloned());
    let mut t = MapM::new().insert_many(vals.iter().cloned());
    let u = t.clone();
    t.invariant();
    u.invariant();
    // t and model are equal
    assert_eq!(model.len(), t.len());
    for ((k, v), (k_, v_)) in t.into_iter().zip(model.iter()) {
        assert_eq!(k, k_);
        assert_eq!(v, v_);
    }
    // mutate t and model
    assert_eq!(model.len(), t.len());
    let mut iter = t.iter_mut_cow();
    let mut miter = model.iter_mut();
    let mut i = 0;
    while i < vals.len() {
        let ((k, v), (k_, v_)) = if rand::thread_rng().gen_bool(0.8) {
            let p = iter.next().unwrap();
            let p_ = miter.next().unwrap();
            (p, p_)
        } else {
            let p = iter.next_back().unwrap();
            let p_ = miter.next_back().unwrap();
            (p, p_)
        };
        assert_eq!(k, k_);
        assert_eq!(v, v_);
        let n: V = random();
        *v = n.clone();
        *v_ = n;
        i += 1;
    }
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next_back(), None);
    t.invariant();
    // t and model are equal after mutation
    assert_eq!(model.len(), t.len());
    for ((k, v), (k_, v_)) in t.into_iter().zip(model.iter()) {
        assert_eq!(k, k_);
        assert_eq!(v, v_);
    }
    // u is unchanged after t's mutation because COW
    u.invariant();
    assert_eq!(model_u.len(), u.len());
    for ((k, v), (k_, v_)) in u.into_iter().zip(model_u.iter()) {
        assert_eq!(k, k_);
        assert_eq!(v, v_);
    }
}

make_tests!(test_map_iter_mut_gen);

#[test]
fn test_map_range_small() {
    let mut v = Vec::new();
    v.extend((-5000..5000).into_iter());
    let t = MapM::new().insert_many(v.iter().map(|x| (*x, *x)));
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
        for e in t.range(0..100) {
            assert_eq!(e.0, e.1);
            assert_eq!(&v[i], e.0);
            assert!(i < 5100);
            i += 1
        }
        assert_eq!(i, 5100)
    }
    {
        let mut i = 5000;
        for e in t.range((Excluded(&0), Included(&100))) {
            assert_eq!(e.0, e.1);
            assert_eq!(&v[i + 1], e.0);
            assert!(i < 5100);
            i += 1
        }
        assert_eq!(i, 5100)
    }
    {
        let mut i = 7300;
        for e in t.range(2300..3500) {
            assert_eq!(e.0, e.1);
            assert_eq!(&v[i], e.0);
            assert!(i < 8500);
            i += 1
        }
        assert_eq!(i, 8500)
    }
    {
        let mut i = 7900;
        for e in t.range(2900..) {
            assert_eq!(e.0, e.1);
            assert_eq!(&v[i], e.0);
            assert!(i < 10000);
            i += 1
        }
        assert_eq!(i, 10000)
    }
    {
        let mut i = 0;
        for e in t.range(-5000..-4000) {
            assert_eq!(e.0, e.1);
            assert_eq!(&v[i], e.0);
            assert!(i < 1000);
            i += 1
        }
        assert_eq!(i, 1000)
    }
    {
        let mut i = 0;
        for _ in t.range((Excluded(&-5000), Excluded(&-4999))) {
            i += 1
        }
        assert_eq!(i, 0)
    }
    {
        let mut i = 0;
        for _ in t.range(1..=0) {
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
    let mut t: MapM<K, V> = MapM::new();
    t = t.insert_many(vals.iter().map(|(k, v)| (k.clone(), v.clone())));
    t.invariant();
    vals.sort_unstable_by(|t0, t1| t0.0.cmp(&t1.0));
    let (start, end) = loop {
        let mut r = rand::thread_rng();
        let i = r.gen_range(0..SIZE);
        let j = r.gen_range(0..SIZE);
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
        for (k, v) in t.range(&vals[i].0..&vals[end].0) {
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
        let lbound = Excluded(&vals[i].0);
        let ubound = Included(&vals[end].0);
        for (k, v) in t.range((lbound, ubound)) {
            let (k_, v_) = (&vals[i + 1].0, &vals[i + 1].1);
            assert_eq!(k, k_);
            assert_eq!(v, v_);
            assert!(i < end);
            i += 1;
        }
        assert_eq!(i, end);
    }
    {
        let mut i = 0;
        for (k, v) in t.range(..&vals[end].0) {
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
        let mut r = t.range(&vals[start].0..&vals[end].0);
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

make_tests!(test_map_range_gen);

fn test_set_gen<T: Borrow<T> + Ord + Clone + Debug + Rand + Hash>() {
    let mut v = randvec::<T>(SIZE);
    dedup_with(&mut v, |k| k);
    let mut t = SetM::new();
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
    test_set_gen::<Arc<str>>();
    test_set_gen::<(i32, Arc<str>)>();
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
    let s0 = v0.iter().map(|v| v.clone()).collect::<SetM<_>>();
    let s1 = v1.iter().map(|v| v.clone()).collect::<SetM<_>>();
    let s2 = v2.iter().map(|v| v.clone()).collect::<SetM<_>>();
    let s3 = v3.iter().map(|v| v.clone()).collect::<SetM<_>>();
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
    let m0 = MapM::from_iter(v0.iter().map(|k| (k.clone(), 1)));
    let m1 = MapM::from_iter(v1.iter().map(|k| (k.clone(), 1)));
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
    test_union_gen::<Arc<str>>();
    test_union_gen::<(i32, Arc<str>)>();
}

fn test_intersect_gen<T: Borrow<T> + Ord + Clone + Debug + Rand + Hash>() {
    let mut v0 = randvec::<T>(SIZE);
    let mut v1 = randvec::<T>(SIZE);
    dedup_with(&mut v0, |k| k);
    dedup_with(&mut v1, |k| k);
    let m0 = MapM::from_iter(v0.iter().map(|k| (k.clone(), 1)));
    let m1 = MapM::from_iter(v1.iter().map(|k| (k.clone(), 1)));
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
    test_intersect_gen::<Arc<str>>();
    test_intersect_gen::<(i32, Arc<str>)>();
}

fn test_diff_gen<T: Borrow<T> + Ord + Clone + Debug + Rand + Hash>() {
    let mut v0 = randvec::<T>(SIZE);
    let mut v1 = randvec::<T>(SIZE);
    dedup_with(&mut v0, |k| k);
    dedup_with(&mut v1, |k| k);
    let m0 = MapM::from_iter(v0.iter().map(|k| (k.clone(), ())));
    let m1 = MapM::from_iter(v1.iter().map(|k| (k.clone(), ())));
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
    test_diff_gen::<Arc<str>>();
    test_diff_gen::<(i32, Arc<str>)>();
}

#[cfg(feature = "serde")]
#[test]
fn test_serde_map() {
    let k = randvec::<i32>(SIZE);
    let v = randvec::<i32>(SIZE);
    let m0 = MapM::from_iter(k.iter().zip(v.iter()).map(|(k, v)| (*k, *v)));
    let json = serde_json::to_string(&m0).unwrap();
    let m1: MapM<i32, i32> = serde_json::from_str(&json).unwrap();
    assert_eq!(&m0, &m1)
}

#[cfg(feature = "serde")]
#[test]
fn test_serde_set() {
    let v = randvec::<i32>(SIZE);
    let s0 = SetM::from_iter(v.iter().map(|v| *v));
    let json = serde_json::to_string(&s0).unwrap();
    let s1: SetM<i32> = serde_json::from_str(&json).unwrap();
    assert_eq!(&s0, &s1)
}

#[cfg(feature = "rayon")]
#[test]
fn test_rayon_map() {
    use rayon::prelude::*;
    let k = randvec::<i32>(SIZE);
    let v = randvec::<i32>(SIZE);
    let m0 = MapM::from_iter(k.iter().zip(v.iter()).map(|(k, v)| (*k, *v)));
    let sum_par: i64 = m0.into_par_iter().map(|(_, v)| *v as i64).sum();
    let sum_seq: i64 = m0.into_iter().map(|(_, v)| *v as i64).sum();
    assert_eq!(sum_par, sum_seq);
    let m1 = m0
        .into_par_iter()
        .map(|(k, v)| (*k, *v))
        .collect::<MapM<_, _>>();
    assert_eq!(m0, m1)
}

#[cfg(feature = "rayon")]
#[test]
fn test_rayon_set() {
    use rayon::prelude::*;
    let v = randvec::<i32>(SIZE);
    let s0 = SetM::from_iter(v.iter().copied());
    let sum_par: i64 = s0.into_par_iter().map(|v| *v as i64).sum();
    let sum_seq: i64 = s0.into_iter().map(|v| *v as i64).sum();
    assert_eq!(sum_par, sum_seq);
    let s1 = s0.into_par_iter().map(|v| *v).collect::<SetM<_>>();
    assert_eq!(s0, s1)
}

fn remove_random_contig_slice(
    v: &Vec<(i32, i32)>,
    map: &MapM<i32, i32>,
) -> (HashMap<i32, i32>, MapM<i32, i32>) {
    let start = rand::thread_rng().gen_range(0..v.len() - 1);
    let end = rand::thread_rng().gen_range(start..v.len());
    let r = v
        .iter()
        .enumerate()
        .filter_map(|(i, kv)| {
            if i >= start && i < end {
                Some(kv)
            } else {
                None
            }
        })
        .copied()
        .collect::<HashMap<_, _>>();
    let map_r = map.update_many(r.iter().map(|(k, _)| (*k, ())), |_, _, _| None);
    map_r.invariant();
    (r, map_r)
}

fn remove_random_entries(
    v: &Vec<(i32, i32)>,
    map: &MapM<i32, i32>,
) -> (HashMap<i32, i32>, MapM<i32, i32>) {
    let mut rng = rand::thread_rng();
    let r = v
        .iter()
        .filter(|(_, _)| rng.gen_range(0..4) == 0)
        .copied()
        .collect::<HashMap<_, _>>();
    let map_r = map.update_many(r.iter().map(|(k, _)| (*k, ())), |_, _, _| None);
    map_r.invariant();
    (r, map_r)
}

fn remove_maybe_nonexist_entries(
    map: &MapM<i32, i32>,
) -> (HashMap<i32, i32>, MapM<i32, i32>) {
    let size = rand::thread_rng().gen_range(10..SIZE);
    let r = randvec::<(i32, i32)>(size)
        .into_iter()
        .collect::<HashMap<_, _>>();
    let map_r = map.update_many(r.iter().map(|(k, _)| (*k, ())), |_, _, _| None);
    map_r.invariant();
    (r, map_r)
}

fn check_removed(v: &Vec<(i32, i32)>, r: &HashMap<i32, i32>, map_r: &MapM<i32, i32>) {
    let expected_len =
        v.iter().fold(
            v.len(),
            |len, (k, _)| {
                if r.contains_key(k) {
                    len - 1
                } else {
                    len
                }
            },
        );
    assert_eq!(map_r.len(), expected_len);
    for (k, v) in v {
        if r.contains_key(k) {
            assert_eq!(None, map_r.get(k));
        } else {
            assert_eq!(Some(v), map_r.get(k));
        }
    }
}

#[test]
fn test_remove_many_patterns() {
    let size = rand::thread_rng().gen_range(10..SIZE);
    let mut v = randvec::<(i32, i32)>(size);
    dedup_with(&mut v, |(k, _)| k);
    v.sort_by_key(|(k, _)| *k);
    let map = MapM::from_iter(v.iter().copied());
    map.invariant();
    for (k, v) in &v {
        assert_eq!(Some(v), map.get(k));
    }
    let (r, map_r) = remove_random_contig_slice(&v, &map);
    check_removed(&v, &r, &map_r);
    let (r, map_r) = remove_random_entries(&v, &map);
    check_removed(&v, &r, &map_r);
    let (r, map_r) = remove_maybe_nonexist_entries(&map);
    check_removed(&v, &r, &map_r);
}
