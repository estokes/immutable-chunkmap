macro_rules! tests {
    ($p:ident) => {
        mod $p {
            extern crate rand;
            use $p::avl;
            use $p::map;
            use tests::$p::rand::Rng;
            use std::{
                iter::{IntoIterator}, vec::{Vec}, fmt::Debug, borrow::Borrow,
                ops::Bound::{Included, Excluded, Unbounded}
            };

            const STRSIZE: usize = 10;
            const SIZE: usize = 500000;
            const CHECK: usize = 10000;

            trait Rand: Sized {
                fn rand<R: Rng>(r: &mut R) -> Self;
            }

            impl Rand for String {
                fn rand<R: Rng>(r: &mut R) -> Self {
                    let mut s = String::new();
                    for _ in 0..STRSIZE { s.push(r.gen()) }
                    s
                }
            }

            impl Rand for i32 {
                fn rand<R: Rng>(r: &mut R) -> Self { r.gen() }
            }

            impl Rand for usize {
                fn rand<R: Rng>(r: &mut R) -> Self { r.gen() }
            }

            fn random<T: Rand>() -> T {
                let mut rng = rand::thread_rng();
                T::rand(&mut rng)
            }

            fn randvec<T: Rand>(len: usize) -> Vec<T> {
                let mut v: Vec<T> = Vec::new();
                for _ in 0..len { v.push(random()) }
                v
            }

            fn insert<I, T>(r: I) -> (avl::Tree<T, T>, usize)
            where I: IntoIterator<Item=T>, T: Ord + Clone + Debug
            {
                let mut t = (avl::Tree::new(), 0, None);
                for i in r {
                    t = t.0.insert(t.1, i.clone(), i.clone());
                    if t.1 % CHECK == 0 { t.0.invariant(t.1); }
                }
                t.0.invariant(t.1);
                (t.0, t.1)
            }

            #[test]
            fn test_insert_int_seq_asc() {
                let (_, len) = insert(0..SIZE);
                if len != SIZE { panic!("length is wrong expected 10000 got {}", len) }
            }

            #[test]
            fn test_insert_int_seq_dec() {
                let (_, len) = insert((0..SIZE).rev());
                if len != SIZE {panic!("length is wrong expected 10000 got {}", len)}
            }

            #[test]
            fn test_insert_int_rand() {
                insert(randvec::<i32>(SIZE)); ()
            }

            fn test_get_rand<T: Ord + Clone + Debug + Rand>() {
                let v = randvec::<T>(SIZE);
                let (t, _) = insert(&v);
                for k in &v {
                    assert_eq!(*t.get(&k).unwrap(), k);
                }
            }

            #[test]
            fn test_get_int_rand() { test_get_rand::<i32>() }

            #[test]
            fn test_get_str_rand() { test_get_rand::<String>() }

            fn test_insert_remove_rand<T: Ord + Clone + Debug + Rand>() {
                let v = randvec::<T>(SIZE);
                let mut t = (avl::Tree::new(), 0, None);
                for k in &v {
                    t = t.0.insert(t.1, k, k);
                    assert_eq!(*t.0.get(&k).unwrap(), k);
                    if t.1 % CHECK == 0 {
                        let (tree, len) = t.0.remove(t.1, &k);
                        t.0 = tree;
                        t.1 = len;
                        assert_eq!(t.0.get(&k), Option::None);
                        t.0.invariant(t.1);
                    }
                }
            }

            #[test]
            fn test_int_insert_remove_rand() { test_insert_remove_rand::<i32>() }

            #[test]
            fn test_str_insert_remove_rand() { test_insert_remove_rand::<String>() }

            #[test]
            fn test_insert_sorted_small() {
                let v: Vec<i32> = vec![1, 9, 16, 11, 7, 12, 8, 12, 12, 11, 9, 12, 9, 7, 16, 9, 1, 9, 1, 1, 22, 112];
                let mut t = avl::Tree::new().insert_sorted(0, v.iter().map(|k| (*k, *k)));
                t.0.invariant(t.1);
                for k in &v {
                    assert_eq!(t.0.get(&k).unwrap(), k)
                }
                t = t.0.remove(t.1, &22i32);
                t = t.0.remove(t.1, &112i32);
                t.0.invariant(t.1);
                for k in &v {
                    if *k == 22i32 || *k == 112i32 {
                        assert_eq!(t.0.get(&k), Option::None);
                    } else {
                        assert_eq!(t.0.get(&k), Option::Some(k));
                    }
                }
                let v2 : Vec<i32> = vec![12i32, 987i32, 19i32, 98i32];
                t = t.0.insert_sorted(t.1, v2.iter().map(|k| (k.clone(), k.clone())));
                for k in &v2 {
                    assert_eq!(t.0.get(&k).unwrap(), k);
                }
            }

            fn test_insert_sorted<T: Ord + Clone + Debug + Rand>() {
                let mut v = randvec::<T>(SIZE);
                v.sort_unstable();
                v.dedup();
                let mut t =
                    avl::Tree::new().insert_sorted(
                        0usize, v.iter().map(|k| (k.clone(), k.clone())));
                t.0.invariant(t.1);
                for k in &v { assert_eq!(t.0.get(&k).unwrap(), k) }
                {
                    let mut i = 0;
                    for k in &v {
                        if i % CHECK == 0 {
                            t = t.0.remove(t.1, &k);
                            t.0.invariant(t.1);
                        }
                        i = i + 1;
                    }
                    i = 0;
                    for k in &v {
                        if i % CHECK == 0 {
                            assert_eq!(t.0.get(&k), Option::None);
                        } else {
                            assert_eq!(t.0.get(&k), Option::Some(k));
                        }
                        i = i + 1;
                    }
                };
                let mut v2 = randvec::<T>(SIZE);
                v2.sort_unstable();
                v2.dedup();
                t = t.0.insert_sorted(t.1, v2.iter().map(|k| (k.clone(), k.clone())));
                t.0.invariant(t.1);
                {
                    let mut i = 0;
                    for k in &v {
                        if i % CHECK != 0 { assert_eq!(t.0.get(&k).unwrap(), k); }
                        i += 1
                    }
                }
                for k in &v2 { assert_eq!(t.0.get(&k).unwrap(), k); }
            }

            #[test]
            fn test_int_insert_sorted() { test_insert_sorted::<i32>() }

            #[test]
            fn test_str_insert_sorted() { test_insert_sorted::<String>() }

            fn test_map_rand<T: Ord + Clone + Debug + Rand>() {
                let v = randvec::<T>(SIZE);
                let mut t = map::Map::new();
                let mut i = 0;
                for k in &v {
                    t = t.insert(k, k).0;
                    assert_eq!(*t.get(&k).unwrap(), k);
                    if i % CHECK == 0 { 
                        t.invariant();
                        for k in &v[0..i] { 
                            assert_eq!(*t.get(&k).unwrap(), k);
                        }
                    }
                    i = i + 1;
                }
                
                i = 0;
                for k in &v {
                    t = t.remove(&k);
                    if i % CHECK == 0 { 
                        t.invariant(); 
                        for k in &v[0..i] {
                            assert_eq!(t.get(&k), Option::None);
                        }
                    }
                    i = i + 1;
                }
            }

            #[test]
            fn test_int_map_rand() { test_map_rand::<i32>() }

            #[test]
            fn test_str_map_rand() { test_map_rand::<String>() }

            fn test_map_iter<T: Borrow<T> + Ord + Clone + Debug + Rand>() {
                let v = randvec::<T>(SIZE);
                let mut t : map::Map<T, T> = map::Map::new();
                for k in &v { t = t.insert(k.clone(), k.clone()).0 };
                t.invariant();
                let mut vs = v.clone(); 
                vs.sort_unstable();
                vs.dedup();
                let mut i = 0;
                for (k0, k1) in &t {
                    assert_eq!(*k0, *k1);
                    assert_eq!(*k0, vs[i]);
                    i = i + 1;
                }
            }

            #[test]
            fn test_int_map_iter() { test_map_iter::<i32>() }

            #[test]
            fn test_string_map_iter() { test_map_iter::<String>() }

            #[test]
            fn test_map_range_small() {
                let mut v = Vec::new();
                v.extend((-5000..5000).into_iter());
                let t = map::Map::new().insert_sorted(v.iter().map(|x| (*x, *x)));
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

            fn test_map_range<T: Borrow<T> + Ord + Clone + Debug + Rand>() {
                let mut v = randvec::<T>(SIZE);
                v.sort_unstable();
                v.dedup();
                let mut t : map::Map<T, T> = map::Map::new();
                t = t.insert_sorted(v.iter().map(|x| (x.clone(), x.clone())));
                t.invariant();
                let (start, end) = loop {
                    let mut r = rand::thread_rng();
                    let i = r.gen_range(0, SIZE - 1);
                    let j = r.gen_range(0, SIZE - 1);
                    if i == j { continue }
                    else if i < j { break (i, j) }
                    else { break (j, i) }
                };
                println!("start: {:?}:{:?} end {:?}:{:?} len {:?}", start, v[start],
                         end, v[end], v.len());
                {
                    let mut i = start;
                    let lbound = Included(v[i].clone());
                    let ubound = Excluded(v[end].clone());
                    for (k0, k1) in t.range(lbound, ubound) {
                        assert_eq!(k0, k1);
                        assert_eq!(k0, &v[i]);
                        assert!(i < end);
                        i += 1;
                    }
                    assert_eq!(i, end);
                }
                {
                    let mut i = start;                
                    let lbound = Excluded(v[i].clone());
                    let ubound = Included(v[end].clone());
                    for (k0, k1) in t.range(lbound, ubound) {
                        assert_eq!(k0, k1);
                        assert_eq!(k0, &v[i + 1]);
                        assert!(i < end);
                        i += 1;
                    }
                    assert_eq!(i, end);
                }
                {
                    let mut i = 0;
                    let lbound = Unbounded;
                    let ubound = Excluded(v[end].clone());
                    for (k0, k1) in t.range(lbound, ubound) {
                        assert_eq!(k0, k1);
                        assert_eq!(k0, &v[i]);
                        assert!(i < end);
                        i += 1;
                    }
                    assert_eq!(i, end);
                }
                {
                    let mut i = end - 1;
                    let lbound = Included(v[start].clone());
                    let ubound = Excluded(v[end].clone());
                    let mut r = t.range(lbound, ubound);
                    while let Some((k0, k1)) = r.next_back() {
                        assert_eq!(k0, k1);
                        assert_eq!(k0, &v[i]);
                        assert!(i >= start);
                        i -= 1;
                    }
                    assert_eq!(start - 1, i);
                }
            }

            #[test]
            fn test_int_map_range() { test_map_range::<i32>() }

            #[test]
            fn test_string_map_range() { test_map_range::<String>() }
        }
    };
}

tests!(rc);
tests!(arc);
