macro_rules! tests {
    ($p:ident) => {
        mod $p {
            extern crate rand;
            use $p::avl;
            use $p::map;
            use tests::$p::rand::Rng;
            use std::{iter::{IntoIterator}, vec::{Vec}, fmt::Debug, borrow::Borrow};

            const STRSIZE: usize = 10;
            const SIZE: usize = 100000;
            const CHECK: usize = 1000;

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
                let mut t = (avl::Tree::new(), 0);
                for i in r {
                    t = t.0.insert(t.1, &i, &i);
                    if t.1 % CHECK == 0 { t.0.invariant(t.1); }
                }
                t.0.invariant(t.1);
                t
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
                let mut t = (avl::Tree::new(), 0);
                for k in &v {
                    t = t.0.insert(t.1, &k, &k);
                    assert_eq!(*t.0.get(&k).unwrap(), k);
                    if t.1 % CHECK == 0 {
                        t = t.0.remove(t.1, &k);
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
                let pairs: Vec<(&i32, &i32)> = v.iter().map(|k| (k, k)).collect();
                let mut t = avl::Tree::new().insert_sorted(0usize, &pairs);
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
                let v2 = vec![12i32, 987i32, 19i32, 98i32];
                let pairs2 : Vec<(&i32, &i32)> = v2.iter().map(|k| (k, k)).collect();
                t = t.0.insert_sorted(t.1, &pairs2);
                for k in &v2 {
                    assert_eq!(t.0.get(&k).unwrap(), k);
                }
            }

            fn test_insert_sorted<T: Ord + Clone + Debug + Rand>() {
                let v = randvec::<T>(SIZE);
                let pairs: Vec<(&T, &T)> = v.iter().map(|k| (k, k)).collect();
                let mut t = avl::Tree::new().insert_sorted(0usize, &pairs);
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
                            assert_eq!(t.0.get(&k).unwrap(), k);
                        }
                        i = i + 1;
                    }
                };
                let v2 = randvec::<T>(SIZE);
                let pairs2 : Vec<(&T, &T)> = v2.iter().map(|k| (k, k)).collect();
                t = t.0.insert_sorted(t.1, &pairs2);
                t.0.invariant(t.1);
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
                    t = t.insert(&k, &k);
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
                for k in &v { t = t.insert(&k, &k) };
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
        }
    };
}

tests!(rc);
tests!(arc);
