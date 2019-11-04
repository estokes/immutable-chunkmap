use std::{
    iter::FromIterator,
    env,
    collections::{HashMap, BTreeMap},
};

mod utils;
mod gen;
use gen::{Bench, CMWrap};

fn usage() {
    println!("usage: <cm|btm|hm> <ptr|str> <size>")
}

fn main() {
    let args = Vec::from_iter(env::args());
    if args.len() != 4 { usage() }
    else {
        let size = args[3].parse::<usize>().unwrap();
        match (&args[1], &args[2]) {
            ("cm", "ptr") => Bench<CMWrap<usize, usize>>::run(size),
            ("cm", "str") => Bench<CMWrap<Arc<String>, Arc<String>>::run(size),
            ("btm", "ptr") => Bench<BTreeMap<usize, usize>>::run(size),
            ("btm", "str") => Bench<BTreeMap<Arc<String>, Arc<String>>>::run(size),
            ("hm", "ptr") => Bench<HashMap<usize, usize>>::run(size),
            ("hm", "str") => Bench<HashMap<Arc<String>, Arc<String>>>::run(size),
            _ => usage() 
        }
    }
}
