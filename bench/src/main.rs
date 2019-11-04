use std::{
    iter::FromIterator,
    env,
    collections::{HashMap, BTreeMap},
};

mod utils;
mod gen;
use gen::{Bench, CMWrap};

fn usage() {
    println!("usage: <cm_ptr|cm_str|btm_ptr|btm_str|hm_ptr|hm_str> <size>")
}

fn main() {
    let args = Vec::from_iter(env::args());
    if args.len() != 3 { usage() }
    else {
        let size = args[2].parse::<usize>().unwrap();
        match args[1].as_ref() {
            "cm_ptr" => Bench<CMWrap<usize, usize>>::run(size),
            "cm_str" => Bench<CMWrap<Arc<String>, Arc<String>>::run(size),
            "btm_ptr" => Bench<BTreeMap<usize, usize>>::run(size),
            "btm_str" => Bench<BTreeMap<Arc<String>, Arc<String>>>::run(size),
            "hm_ptr" => Bench<HashMap<usize, usize>>::run(size),
            "hm_str" => Bench<HashMap<Arc<String>, Arc<String>>>::run(size),
            _ => usage() 
        }
    }
}
