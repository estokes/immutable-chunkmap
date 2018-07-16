use std::vec::Vec;
use std::iter::FromIterator;
use std::env;
mod cm;
mod btm;
mod hm;
mod bs;
mod avl;
mod ls;
mod vec;
mod utils;

fn usage() { println!("usage: <arc|rc|btm|bs> <size>") }

fn main() {
    let args = Vec::from_iter(env::args());
    if args.len() != 3 { usage() }
    else {
        let size = args[2].parse::<usize>().unwrap();
        match args[1].as_ref() {
            "cm" => cm::run(size),
            "bs" => bs::run(size),
            "avl" => avl::run(size),
            "ls" => ls::run(size),
            "btm" => btm::run(size),
            "hm" => hm::run(size),
            "vec" => vec::run(size),
            _ => usage() 
        }
    }
}
