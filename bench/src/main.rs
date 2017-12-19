use std::vec::Vec;
use std::iter::FromIterator;
use std::env;
mod rc;
mod arc;
mod btm;
mod hm;
mod bs;
mod ls;
mod utils;

fn usage() { println!("usage: <arc|rc|btm|bs> <size>") }

fn main() {
  let args = Vec::from_iter(env::args());
  if args.len() != 3 { usage() }
  else {
    let size = args[2].parse::<usize>().unwrap();
    match args[1].as_ref() {
      "rc" => rc::run(size),
      "arc" => arc::run(size),
      "bs" => bs::run(size),
      "avl" => avl::run(size),
      "ls" => ls::run(size),
      "btm" => btm::run(size),
      "hm" => hm::run(size),
      _ => usage() 
    }
  }
}
