use std::vec::Vec;
use std::iter::FromIterator;
use std::env;
mod rc;
mod arc;
mod btm;
mod utils;

fn usage() { println!("usage: <arc|rc|btm> <size>") }

fn main() {
  let args = Vec::from_iter(env::args());
  if args.len() != 3 { usage() }
  else {
    let size = args[2].parse::<usize>().unwrap();
    match args[1].as_ref() {
      "rc" => rc::run(size),
      "arc" => arc::run(size),
      "btm" => btm::run(size),
      _ => usage() 
    }
  }
}
