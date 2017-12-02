use std::vec::Vec;
use std::iter::FromIterator;
use std::env;
mod rc;
mod arc;
mod utils;

enum Kind {
  Rc,
  Arc
}

fn main() {
  let args = Vec::from_iter(env::args());
  let (typ, size) =
    if args.len() != 3 { (Kind::Rc, 10000) }
    else {
      (match args[1].as_ref() {
         "rc" => Kind::Rc,
         "arc" => Kind::Arc,
         typ => panic!("invalid test type, {}, use rc or arc", typ)
       },
       args[2].parse::<usize>().unwrap())
    } ;
  match typ {
    Kind::Rc => rc::run(size),
    Kind::Arc => arc::run(size)
  }
}
