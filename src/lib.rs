//#![forbid(unsafe_code)]
//! Immutable maps and sets. See map and set modules for details.

//#[macro_use] extern crate lazy_static;

pub(crate) mod chunk;
pub(crate) mod avl;
pub mod map;
pub mod set;

#[cfg(test)]
mod tests;
