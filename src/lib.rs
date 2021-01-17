#![forbid(unsafe_code)]
//! Immutable maps and sets. See map and set modules for details.

#[macro_use] extern crate packed_struct_codegen;

pub(crate) mod chunk;
pub(crate) mod avl;
pub(crate) mod cached_avl;
pub mod map;
pub mod map_c;
pub mod set;

#[cfg(test)]
mod tests;
