//! Immutable maps and sets. See map and set modules for details.

#[macro_use] extern crate packed_struct_codegen;

pub(crate) mod chunk;
pub(crate) mod avl;
pub mod map;
pub mod cached_map;
pub mod set;

#[cfg(test)]
mod tests;
