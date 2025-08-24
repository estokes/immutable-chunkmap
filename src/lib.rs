//! Immutable maps and sets. See map and set modules for details.

#![cfg_attr(not(any(feature = "rayon", feature = "pool")), no_std)]

extern crate alloc;

pub(crate) mod avl;
pub(crate) mod chunk;
pub mod map;
pub mod pool;
pub mod set;

#[cfg(test)]
mod tests;
