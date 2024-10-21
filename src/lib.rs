//! Immutable maps and sets. See map and set modules for details.

#![cfg_attr(not(feature = "rayon"), no_std)]

extern crate alloc;

pub(crate) mod chunk;
pub(crate) mod avl;
pub mod map;
pub mod set;

#[cfg(test)]
mod tests;
