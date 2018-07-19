#![forbid(unsafe_code)]
//! Immutable maps and sets. See map and set modules for details.
extern crate arrayvec;

pub(crate) mod avl;
pub mod map;
pub mod set;

#[cfg(test)]
mod tests;
