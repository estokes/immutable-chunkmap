//! Immutable maps and sets. See map and set modules for details.

pub(crate) mod chunk;
pub(crate) mod avl;
pub mod map;
pub mod set;

#[cfg(test)]
mod tests;
