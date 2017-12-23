//! Support for common functional data structures in rust. Each data structure
//! is implemented with either Rc, or `Arc`. The `Rc` versions cannot be used by
//! multiple threads at once, but have slightly lower single threaded overhead.
//! Each module is duplicated for rc/arc. e.g. `rc::map` uses `Rc`, `arc::map` uses `Arc`.

#[macro_use]
mod macros;

/// immutable data structures using `Rc`
pub mod rc {
  pub(crate) mod avl {
    avltree!(std::rc::Rc, Rc, Rc::new, 512);
  }

  /// A Map implemented using a cache efficient balanced binary tree
  pub mod map {
    map!(rc::avl);
  }
}

/// immutable data structures using `Arc`
pub mod arc {
  pub(crate) mod avl {
    avltree!(std::sync::Arc, Arc, Arc::new, 512);
  }

  /// A Map implemented using a cache efficient balanced binary tree
  pub mod map {
    map!(arc::avl);
  }
}

#[cfg(test)]
mod tests;
