//! A cache efficient immutable map with lookup performance equivalent to BTreeMap, and reasonably good
//! insertion performance (for a persistent structure). The `Rc` versions cannot be used by multiple
//! threads at once, but have slightly lower single threaded overhead. Each module is duplicated for
//! rc/arc. e.g. `rc::map` uses `Rc`, `arc::map` uses `Arc`.

extern crate arrayvec;

#[macro_use]
mod macros;

/// chunkmap using `Rc` pointers
pub mod rc {
  pub(crate) mod avl {
    avltree!(std::rc::Rc, Rc, Rc::new, 512);
  }

  /// A Map implemented using a cache efficient balanced binary tree
  pub mod map {
    map!(rc::avl);
  }
}

/// chunkmap using `Arc` pointers
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
