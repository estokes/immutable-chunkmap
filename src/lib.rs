#[macro_use]
mod macros;

pub mod rc {
  pub(crate) mod avl {
    avltree!(std::rc::Rc, Rc, Rc::new, 1024);
  }

  pub mod map {
    map!(rc::avl);
  }
}

pub mod arc {
  pub(crate) mod avl {
    avltree!(std::sync::Arc, Arc, Arc::new, 1024);
  }

  pub mod map {
    map!(arc::avl);
  }
}

#[cfg(test)]
mod tests;
