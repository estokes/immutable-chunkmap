use avl::{Tree, Iter};
use std::{
    cmp::{PartialEq, Eq, PartialOrd, Ord, Ordering},
    fmt::{self, Debug, Formatter}, borrow::Borrow,
    ops::Bound, default::Default, iter::FromIterator,
    hash::{Hash, Hasher}
};
/// This set uses a similar strategy to BTreeSet to ensure cache
/// efficient performance on modern hardware while still providing
/// log(N) get, insert, and remove operations.
/// # Examples
/// ```
/// use std::string::String;
/// use self::immutable_chunkmap::set::Set;
///
/// let m =
///    Set::new()
///    .insert(String::from("1")).0
///    .insert(String::from("2")).0
///    .insert(String::from("3")).0;
///
/// assert_eq!(m.contains("1"), true);
/// assert_eq!(m.contains("2"), true);
/// assert_eq!(m.contains("3"), true);
/// assert_eq!(m.contains("4"), false);
///
/// for k in &m { println!("{}", k) }
/// ```
#[derive(Clone)]
pub struct Set<K: Ord + Clone> {
    len: usize,
    root: Tree<K, ()>
}

impl<K> Hash for Set<K> where K: Hash + Ord + Clone {
    fn hash<H: Hasher>(&self, state: &mut H) { self.root.hash(state) }
}

impl<K> Default for Set<K>
where K: Ord + Clone { fn default() -> Set<K> { Set::new() } }

impl<K> PartialEq for Set<K> where K: Ord + Clone {
    fn eq(&self, other: &Set<K>) -> bool {
        self.len == other.len && self.root == other.root
    }
}

impl<K> Eq for Set<K> where K: Eq + Ord + Clone {}

impl<K> PartialOrd for Set<K> where K: Ord + Clone {
    fn partial_cmp(&self, other: &Set<K>) -> Option<Ordering> {
        self.root.partial_cmp(&other.root)
    }
}

impl<K> Ord for Set<K> where K: Ord + Clone {
    fn cmp(&self, other: &Set<K>) -> Ordering { self.root.cmp(&other.root) }
}

impl<K> Debug for Set<K> where K: Debug + Ord + Clone {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_set().entries(self.into_iter()).finish()
    }
}

impl<K> FromIterator<K> for Set<K>
where K: Ord + Clone {
    fn from_iter<T: IntoIterator<Item=K>>(iter: T) -> Self {
        Set::new().insert_many(iter)
    }
}

pub struct SetIter<'a, Q: Ord, K: 'a + Clone + Ord + Borrow<Q>>(
    Iter<'a, Q, K, ()>
);

impl<'a, Q, K> Iterator for SetIter<'a, Q, K>
where Q: Ord, K: 'a + Clone + Ord + Borrow<Q> {
    type Item = &'a K;
    fn next(&mut self) -> Option<Self::Item> { self.0.next().map(|(k, ())| k) }
}

impl<'a, Q, K> DoubleEndedIterator for SetIter<'a, Q, K>
where Q: Ord, K: 'a + Clone + Ord + Borrow<Q> {
    fn next_back(&mut self) -> Option<Self::Item> { self.0.next_back().map(|(k, ())| k) }
}

impl<'a, K> IntoIterator for &'a Set<K>
where
    K: 'a + Borrow<K> + Ord + Clone,
{
    type Item = &'a K;
    type IntoIter = SetIter<'a, K, K>;
    fn into_iter(self) -> Self::IntoIter { SetIter(self.root.into_iter()) }
}

impl<K> Set<K> where K: Ord + Clone {
    /// Create a new empty set
    pub fn new() -> Self { Set { len: 0, root: Tree::new() } }

    /// This will insert many elements at once, and is
    /// potentially a lot faster than inserting one by one,
    /// especially if the data is sorted.
    ///
    /// #Examples
    ///```
    /// use self::immutable_chunkmap::set::Set;
    ///
    /// let mut v = vec![1, 10, -12, 44, 50];
    /// v.sort_unstable();
    ///
    /// let m = Set::new().insert_many(v.iter().map(|k| *k));
    ///
    /// for k in &v {
    ///   assert_eq!(m.contains(k), true)
    /// }
    /// ```
    pub fn insert_many<E: IntoIterator<Item=K>>(
        &self, elts: E
    ) -> Self {
        let (root, len) =
            self.root.insert_many(self.len, elts.into_iter().map(|k| (k, ())));
        Set { len, root }
    }

    /// Remove multiple elements in a single pass. Similar performance
    /// to insert_many.
    pub fn remove_many<E, F>(&self, elts: E) -> Self
    where E: IntoIterator<Item=K> {
        let (root, len) =
            self.root.update_many(
                self.len, elts.into_iter().map(|k| (k, ())),
                &mut |_, _, _| None);
        Set { len, root }
    }
    
    /// return a new set with k inserted into it. If k already
    /// exists in the old set return true, else false. If the
    /// element already exists in the set memory will not be
    /// allocated.
    pub fn insert(&self, k: K) -> (Self, bool) {
        if self.contains(&k) { (self.clone(), true) }
        else {
            let (root, len, _) = self.root.insert(self.len, k, ());
            (Set {len, root}, false)
        }
    }

    /// return true if the set contains k, else false. Runs in
    /// log(N) time and constant space. where N is the size of
    /// the set.
    pub fn contains<'a, Q>(&'a self, k: &Q) -> bool
    where Q: ?Sized + Ord, K: Borrow<Q>
    { self.root.get(k).is_some() }

    /// return a reference to an item in the set if any that is equal to the given value.
    pub fn get<'a, Q>(&'a self, k: &Q) -> Option<&K>
    where Q: ?Sized + Ord, K: Borrow<Q> {
        self.root.get_key(k)
    }

    /// return a new set with k removed. Runs in log(N) time
    /// and log(N) space, where N is the size of the set
    pub fn remove<Q: Sized + Ord>(&self, k: &Q) -> (Self, bool)
    where K: Borrow<Q>
    {
        let (t, len, prev) = self.root.remove(self.len, k);
        (Set {root: t, len: len}, prev.is_some())
    }

    /// get the number of elements in the map O(1) time and space
    pub fn len(&self) -> usize { self.len }

    /// return an iterator over the subset of elements in the
    /// set that are within the specified range.
    ///
    /// The returned iterator runs in O(log(N) + M) time, and
    /// constant space. N is the number of elements in the
    /// tree, and M is the number of elements you examine.
    ///
    /// if lbound >= ubound the returned iterator will be empty
    pub fn range<'a, Q>(
        &'a self, lbound: Bound<Q>, ubound: Bound<Q>
    ) -> SetIter<'a, Q, K>
    where Q: Ord, K: 'a + Clone + Ord + Borrow<Q> {
        SetIter(self.root.range(lbound, ubound))
    }
}

impl<K> Set<K> where K: Ord + Clone + Debug {
    #[allow(dead_code)]
    pub(crate) fn invariant(&self) -> () { self.root.invariant(self.len) }
}
