use crate::avl::{Iter, Tree};
use std::{
    borrow::Borrow,
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    default::Default,
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
    iter::FromIterator,
    ops::Bound,
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
pub struct Set<K: Ord + Clone>(Tree<K, ()>);

impl<K> Hash for Set<K>
where
    K: Hash + Ord + Clone,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl<K> Default for Set<K>
where
    K: Ord + Clone,
{
    fn default() -> Set<K> {
        Set::new()
    }
}

impl<K> PartialEq for Set<K>
where
    K: Ord + Clone,
{
    fn eq(&self, other: &Set<K>) -> bool {
        self.0 == other.0
    }
}

impl<K> Eq for Set<K> where K: Eq + Ord + Clone {}

impl<K> PartialOrd for Set<K>
where
    K: Ord + Clone,
{
    fn partial_cmp(&self, other: &Set<K>) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<K> Ord for Set<K>
where
    K: Ord + Clone,
{
    fn cmp(&self, other: &Set<K>) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<K> Debug for Set<K>
where
    K: Debug + Ord + Clone,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_set().entries(self.into_iter()).finish()
    }
}

impl<K> FromIterator<K> for Set<K>
where
    K: Ord + Clone,
{
    fn from_iter<T: IntoIterator<Item = K>>(iter: T) -> Self {
        Set::new().insert_many(iter)
    }
}

pub struct SetIter<'a, Q: Ord, K: Clone + Ord + Borrow<Q>>(Iter<'a, Q, K, ()>);

impl<'a, Q, K> Iterator for SetIter<'a, Q, K>
where
    Q: Ord,
    K: Clone + Ord + Borrow<Q>,
{
    type Item = &'a K;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, ())| k)
    }
}

impl<'a, Q, K> DoubleEndedIterator for SetIter<'a, Q, K>
where
    Q: Ord,
    K: Clone + Ord + Borrow<Q>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(k, ())| k)
    }
}

impl<'a, K> IntoIterator for &'a Set<K>
where
    K: Borrow<K> + Ord + Clone,
{
    type Item = &'a K;
    type IntoIter = SetIter<'a, K, K>;
    fn into_iter(self) -> Self::IntoIter {
        SetIter(self.0.into_iter())
    }
}

impl<K> Set<K>
where
    K: Ord + Clone,
{
    /// Create a new empty set
    pub fn new() -> Self {
        Set(Tree::new())
    }

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
    pub fn insert_many<E: IntoIterator<Item = K>>(&self, elts: E) -> Self {
        let root = self.0.insert_many(elts.into_iter().map(|k| (k, ())));
        Set(root)
    }

    /// Remove multiple elements in a single pass. Similar performance
    /// to insert_many.
    pub fn remove_many<Q, E>(&self, elts: E) -> Self
    where
        Q: Ord,
        K: Borrow<Q>,
        E: IntoIterator<Item = Q>,
    {
        let root = self
            .0
            .update_many(elts.into_iter().map(|k| (k, ())), &mut |_, _, _| None);
        Set(root)
    }

    /// This is just slightly wierd, however if you have a bunch of
    /// borrowed forms of members of the set, and you want to look at
    /// the real entries and possibly add/update/remove them, then
    /// this method is for you.
    pub fn update_many<Q, E, F>(&self, elts: E, mut f: F) -> Self
    where
        Q: Ord,
        K: Borrow<Q>,
        E: IntoIterator<Item = Q>,
        F: FnMut(Q, Option<&K>) -> Option<K>,
    {
        let root = self
            .0
            .update_many(elts.into_iter().map(|k| (k, ())), &mut |q, (), cur| {
                let cur = cur.map(|(k, ())| k);
                f(q, cur).map(|k| (k, ()))
            });
        Set(root)
    }

    /// return a new set with k inserted into it. If k already
    /// exists in the old set return true, else false. If the
    /// element already exists in the set memory will not be
    /// allocated.
    pub fn insert(&self, k: K) -> (Self, bool) {
        if self.contains(&k) {
            (self.clone(), true)
        } else {
            (Set(self.0.insert(k, ()).0), false)
        }
    }

    /// return true if the set contains k, else false. Runs in
    /// log(N) time and constant space. where N is the size of
    /// the set.
    pub fn contains<'a, Q>(&'a self, k: &Q) -> bool
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        self.0.get(k).is_some()
    }

    /// return a reference to the item in the set that is equal to the
    /// given value, or None if no such value exists.
    pub fn get<'a, Q>(&'a self, k: &Q) -> Option<&K>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
    {
        self.0.get_key(k)
    }

    /// return a new set with k removed. Runs in log(N) time
    /// and log(N) space, where N is the size of the set
    pub fn remove<Q: Sized + Ord>(&self, k: &Q) -> (Self, bool)
    where
        K: Borrow<Q>,
    {
        let (t, prev) = self.0.remove(k);
        (Set(t), prev.is_some())
    }

    /// return the union of 2 sets. Runs in O(log(N) + M) time and
    /// space, where N is the largest of the two sets, and M is the
    /// number of chunks that intersect, which is roughly proportional
    /// to the size of the intersection.
    ///
    /// # Examples
    /// ```
    /// use std::iter::FromIterator;
    /// use self::immutable_chunkmap::set::Set;
    ///
    /// let s0 = Set::from_iter(0..10);
    /// let s1 = Set::from_iter(5..15);
    /// let s2 = s0.union(&s1);
    /// for i in 0..15 {
    ///     assert!(s2.contains(&i));
    /// }
    /// ```
    pub fn union(&self, other: &Set<K>) -> Self {
        Set(Tree::union(&self.0, &other.0, &mut |_, (), ()| Some(())))
    }

    /// return the intersection of 2 sets. Runs in O(log(N) + M) time
    /// and space, where N is the smallest of the two sets, and M is
    /// the number of intersecting chunks.
    ///
    /// # Examples
    /// use std::iter::FromIterator;
    /// use self::immutable_chunkmap::set::Set;
    ///
    /// let s0 = Set::from_iter(0..100);
    /// let s1 = Set::from_iter(20..50);
    /// let s2 = s0.intersect(&s1);
    ///
    /// assert!(s2.len() == 30);
    /// for i in 0..100 {
    ///     if i < 20 || i >= 50 {
    ///         assert!(!s2.contains(&i));
    ///     } else {
    ///         assert!(s2.contains(&i));
    ///     }
    /// }
    pub fn intersect(&self, other: &Set<K>) -> Self {
        Set(Tree::intersect(&self.0, &other.0, &mut |_, (), ()| Some(())))
    }

    /// Return the difference of two sets. Runs in O(log(N) + M) time
    /// and space, where N is the smallest of the two sets, and M is
    /// the number of intersecting chunks.
    ///
    /// # Examples
    /// ```
    /// use std::iter::FromIterator;
    /// use self::immutable_chunkmap::set::Set;
    ///
    /// let s0 = Set::from_iter(0..100);
    /// let s1 = Set::from_iter(0..50);
    /// let s2 = s0.diff(&s1);
    ///
    /// assert!(s2.len() == 50);
    /// for i in 0..50 {
    ///     assert!(!s2.contains(&i));
    /// }
    /// for i in 50..100 {
    ///     assert!(s2.contains(&i));
    /// }
    /// ```
    pub fn diff(&self, other: &Set<K>) -> Self where K: Debug {
        Set(Tree::diff(&self.0, &other.0, &mut |_, (), ()| None))
    }

    /// get the number of elements in the map O(1) time and space
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// return an iterator over the subset of elements in the
    /// set that are within the specified range.
    ///
    /// The returned iterator runs in O(log(N) + M) time, and
    /// constant space. N is the number of elements in the
    /// tree, and M is the number of elements you examine.
    ///
    /// if lbound >= ubound the returned iterator will be empty
    pub fn range<'a, Q>(&'a self, lbound: Bound<Q>, ubound: Bound<Q>) -> SetIter<'a, Q, K>
    where
        Q: Ord,
        K: 'a + Clone + Ord + Borrow<Q>,
    {
        SetIter(self.0.range(lbound, ubound))
    }
}

impl<K> Set<K>
where
    K: Ord + Clone + Debug,
{
    #[allow(dead_code)]
    pub(crate) fn invariant(&self) -> () {
        self.0.invariant()
    }
}
