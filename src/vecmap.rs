//! A wrapper around a sorted vector of tuples that KSON uses to serialize maps.

use hashbrown::HashMap;
use std::{collections::BTreeMap, hash::*, iter::FromIterator, slice::Iter, vec::IntoIter};

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug, Default)]
/// A map implemented as a sorted `Vec` of pairs.
pub struct VecMap<K: Ord, V>(Vec<(K, V)>);

impl<K: Ord, V> VecMap<K, V> {
    /// Creates a `VecMap` from a vector of key-value pairs sorted by their first
    /// elements.  
    /// # Arguments
    ///
    /// * `v: Vec<(K, V)>` - A vector of key-value pairs sorted by their first element.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// // create `VecMap`
    /// let vmap = VecMap::from_sorted(vec![(1, "foo"), (2, "bar"), (3, "baz")]);
    /// ```
    ///
    /// # Panics
    ///
    /// This function will panic if `v` is not sorted.
    pub fn from_sorted(v: Vec<(K, V)>) -> Self {
        // panic if `v` is not sorted
        // assert!(v.is_sorted_by(|(k1, _), (k2, _)| k1.partial_cmp(k2)));
        VecMap(v)
    }

    /// Returns length.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// // create `VecMap`
    /// let vmap = VecMap::from_sorted(vec![("foo", "bar")]);
    ///
    /// // should have one element
    /// assert_eq!(vmap.len(), 1);
    /// ```
    pub fn len(&self) -> usize { self.0.len() }

    /// Indicates whether or not the `VecMap` is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// // create empty VecMap
    /// let vmap = VecMap::from_sorted(Vec::<(u8, u8)>::new());
    ///
    /// // should return `true`
    /// assert!(vmap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool { self.0.is_empty() }

    /// Returns an `Iter` of the key value pairs.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// // create `VecMap`
    /// let vmap = VecMap::from_sorted(vec![(1, "foo"), (2, "bar"), (3, "baz")]);
    ///
    /// // get first element
    /// let (k, v) = vmap.iter().next().unwrap();
    ///
    /// // should be equal
    /// assert_eq!((k, v), (&1, &"foo"))
    /// ```
    pub fn iter(&self) -> Iter<(K, V)> { self.0.iter() }
}

impl<K: Ord + Hash, V> VecMap<K, V> {
    /// Consumes a `VecMap`, producing a `HashMap` from the entries.
    ///
    /// # Example
    ///
    /// ```
    /// use hashbrown::HashMap;
    /// use kson::prelude::*;
    ///
    /// // create `VecMap`
    /// let vmap = VecMap::from_sorted(vec![(1, "foo"), (2, "bar"), (3, "baz")]);
    ///
    /// // convert to `HashMap`
    /// let hmap: HashMap<u8, &str> = vmap.into_hashmap();
    /// ```
    pub fn into_hashmap<S: BuildHasher + Default>(self) -> HashMap<K, V, S> {
        self.into_iter().collect()
    }
}

impl<K: Ord, V> From<Vec<(K, V)>> for VecMap<K, V> {
    fn from(mut v: Vec<(K, V)>) -> Self {
        v.sort_unstable_by(|(k1, _), (k2, _)| k1.cmp(k2));
        VecMap(v)
    }
}

impl<K: Ord + Hash, V, S: BuildHasher> From<HashMap<K, V, S>> for VecMap<K, V> {
    fn from(hm: HashMap<K, V, S>) -> Self {
        let v: Vec<(K, V)> = hm.into_iter().collect();
        v.into()
    }
}

impl<K: Ord, V> IntoIterator for VecMap<K, V> {
    type IntoIter = IntoIter<(K, V)>;
    type Item = (K, V);

    fn into_iter(self) -> IntoIter<(K, V)> { self.0.into_iter() }
}

impl<K: Ord, V> FromIterator<(K, V)> for VecMap<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> VecMap<K, V> {
        VecMap::from(Vec::from_iter(iter))
    }
}

impl<K: Ord, V> From<BTreeMap<K, V>> for VecMap<K, V> {
    fn from(bt: BTreeMap<K, V>) -> Self { Self::from_iter(bt) }
}
