//! A wrapper around a sorted vector of tuples that KSON uses to serialize maps.
//!
//! This data structure is mostly for internal use, but it has several methods that can
//! provide some flexibility when constructing and processing KSON [maps][`Kson::Map`].
//!
//! # Example
//!
//! ```
//! use std::collections::HashMap;
//! use kson::prelude::*;
//! use std::collections::BTreeMap;
//!
//! let key = Bytes::from_buf("a");
//! let value = 1;
//!
//! // from a `BTreeMap`
//! let mut btmap = BTreeMap::new();
//! btmap.insert(key.clone(), value);
//!
//! let bt_vm = VecMap::from(btmap);
//!
//! // from a `HashMap`
//! let mut hashmap = HashMap::new();
//! hashmap.insert(key.clone(), value);
//!
//! let hm_vm = VecMap::from(hashmap);
//!
//! // from a vector of tuples
//! let entries = vec![(key.clone(), value)];
//!
//! let vec_vm = VecMap::from(entries);
//!
//! // From a vector of tuples we know is sorted by the keys.
//! // This is still checked and the function panics if it is not sorted,
//! // but this is in `O(n)` instead of `O(log(n))`
//! let entries = vec![(key.clone(), value)];
//!
//! let vec_vm = VecMap::from_sorted(entries);
//! ```

use std::{
    collections::{BTreeMap, HashMap},
    hash::*,
    iter::FromIterator,
    slice::Iter,
    vec::IntoIter,
};

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug, Default)]
/// A map implemented as a sorted [`Vec`] of pairs.
///
/// See also: [module level documentation](`crate::vecmap`).
pub struct VecMap<K: Ord, V>(Vec<(K, V)>);

impl<K: Ord, V> VecMap<K, V> {
    /// Creates a [`VecMap`] from a vector of key-value pairs sorted by their first
    /// elements.  
    ///
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
    /// This function will panic if `v` is not sorted by its first element.
    /// This requirement is strict, and keys must be unique.
    ///
    /// For example, this will panic because it is not sorted:
    ///
    /// ```should_panic
    /// use kson::prelude::*;
    ///
    /// let vmap = VecMap::from_sorted(vec![("b", ""), ("a", "")]);
    /// ```
    ///
    /// And so will this, because the keys are not unique:
    ///
    /// ```should_panic
    /// use kson::prelude::*;
    ///
    /// let vmap = VecMap::from_sorted(vec![("a", ""), ("a", "")]);
    /// ```
    pub fn from_sorted(v: Vec<(K, V)>) -> Self {
        for i in 1..v.len() {
            if v[i - 1].0 >= v[i].0 {
                panic!("`Vec` is not sorted by key")
            }
        }
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

    /// Indicates whether the [`VecMap`] is empty.
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

    /// Returns an [`Iter`] of the key value pairs.
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
    /// Consumes a [`VecMap`], producing a [`HashMap`] from the entries.
    ///
    /// # Example
    ///
    /// ```
    /// use std::collections::HashMap;
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
