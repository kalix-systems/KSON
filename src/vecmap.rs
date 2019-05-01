use hashbrown::HashMap;

use std::{
    collections::BTreeMap, hash::*, iter::FromIterator, ops::Deref, slice::Iter, vec::IntoIter,
};

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug, Default)]
pub struct VecMap<K: Ord, V>(Vec<(K, V)>);

impl<K: Ord, V> VecMap<K, V> {
    pub fn new() -> VecMap<K, V> { VecMap(Vec::new()) }

    pub fn with_capacity(cap: usize) -> VecMap<K, V> { VecMap(Vec::with_capacity(cap)) }

    pub fn from_sorted(v: Vec<(K, V)>) -> Self {
        assert!(v.is_sorted_by(|(k1, _), (k2, _)| k1.partial_cmp(k2)));
        VecMap(v)
    }

    pub fn len(&self) -> usize { self.0.len() }

    pub fn is_empty(&self) -> bool { self.0.is_empty() }

    pub fn iter(&self) -> Iter<(K, V)> { self.0.iter() }
}

impl<K: Ord + Hash, V> VecMap<K, V> {
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
