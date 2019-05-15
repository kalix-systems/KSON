use std::ops::{Deref, DerefMut};

/// A value that can be temporarily `rented`, modified, and then replaced.
/// It's just a wrapper over `Option`.
#[derive(Eq, PartialEq, Hash, Debug)]
pub(crate) struct Rentable<T> {
    value: Option<T>,
}

impl<T> Rentable<T> {
    /// Creates a new `Rentable` value.
    pub(crate) fn new(value: T) -> Rentable<T> { Rentable { value: Some(value) } }

    /// Is the value currently rented out?
    pub(crate) fn is_rented(&self) -> bool { self.value.is_none() }

    /// Rents the value.
    pub(crate) fn rent(&mut self) -> T {
        assert!(!self.is_rented());
        self.value.take().unwrap()
    }

    /// Returns the value after renting is done.
    pub(crate) fn replace(&mut self, val: T) {
        assert!(self.is_rented());
        self.value = Some(val);
    }
}

impl<T> Deref for Rentable<T> {
    type Target = T;

    fn deref(&self) -> &T {
        match &self.value {
            None => panic!("value is rented"),
            Some(r) => r,
        }
    }
}

impl<T> DerefMut for Rentable<T> {
    fn deref_mut(&mut self) -> &mut T {
        match &mut self.value {
            None => panic!("value is rented"),
            Some(r) => r,
        }
    }
}
