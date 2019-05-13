//! Errors that can be encountered when working with KSON.
//!
//! KSON defines two types of errors:
//!
//! * [`DecodingError`](`crate::errors::DecodingError`) - An error indicating that the
//!   deserialization has encountered a problem, with an error message describing what
//!   went wrong.
//!
//! * [`KsonConversionError`] - An error indicating that a value could not be successfully
//!   converted from [`Kson`](`crate::Kson`).

use std::{error::Error, fmt};

#[derive(Debug, Clone, Default)]
/// An error encountered when decoding fails.
///
/// # Example
///
/// ```
/// use kson::prelude::*;
///
/// // This is an invalid tag byte.
/// // It starts with `000`, so it should be a constant,
/// // but it's not part of the specification.
/// let bad_tag = &mut vec![0b0001_0000].into_buf();
///
/// // this will fail
/// match decode(bad_tag) {
///     Err(e) => println!("{}", e), // print message describing failure
///     //        ^-- prints: [src/errors.rs:70:22] Decoding failed with error: Encountered unknown constant `10000` while reading tag
///     Ok(v) => panic!(),
/// }
/// ```
pub struct DecodingError(pub String);

impl DecodingError {
    /// Creates a new [`DecodingError`].
    ///
    /// # Arguments
    ///
    /// * `s: & str` - The message associated with the error.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let err = DecodingError::new("This is not a helpful error message");
    /// ```
    pub fn new(s: &str) -> Self { DecodingError(s.to_string()) }
}

impl Error for DecodingError {}

impl fmt::Display for DecodingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "[{file}:{line}:{column}] Decoding failed with error: {error}",
            file = file!(),
            line = line!(),
            column = column!(),
            error = self.0,
        )
    }
}

#[derive(Debug, Clone, Default)]
/// An error encountered when a type-conversion from [`Kson`](`crate::Kson`) fails.
///
/// ```
/// use kson::prelude::*;
///
/// let ks_null = Kson::Null;
///
/// // This conversion will not succeed in a sane world.
/// match i32::from_kson(ks_null) {
///     Err(e) => println!("{}", e), // print the message describing what went wrong
///     Ok(value) => panic!("Nothing makes sense anymore"),
/// }
/// ```
pub struct KsonConversionError(pub String);

impl Error for KsonConversionError {}

impl KsonConversionError {
    /// Creates a new [`KsonConversionError`]
    ///
    /// # Arguments
    ///
    /// * `s: & str` - The message associated with the error.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let err = KsonConversionError::new("This is not a helpful error message");
    /// ```
    pub fn new(s: &str) -> Self { KsonConversionError(s.to_string()) }
}

impl fmt::Display for KsonConversionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "[{file}:{line}:{column}] Conversion failed with error: {error}",
            file = file!(),
            line = line!(),
            column = column!(),
            error = self.0,
        )
    }
}
