//! Errors that can be encountered when working with KSON.
//!
//! KSON defines two types of errors:
//!
//! * [`DecodingError`](`crate::errors::DecodingError`) - An error indicating that the
//!   deserialization has encountered an error, with an error message describing what went
//!   wrong.
//!
//! * [`KsonConversionError`] - An error indicating that a value could not be successfully
//!   converted from [`Kson`](`crate::Kson`).
//!
//! # Example: `DecodingError`
//!
//!
//! # Example: `KsonConversionError`
//!
//! ```
//! use kson::prelude::*;
//!
//! let ks_null = Kson::Null;
//!
//! // This conversion will not succeed in a sane world.
//! match i32::from_kson(ks_null) {
//!     Err(e) => println!("{}", e), // print the message describing what went wrong
//!     Ok(value) => panic!("Nothing makes sense anymore"),
//! }
//! ```

use std::{error::Error, fmt};

#[derive(Debug, Clone, Default)]
/// An error encountered when decoding fails.
pub struct DecodingError(pub String);

impl DecodingError {
    /// Creates a new [`DecodingError`].
    ///
    /// # Arguments
    ///
    /// * `s: & str` - The message associated with the error.
    pub fn new(s: &str) -> Self { DecodingError(s.to_string()) }
}

impl Error for DecodingError {}

impl fmt::Display for DecodingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Decoding failed at {line}::{column} with error: {error}",
            line = line!(),
            column = column!(),
            error = self.0,
        )
    }
}

#[derive(Debug, Clone, Default)]
/// An error encountered when a type-conversion from [`Kson`](`crate::Kson`) fails.
pub struct KsonConversionError(pub String);

impl Error for KsonConversionError {}

impl KsonConversionError {
    /// Creates a new [`KsonConversionError`]
    ///
    /// # Arguments
    ///
    /// * `s: & str` - The message associated with the error.
    pub fn new(s: &str) -> Self { KsonConversionError(s.to_string()) }
}

impl fmt::Display for KsonConversionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Conversion failed at {line}::{column} with error: {error}",
            line = line!(),
            column = column!(),
            error = self.0,
        )
    }
}
