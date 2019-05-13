use std::{error::Error, fmt};

#[derive(Debug, Clone, Default)]
/// An error encountered when decoding fails.
pub struct DecodingError(pub String);

impl DecodingError {
    /// Creates a new `DecodingError`
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
/// An error encountered when a type-conversion from `Kson` fails.
pub struct KsonConversionError(pub String);

impl Error for KsonConversionError {}

impl KsonConversionError {
    /// Creates a new `KsonConversionError`
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
            "Conversion {line}::{column} with error: {error}",
            line = line!(),
            column = column!(),
            error = self.0,
        )
    }
}
