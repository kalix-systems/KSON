use std::{error::Error, fmt};

#[derive(Debug, Clone, Default)]
pub struct DecodingError(pub String);

impl DecodingError {
    pub fn new(s: &str) -> Self { DecodingError(s.to_string()) }
}

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
pub struct KsonConversionError(pub String);

impl KsonConversionError {
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
