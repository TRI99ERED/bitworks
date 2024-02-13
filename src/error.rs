//! Module containing [`ConvError`] and [`ConvTarget`].

use std::{
    error::Error,
    fmt::{Debug, Display},
};

pub type ConvResult<T> = Result<T, ConvError>;

/// Target or instigator for conversions.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ConvTarget {
    /// Represents [`Bitset`][crate::bitset::Bitset], bit size of which is contained inside.
    Set(usize),
    /// Represents [`Index`][crate::index::Index], max value of which is contained inside.
    Index(usize),
    // Enum(usize),
    /// Represents a [`usize`] value, contained inside.
    Raw(usize),
}

/// Conversion error. Implements [`Error`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ConvError {
    from: ConvTarget,
    to: ConvTarget,
}

impl Debug for ConvTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Set(size) => write!(f, "Bitset{size}"),
            Self::Index(size) => write!(f, "Index<Bitset{size}>"),
            // Self::Enum(size) => write!(f, "Enum({size} variants)"),
            Self::Raw(n) => write!(f, "{n}usize"),
        }
    }
}

impl Display for ConvTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::Set(size) => write!(f, "Bitset (size {size})"),
            Self::Index(max) => write!(f, "Index (max = {max})"),
            // Self::Enum(size) => write!(f, "Enum ({size} variants)"),
            Self::Raw(n) => write!(f, "{n}usize"),
        }
    }
}

impl ConvError {
    /// Constructs new value of ConvError.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::error::{ConvError, ConvTarget};
    ///
    /// //Oh no! I couldn't convert from a raw usize to my index!
    /// let error = ConvError::new(ConvTarget::Raw(19), ConvTarget::Index(8));
    ///
    /// assert_eq!(error.to_string(), "failed to convert from 19usize to Index (max = 8)");
    /// #   Ok(())
    /// # }
    /// ```
    pub const fn new(from: ConvTarget, to: ConvTarget) -> Self {
        Self { from, to }
    }
}

impl Error for ConvError {}

impl Display for ConvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "failed to convert from {} to {}", self.from, self.to)
    }
}
