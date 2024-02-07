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
    Field(usize),
    Index(usize),
    Enum(usize),
    Raw(usize),
}

/// Conversion error.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ConvError {
    from: ConvTarget,
    to: ConvTarget,
}

impl Debug for ConvTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Field(size) => write!(f, "Bitfield{size}"),
            Self::Index(size) => write!(f, "Index<Bitfield{size}>"),
            Self::Enum(size) => write!(f, "FlagsEnum<Bitfield = Bitfield{size}>"),
            Self::Raw(n) => write!(f, "{n}usize"),
        }
    }
}

impl Display for ConvTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::Field(size) => write!(f, "Bitfield (size {size})"),
            Self::Index(max) => write!(f, "Index (max = {max})"),
            Self::Enum(size) => write!(f, "FlagsEnum (Bitfield (size {size}))"),
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
    /// use simple_bitfield::error::{ConvError, ConvTarget};
    ///
    /// //Oh no! I couldn't convert from a bitfield to my enum!
    /// let error = ConvError::new(ConvTarget::Field(8), ConvTarget::Enum(8));
    ///
    /// assert_eq!(error.to_string(), "failed to convert from Bitfield (size 8) to FlagsEnum (Bitfield (size 8))");
    /// #   Ok(())
    /// # }
    /// ```
    pub fn new(from: ConvTarget, to: ConvTarget) -> Self {
        Self { from, to }
    }
}

impl Error for ConvError {}

impl Display for ConvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "failed to convert from {} to {}", self.from, self.to)
    }
}
