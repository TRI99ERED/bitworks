//! Module containing error types.

use std::{
    error::Error,
    fmt::{Debug, Display},
};

pub type ConvResult<T> = Result<T, ConvError>;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ConvTarget {
    Field(usize),
    Index(usize),
    Enum(usize),
    Raw(usize),
}

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
            Self::Index(size) => write!(f, "BitfieldIndex<Bitfield{size}>"),
            Self::Enum(size) => write!(f, "Flagenum<Bitfield = Bitfield{size}>"),
            Self::Raw(n) => write!(f, "{n}usize"),
        }
    }
}

impl Display for ConvTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::Field(size) => write!(f, "Bitfield of size {size}"),
            Self::Index(size) => write!(f, "BitfieldIndex of size {size}"),
            Self::Enum(size) => write!(f, "Flagenum of size {size}"),
            Self::Raw(n) => write!(f, "{n}usize"),
        }
    }
}

impl ConvError {
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
