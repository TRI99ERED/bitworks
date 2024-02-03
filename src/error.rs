//! Module containing error types.

use std::{error::Error, fmt::Display};

pub type BitfieldResult<T> = Result<T, BitfieldError>;

#[derive(Clone, Copy, Debug)]
pub enum ConvTarget {
    Bitfield8,
    Bitfield16,
    Bitfield32,
    Bitfield64,
    Bitfield128,
}

impl Display for ConvTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            ConvTarget::Bitfield8 => write!(f, "Bitfield8"),
            ConvTarget::Bitfield16 => write!(f, "Bitfield16"),
            ConvTarget::Bitfield32 => write!(f, "Bitfield32"),
            ConvTarget::Bitfield64 => write!(f, "Bitfield64"),
            ConvTarget::Bitfield128 => write!(f, "Bitfield128"),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum BitfieldError {
    IntoEnum,
    Conversion { from: ConvTarget, to: ConvTarget },
}

impl BitfieldError {
    pub fn conv_error(from: ConvTarget, to: ConvTarget) -> Self {
        Self::Conversion { from, to }
    }
}

impl Error for BitfieldError {}

impl Display for BitfieldError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            BitfieldError::IntoEnum => write!(f, "invalid value for enum"),
            BitfieldError::Conversion { from, to } => {
                write!(f, "couldn't convert from {from} to {to}")
            }
        }
    }
}
