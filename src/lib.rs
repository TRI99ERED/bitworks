//! Crate meant to provide easy to use bitsets, with some out of the box functionality.

pub mod bitset;
pub mod bitset128;
pub mod bitset16;
pub mod bitset32;
pub mod bitset64;
pub mod bitset8;
pub mod byte_set;

pub mod bit;
pub mod error;
pub mod index;

/// Prelude.
pub mod prelude {
    use super::*;

    pub use bit::Bit::{self, One, Zero};

    pub use bitset::Bitset;

    pub use bitset128::Bitset128;
    pub use bitset16::Bitset16;
    pub use bitset32::Bitset32;
    pub use bitset64::Bitset64;
    pub use bitset8::Bitset8;
    pub use byte_set::Byteset;

    pub use index::Index;
}
