//! Crate meant to provide easy to use bitfields, with some out of the box functionality.

pub mod bitfield;
pub mod bitfield128;
pub mod bitfield16;
pub mod bitfield32;
pub mod bitfield64;
pub mod bitfield8;
pub mod byte_field;

pub mod bit;
pub mod error;
pub mod index;

/// Prelude.
pub mod prelude {
    use super::*;

    pub use bit::Bit::{self, One, Zero};
    pub use bitfield::Bitfield;
    pub use bitfield128::Bitfield128;
    pub use bitfield16::Bitfield16;
    pub use bitfield32::Bitfield32;
    pub use bitfield64::Bitfield64;
    pub use bitfield8::Bitfield8;
    pub use byte_field::ByteField;

    pub use index::Index;
}

mod private {
    #[deprecated]
    pub trait Sealed {}
}
