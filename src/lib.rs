//! Crate meant to provide easy to use bitfields, with some out of the box functionality.

pub mod bitfield;
pub mod bitfield128;
pub mod bitfield16;
pub mod bitfield32;
pub mod bitfield64;
pub mod bitfield8;

pub mod error;
pub mod flagenum;
pub mod index;
pub mod iter;

/// Prelude.
pub mod prelude {
    use super::*;

    pub use bitfield::Bitfield;
    pub use bitfield128::Bitfield128;
    pub use bitfield16::Bitfield16;
    pub use bitfield32::Bitfield32;
    pub use bitfield64::Bitfield64;
    pub use bitfield8::Bitfield8;

    pub use flagenum::Flagenum;
    pub use index::BitfieldIndex;

    pub use iter::BitIter;
}
