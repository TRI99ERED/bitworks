//! Crate meant to provide easy to use bitsets, with some out of the box functionality.
//!
//! Enable feature `"serde"` to enable `serde::Serialize` and `serde::Deserialize` for most applicable types.

pub mod bitset;
pub mod bitset128;
pub mod bitset16;
pub mod bitset32;
pub mod bitset64;
pub mod bitset8;
pub mod byteset;

pub mod bit;
pub mod error;
pub mod index;
pub mod safety_markers;

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
    pub use byteset::Byteset;

    pub use index::Index;

    /// Alias for [`Index<Bitset8>`][Index].
    pub type Index8 = Index<Bitset8>;
    /// Alias for [`Index<Bitset16>`][Index].
    pub type Index16 = Index<Bitset16>;
    /// Alias for [`Index<Bitset32>`][Index].
    pub type Index32 = Index<Bitset32>;
    /// Alias for [`Index<Bitset64>`][Index].
    pub type Index64 = Index<Bitset64>;
    /// Alias for [`Index<Bitset128>`][Index].
    pub type Index128 = Index<Bitset128>;
}
