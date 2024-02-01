use std::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
    ShrAssign,
};

use crate::flagenum::Flagenum;

/// Trait defining common bitfield logic.
pub trait Bitfield:
    Sized
    + Copy
    + Clone
    + PartialEq
    + Eq
    + Not<Output = Self>
    + BitAnd<Output = Self>
    + BitAndAssign
    + BitOr<Output = Self>
    + BitOrAssign
    + BitXor<Output = Self>
    + BitXorAssign
    + Shl<usize, Output = Self>
    + ShlAssign<usize>
    + Shr<usize, Output = Self>
    + ShrAssign<usize>
    + IntoIterator<Item = bool>
    + FromIterator<bool>
{
    /// Identity of the representing type (e.g. 1u8 for u8, 1u16 for u16).
    const IDENT: Self;

    /// Fully unset value of the representing type (e.g. 0u8 for u8, 0u16 for u16).
    const EMPTY: Self;

    /// Fully set value of the representing type (e.g. 255u8 for u8, 65535u16 for u16).
    const ALL: Self;

    /// Number of bits in the bitfield.
    const BITS: usize;

    /// Count the number of all set bits.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::from(0b00000111); // implements Bitfield
    ///     assert_eq!(Bitfield::count_set(&bitfield), 3);
    ///     assert_ne!(Bitfield::count_set(&bitfield), 4);
    /// }
    /// ```
    fn count_set(&self) -> usize;

    /// Count the number of all unset bits.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::from(0b00000111); // implements Bitfield
    ///     assert_eq!(Bitfield::count_unset(&bitfield), 5);
    ///     assert_ne!(Bitfield::count_set(&bitfield), 4);
    /// }
    /// ```
    fn count_unset(&self) -> usize;

    /// Returns iterator over bits of the bitfield in boolean representation.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::from(0b01010100); // implements Bitfield
    ///     let mut bit_iter = Bitfield::bit_iter(&bitfield);
    ///     assert_eq!(bit_iter.next(), Some(false)); // 0
    ///     assert_eq!(bit_iter.next(), Some(false)); // 0
    ///     assert_eq!(bit_iter.next(), Some(true));  // 1
    ///     assert_eq!(bit_iter.next(), Some(false)); // 0
    ///     assert_eq!(bit_iter.next(), Some(true));  // 1
    ///     assert_eq!(bit_iter.next(), Some(false)); // 0
    ///     assert_eq!(bit_iter.next(), Some(true));  // 1
    ///     assert_eq!(bit_iter.next(), Some(false)); // 0
    ///     assert_eq!(bit_iter.next(), None);
    /// }
    /// ```
    fn bit_iter(&self) -> impl Iterator<Item = bool> {
        self.into_iter()
    }

    /// Returns iterator over set bit position of the bitfield
    /// converted to target type T, where T implements Flagenum.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Flagenum};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// enum E {
    ///     A, // 0
    ///     B, // 1
    ///     D  =  3,
    ///     E, // 4
    /// }
    ///
    /// impl TryFrom<Bitfield8> for E {
    ///     type Error = String;
    ///
    ///     fn try_from(value: Bitfield8) -> Result<Self, Self::Error> {
    ///         match value.value() {
    ///             0 => Ok(E::A),
    ///             1 => Ok(E::B),
    ///             3 => Ok(E::D),
    ///             4 => Ok(E::E),
    ///             _ => Err(format!("Invalid value for E")),
    ///         }
    ///     }
    /// }
    ///
    /// impl Flagenum for E {
    ///     type Bitfield = Bitfield8;
    /// }
    ///
    /// fn example() {                     // E D _ B A
    ///     let bitfield = Bitfield8::from(0b_0_1_1_0_1); // implements Bitfield
    ///     let mut set_enum_iter = Bitfield::set_enum_iter::<E>(&bitfield);
    ///     assert_eq!(set_enum_iter.next(), Some(E::A));
    ///     assert_eq!(set_enum_iter.next(), Some(E::D));
    ///     assert_eq!(set_enum_iter.next(), None);
    /// }
    /// ```
    fn set_enum_iter<T>(&self) -> impl Iterator<Item = T>
    where
        T: Flagenum<Bitfield = Self>;

    /// Returns iterator over unset bit position of the bitfield
    /// converted to target type T, where T implements Flagenum.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Flagenum};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// enum E {
    ///     A, // 0
    ///     B, // 1
    ///     D  =  3,
    ///     E, // 4
    /// }
    ///
    /// impl TryFrom<Bitfield8> for E {
    ///     type Error = String;
    ///
    ///     fn try_from(value: Bitfield8) -> Result<Self, Self::Error> {
    ///         match value.value() {
    ///             0 => Ok(E::A),
    ///             1 => Ok(E::B),
    ///             3 => Ok(E::D),
    ///             4 => Ok(E::E),
    ///             _ => Err(format!("Invalid value for E")),
    ///         }
    ///     }
    /// }
    ///
    /// impl Flagenum for E {
    ///     type Bitfield = Bitfield8;
    /// }
    ///
    /// fn example() {                     // E D _ B A
    ///     let bitfield = Bitfield8::from(0b_0_1_1_0_1); // implements Bitfield
    ///     let mut set_enum_iter = Bitfield::unset_enum_iter::<E>(&bitfield);
    ///     assert_eq!(set_enum_iter.next(), Some(E::B));
    ///     assert_eq!(set_enum_iter.next(), Some(E::E));
    ///     assert_eq!(set_enum_iter.next(), None);
    /// }
    /// ```
    fn unset_enum_iter<T>(&self) -> impl Iterator<Item = T>
    where
        T: Flagenum<Bitfield = Self>;

    /// Returns iterator over positions of the set bits of the bitfield.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::from(0b01010100); // implements Bitfield
    ///     let mut bit_iter = Bitfield::set_pos_iter(&bitfield);
    ///     assert_eq!(bit_iter.next(), Some(2));
    ///     assert_eq!(bit_iter.next(), Some(4));
    ///     assert_eq!(bit_iter.next(), Some(6));
    ///     assert_eq!(bit_iter.next(), None);
    /// }
    /// ```
    fn set_pos_iter(&self) -> impl Iterator<Item = usize> {
        self.bit_iter()
            .enumerate()
            .filter_map(|(i, bit)| if bit { Some(i) } else { None })
    }

    /// Returns iterator over positions of the unset bits of the bitfield.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::from(0b01010100); // implements Bitfield
    ///     let mut bit_iter = Bitfield::set_pos_iter(&bitfield);
    ///     assert_eq!(bit_iter.next(), Some(0));
    ///     assert_eq!(bit_iter.next(), Some(1));
    ///     assert_eq!(bit_iter.next(), Some(3));
    ///     assert_eq!(bit_iter.next(), Some(5));
    ///     assert_eq!(bit_iter.next(), Some(7));
    ///     assert_eq!(bit_iter.next(), None);
    /// }
    /// ```
    fn unset_pos_iter(&self) -> impl Iterator<Item = usize> {
        self.bit_iter()
            .enumerate()
            .filter_map(|(i, bit)| if !bit { Some(i) } else { None })
    }

    /// Constructs empty Bitfield.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::new();
    ///     assert_eq!(bitfield.value(), 0b00000000);
    /// }
    /// ```
    fn new() -> Self {
        Self::EMPTY
    }

    /// Sets bit at pos to value. Returns copy of the resulting bitfield.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::from(0b01010100) // implements Bitfield
    ///         .set_bit(1, true)
    ///         .set_bit(2, false)
    ///         .set_bit(3, true)
    ///         .set_bit(4, false)
    ///         .set_bit(5, true)
    ///         .set_bit(6, false)
    ///         .set_bit(7, true);
    ///     assert_eq!(bitfield.value(), 0b10101010);
    /// }
    /// ```
    fn set_bit(&mut self, pos: usize, value: bool) -> Self {
        if value {
            *self |= Self::IDENT << pos;
        } else {
            *self &= !(Self::IDENT << pos);
        }
        *self
    }

    /// Returns bit at pos.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::new().set_bit(1, true);
    ///     assert_eq!(Bitfield::get_bit(&bitfield, 0), false);
    ///     assert_eq!(Bitfield::get_bit(&bitfield, 1), true);
    /// }
    /// ```
    fn get_bit(&self, pos: usize) -> bool {
        let bit = Self::IDENT << pos;
        (*self & bit) != Self::EMPTY
    }

    /// Sets bit at pos to 1. Returns copy of the resulting bitfield.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::from(0) // implements Bitfield
    ///         .check_bit(1)
    ///         .check_bit(3)
    ///         .check_bit(5)
    ///         .check_bit(7);
    ///     assert_eq!(bitfield.value(), 0b10101010);
    /// }
    /// ```
    fn check_bit(&mut self, pos: usize) -> Self {
        *self |= Self::IDENT << pos;
        *self
    }

    /// Sets bit at pos to 0. Returns copy of the resulting bitfield.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::from(1) // implements Bitfield
    ///         .uncheck_bit(0)
    ///         .uncheck_bit(2)
    ///         .uncheck_bit(4)
    ///         .uncheck_bit(6);
    ///     assert_eq!(bitfield.value(), 0b10101010);
    /// }
    /// ```
    fn uncheck_bit(&mut self, pos: usize) -> Self {
        *self &= !(Self::IDENT << pos);
        *self
    }

    /// Returns Set complement (`self′`) of bitfield.<br/>
    /// Alias for `!` operator
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let a = Bitfield8::from(0b11110000); // implements Bitfield
    ///     let b = Bitfield::complement(a);
    ///     assert_eq!(a.value(), 0b11110000);
    ///     assert_eq!(a.value(), 0b00001111);
    /// }
    /// ```
    fn complement(self) -> Self {
        !self
    }

    /// Returns Set union (`self ∪ other`) of two bitfields.<br/>
    /// Alias for `|` operator
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let a = Bitfield8::from(0b11001100); // implements Bitfield
    ///     let b = Bitfield8::from(0b11110000);
    ///     let c = Bitfield::union(a, b);
    ///     assert_eq!(c.value(), 0b11111100);
    /// }
    /// ```
    fn union(self, other: Self) -> Self {
        self | other
    }

    /// Returns Set intersection (`self ∩ other`) of two bitfields.<br/>
    /// Alias for `&` operator
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let a = Bitfield8::from(0b11001100); // implements Bitfield
    ///     let b = Bitfield8::from(0b11110000);
    ///     let c = Bitfield::intersection(a, b);
    ///     assert_eq!(c.value(), 0b11000000);
    /// }
    /// ```
    fn intersection(self, other: Self) -> Self {
        self & other
    }

    /// Returns Set difference (`self \ other`) of two bitfields.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let a = Bitfield8::from(0b11001100); // implements Bitfield
    ///     let b = Bitfield8::from(0b11110000);
    ///     let c = Bitfield::difference(a, b);
    ///     assert_eq!(c.value(), 0b00001100);
    /// }
    /// ```
    fn difference(self, other: Self) -> Self {
        self & !other
    }

    /// Returns Set symmetric difference (`self Δ other`) of two bitfields.<br/>
    /// Alias for `^` operator
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let a = Bitfield8::from(0b11001100); // implements Bitfield
    ///     let b = Bitfield8::from(0b11110000);
    ///     let c = Bitfield::sym_difference(a, b);
    ///     assert_eq!(c.value(), 0b00111100);
    /// }
    /// ```
    fn sym_difference(self, other: Self) -> Self {
        self ^ other
    }

    /// Builds Bitfield from slice over boolean values.<br/>
    /// Maintains the same index order: leftmost slice item becomes rightmost bit
    /// in number representation.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///    // Same index order
    ///    let slice: &[bool] = &[true, false, true, false, true, false, true, false];
    ///    let bitfield: Bitfield8 = Bitfield8::from_slice(slice);
    ///
    ///    assert_eq!(bitfield, 0b01010101.into());
    /// }
    /// ```
    fn from_slice(slice: &[bool]) -> Self {
        slice.iter().take(Self::BITS).copied().collect()
    }
}
