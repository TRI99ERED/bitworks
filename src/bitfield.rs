use std::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
    ShrAssign,
};

use crate::{flagenum::Flagenum, index::BitfieldIndex};

/// Trait defining common bitfield logic.
pub trait Bitfield:
    Sized
    + Copy
    + Clone
    + PartialEq
    + Eq
    + PartialOrd
    + Ord
    + Not<Output = Self>
    + BitAnd<Output = Self>
    + BitAndAssign
    + BitOr<Output = Self>
    + BitOrAssign
    + BitXor<Output = Self>
    + BitXorAssign
    + Shl<BitfieldIndex<Self>, Output = Self>
    + ShlAssign<BitfieldIndex<Self>>
    + Shr<BitfieldIndex<Self>, Output = Self>
    + ShrAssign<BitfieldIndex<Self>>
    + IntoIterator<Item = bool>
    + FromIterator<bool>
    + From<BitfieldIndex<Self>>
{
    /// Identity of the representing type (e.g. 1u8 for u8, 1u16 for u16).
    const ONE: Self;

    /// Fully unset value of the representing type (e.g. 0u8 for u8, 0u16 for u16).
    const EMPTY: Self;

    /// Fully set value of the representing type (e.g. 255u8 for u8, 65535u16 for u16).
    const ALL: Self;

    /// Number of bits in the bitfield.
    const BITS: usize;

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
    #[inline(always)]
    fn new() -> Self {
        Self::EMPTY
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
    #[inline(always)]
    fn from_slice(slice: &[bool]) -> Self {
        slice.iter().take(Self::BITS).copied().collect()
    }

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
    #[inline(always)]
    fn count_set(&self) -> usize {
        (0..Self::BITS).fold(0, |acc, i| {
            acc + if self.get_bit(i.try_into().unwrap()) {
                1
            } else {
                0
            }
        })
    }

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
    #[inline(always)]
    fn count_unset(&self) -> usize {
        (0..Self::BITS).fold(0, |acc, i| {
            acc + (if self.get_bit(i.try_into().unwrap()) {
                0
            } else {
                1
            })
        })
    }

    /// Sets bit at index to value. Returns copy of the resulting bitfield.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::from(0b01010100) // implements Bitfield
    ///         .set_bit(1.try_into().unwrap(), true)
    ///         .set_bit(2.try_into().unwrap(), false)
    ///         .set_bit(3.try_into().unwrap(), true)
    ///         .set_bit(4.try_into().unwrap(), false)
    ///         .set_bit(5.try_into().unwrap(), true)
    ///         .set_bit(6.try_into().unwrap(), false)
    ///         .set_bit(7.try_into().unwrap(), true);
    ///     assert_eq!(bitfield.value(), 0b10101010);
    /// }
    /// ```
    fn set_bit(&mut self, i: BitfieldIndex<Self>, value: bool) -> Self {
        if value {
            *self |= Self::ONE << i;
        } else {
            *self &= !(Self::ONE << i);
        }
        *self
    }

    /// Returns bit at index.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::new().set_bit(1.try_into().unwrap(), true);
    ///     assert_eq!(Bitfield::get_bit(&bitfield, 0.try_into().unwrap()), false);
    ///     assert_eq!(Bitfield::get_bit(&bitfield, 1.try_into().unwrap()), true);
    /// }
    /// ```
    #[inline(always)]
    fn get_bit(&self, i: BitfieldIndex<Self>) -> bool {
        let bit = Self::ONE << i;
        (*self & bit) != Self::EMPTY
    }

    /// Sets bit at index to 1. Returns copy of the resulting bitfield.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::from(0) // implements Bitfield
    ///         .check_bit(1.try_into().unwrap())
    ///         .check_bit(3.try_into().unwrap())
    ///         .check_bit(5.try_into().unwrap())
    ///         .check_bit(7.try_into().unwrap());
    ///     assert_eq!(bitfield.value(), 0b10101010);
    /// }
    /// ```
    #[inline(always)]
    fn check_bit(&mut self, i: BitfieldIndex<Self>) -> Self {
        *self |= Self::ONE << i;
        *self
    }

    /// Sets bit at index to 0. Returns copy of the resulting bitfield.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::from(1) // implements Bitfield
    ///         .uncheck_bit(0.try_into().unwrap())
    ///         .uncheck_bit(2.try_into().unwrap())
    ///         .uncheck_bit(4.try_into().unwrap())
    ///         .uncheck_bit(6.try_into().unwrap());
    ///     assert_eq!(bitfield.value(), 0b10101010);
    /// }
    /// ```
    #[inline(always)]
    fn uncheck_bit(&mut self, i: BitfieldIndex<Self>) -> Self {
        *self &= !(Self::ONE << i);
        *self
    }

    /// Returns iterator over bits of the bitfield in boolean representation.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::from(0b01010100); // implements Bitfield
    ///     let mut iter = Bitfield::bit_iter(&bitfield);
    ///     assert_eq!(iter.next(), Some(false)); // 0
    ///     assert_eq!(iter.next(), Some(false)); // 0
    ///     assert_eq!(iter.next(), Some(true));  // 1
    ///     assert_eq!(iter.next(), Some(false)); // 0
    ///     assert_eq!(iter.next(), Some(true));  // 1
    ///     assert_eq!(iter.next(), Some(false)); // 0
    ///     assert_eq!(iter.next(), Some(true));  // 1
    ///     assert_eq!(iter.next(), Some(false)); // 0
    ///     assert_eq!(iter.next(), None);
    /// }
    /// ```
    #[inline(always)]
    fn bit_iter(&self) -> impl Iterator<Item = bool> {
        self.into_iter()
    }

    /// Returns iterator over indeces of the set bits of the bitfield.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::from(0b01010100); // implements Bitfield
    ///     let mut iter = Bitfield::set_index_iter(&bitfield);
    ///     assert_eq!(iter.next(), Some(2.try_into().unwrap()));
    ///     assert_eq!(iter.next(), Some(4.try_into().unwrap()));
    ///     assert_eq!(iter.next(), Some(6.try_into().unwrap()));
    ///     assert_eq!(iter.next(), None);
    /// }
    /// ```
    #[inline(always)]
    fn set_index_iter(&self) -> impl Iterator<Item = BitfieldIndex<Self>> {
        self.bit_iter().enumerate().filter_map(|(i, bit)| {
            if bit {
                Some(i.try_into().unwrap())
            } else {
                None
            }
        })
    }

    /// Returns iterator over indeces of the unset bits of the bitfield.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// fn example() {
    ///     let bitfield = Bitfield8::from(0b01010100); // implements Bitfield
    ///     let mut iter = Bitfield::unset_index_iter(&bitfield);
    ///     assert_eq!(iter.next(), Some(0.try_into().unwrap()));
    ///     assert_eq!(iter.next(), Some(1.try_into().unwrap()));
    ///     assert_eq!(iter.next(), Some(3.try_into().unwrap()));
    ///     assert_eq!(iter.next(), Some(5.try_into().unwrap()));
    ///     assert_eq!(iter.next(), Some(7.try_into().unwrap()));
    ///     assert_eq!(iter.next(), None);
    /// }
    /// ```
    #[inline(always)]
    fn unset_index_iter(&self) -> impl Iterator<Item = BitfieldIndex<Self>> {
        self.bit_iter().enumerate().filter_map(|(i, bit)| {
            if !bit {
                Some(i.try_into().unwrap())
            } else {
                None
            }
        })
    }

    /// Returns iterator over set bit indeces of the bitfield
    /// converted to target type T, where T implements Flagenum.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Flagenum, BitfieldIndex};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// enum E {
    ///     A, // 0
    ///     B, // 1
    ///     D  =  3,
    ///     E, // 4
    /// }
    ///
    /// impl TryFrom<BitfieldIndex<Bitfield8>> for E {
    ///     type Error = String;
    ///
    ///     fn try_from(i: BitfieldIndex<Bitfield8>) -> Result<Self, Self::Error> {
    ///         match i.value() {
    ///             0 => Ok(E::A),
    ///             1 => Ok(E::B),
    ///             3 => Ok(E::D),
    ///             4 => Ok(E::E),
    ///             _ => Err(String::new()),
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
    ///     let mut iter = Bitfield::selected_variant_iter::<E>(&bitfield);
    ///     assert_eq!(iter.next(), Some(E::A));
    ///     assert_eq!(iter.next(), Some(E::D));
    ///     assert_eq!(iter.next(), None);
    /// }
    /// ```
    #[inline(always)]
    fn selected_variant_iter<T>(&self) -> impl Iterator<Item = T>
    where
        T: Flagenum<Bitfield = Self>,
    {
        self.set_index_iter()
            .filter_map(|i| T::try_from_index(i).ok())
    }

    /// Returns iterator over unset bit indeces of the bitfield
    /// converted to target type T, where T implements Flagenum.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Flagenum, BitfieldIndex};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// enum E {
    ///     A, // 0
    ///     B, // 1
    ///     D  =  3,
    ///     E, // 4
    /// }
    ///
    /// impl TryFrom<BitfieldIndex<Bitfield8>> for E {
    ///     type Error = String;
    ///
    ///     fn try_from(i: BitfieldIndex<Bitfield8>) -> Result<Self, Self::Error> {
    ///         match i.value() {
    ///             0 => Ok(E::A),
    ///             1 => Ok(E::B),
    ///             3 => Ok(E::D),
    ///             4 => Ok(E::E),
    ///             _ => Err(String::new()),
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
    ///     let mut iter = Bitfield::unselected_variant_iter::<E>(&bitfield);
    ///     assert_eq!(iter.next(), Some(E::B));
    ///     assert_eq!(iter.next(), Some(E::E));
    ///     assert_eq!(iter.next(), None);
    /// }
    /// ```
    #[inline(always)]
    fn unselected_variant_iter<T>(&self) -> impl Iterator<Item = T>
    where
        T: Flagenum<Bitfield = Self>,
    {
        self.unset_index_iter()
            .filter_map(|i| T::try_from_index(i).ok())
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
    #[inline(always)]
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
    #[inline(always)]
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
    #[inline(always)]
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
    #[inline(always)]
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
    #[inline(always)]
    fn sym_difference(self, other: Self) -> Self {
        self ^ other
    }
}
