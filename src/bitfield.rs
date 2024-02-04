//! Module containing Bitfield.

use crate::{flagenum::Flagenum, index::BitfieldIndex};
use std::ops::{BitAnd, BitAndAssign, BitOr, BitXor, Not, Shl, Shr};

/// Trait defining common bitfield logic.
pub trait Bitfield:
    Sized
    + Clone
    + PartialEq
    + Eq
    + Not<Output = Self>
    + BitAnd<Output = Self>
    + BitAndAssign
    + BitOr<Output = Self>
    + BitXor<Output = Self>
    + Shl<BitfieldIndex<Self>, Output = Self>
    + Shr<BitfieldIndex<Self>, Output = Self>
    + From<BitfieldIndex<Self>>
{
    /// Number of bits (size) of the bitfield.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let size_in_bits = <Bitfield8 as Bitfield>::BIT_SIZE;
    ///
    /// assert_eq!(size_in_bits, 8);
    /// #   Ok(())
    /// # }
    /// ```
    const BIT_SIZE: usize;

    const ONE: Self;

    /// Value of the bitfield with every bit unset.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield: Bitfield8 = Bitfield::NONE;
    ///
    /// assert_eq!(bitfield.into_inner(), 0b00000000);
    /// #   Ok(())
    /// # }
    /// ```
    const NONE: Self;

    /// Value of the bitfield with every bit set.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield: Bitfield8 = Bitfield::ALL;
    ///
    /// assert_eq!(bitfield.into_inner(), 0b11111111);
    /// #   Ok(())
    /// # }
    /// ```
    const ALL: Self;

    /// Constructs empty Bitfield.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield: Bitfield8 = Bitfield::new();
    ///
    /// assert_eq!(bitfield.into_inner(), 0b00000000);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn new() -> Self {
        Self::NONE
    }

    #[inline(always)]
    fn from_index(index: BitfieldIndex<Self>) -> Self {
        Self::ONE << index
    }

    /// Builds Bitfield from slice over boolean values.<br/>
    /// Maintains the same index order: leftmost slice item becomes rightmost bit
    /// in number representation.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// // Same index order
    /// let slice: &[bool] = &[true, false, true, false, true, false, true, false];
    /// let bitfield: Bitfield8 = Bitfield::from_slice_bool(slice);
    ///
    /// assert_eq!(bitfield.into_inner(), 0b01010101);
    /// #   Ok(())
    /// # }
    /// ```
    fn from_slice_bool(slice: &[bool]) -> Self
    where
        Self: FromIterator<bool>,
    {
        slice.iter().take(Self::BIT_SIZE).copied().collect()
    }

    /// Builds Bitfield from slice over T values, where T implements Flagenum.
    /// Considers contained variants as set bits.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::{prelude::{Bitfield, Bitfield8, Flagenum, BitfieldIndex}, error::{ConvError, ConvTarget}};
    ///
    /// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    /// enum E {
    ///     A, // 0
    ///     B, // 1
    ///     D  =  3,
    ///     E, // 4
    /// }
    ///
    /// impl TryFrom<BitfieldIndex<Bitfield8>> for E {
    ///     type Error = ConvError;
    ///
    ///     fn try_from(index: BitfieldIndex<Bitfield8>) -> Result<Self, Self::Error> {
    ///         match index.into_inner() {
    ///             0 => Ok(E::A),
    ///             1 => Ok(E::B),
    ///             3 => Ok(E::D),
    ///             4 => Ok(E::E),
    ///             _ => Err(ConvError::new(ConvTarget::Index(8), ConvTarget::Enum(8))),
    ///         }
    ///     }
    /// }
    ///
    /// impl From<E> for BitfieldIndex<Bitfield8> {
    ///     fn from(value: E) -> Self {
    ///         Self::try_from(value as usize).expect("Enum E should always be a valid index")
    ///     }
    /// }
    ///
    /// impl Flagenum for E {
    ///     type Bitfield = Bitfield8;
    /// }
    ///
    /// let slice: &[E] = &[E::A, E::E, E::D];
    /// let bitfield: Bitfield8 = Bitfield::from_slice_flags(slice);
    ///
    /// assert_eq!(bitfield.into_inner(), 0b00011001);
    /// #   Ok(())
    /// # }
    /// ```
    fn from_slice_flags<T>(slice: &[T]) -> Self
    where
        T: Flagenum<Bitfield = Self>,
        BitfieldIndex<Self>: From<T>,
        Self: FromIterator<T>,
    {
        slice.iter().take(Self::BIT_SIZE).cloned().collect()
    }

    /// Count the number of all set bits.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::from(0b00000111);
    ///
    /// assert_eq!(Bitfield::count_ones(&bitfield), 3);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn count_ones(&self) -> usize {
        (0..Self::BIT_SIZE).fold(0, |acc, i| {
            acc + if self.get(i.try_into().unwrap()) {
                1
            } else {
                0
            }
        })
    }

    /// Count the number of all unset bits.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::from(0b00000111);
    ///
    /// assert_eq!(Bitfield::count_zeros(&bitfield), 5);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn count_zeros(&self) -> usize {
        (0..Self::BIT_SIZE).fold(0, |acc, i| {
            acc + (if self.get(i.try_into().unwrap()) {
                0
            } else {
                1
            })
        })
    }

    /// Sets bit at index to value. Returns copy of the resulting bitfield.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::from(0b01010100)
    ///     .set(1.try_into()?, true)
    ///     .set(2.try_into()?, false)
    ///     .set(3.try_into()?, true)
    ///     .set(4.try_into()?, false)
    ///     .set(5.try_into()?, true)
    ///     .set(6.try_into()?, false)
    ///     .set(7.try_into()?, true);
    ///
    /// assert_eq!(bitfield.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn set(&mut self, index: BitfieldIndex<Self>, value: bool) -> Self {
        if value {
            *self = self.clone() | Self::from(BitfieldIndex::<Self>::MIN) << index;
        } else {
            *self = self.clone() & !(Self::from(BitfieldIndex::<Self>::MIN) << index);
        }
        self.clone()
    }

    /// Returns bit at index.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::new().set(1.try_into()?, true);
    ///
    /// assert_eq!(Bitfield::get(&bitfield, 0.try_into()?), false);
    /// assert_eq!(Bitfield::get(&bitfield, 1.try_into()?), true);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn get(&self, index: BitfieldIndex<Self>) -> bool {
        let bit = Self::from(BitfieldIndex::<Self>::MIN) << index;
        (self.clone() & bit) != Self::NONE
    }

    /// Sets bit at index to 1. Returns copy of the resulting bitfield.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::NONE
    ///     .check_bit(1.try_into()?)
    ///     .check_bit(3.try_into()?)
    ///     .check_bit(5.try_into()?)
    ///     .check_bit(7.try_into()?);
    ///
    /// assert_eq!(bitfield.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn check_bit(&mut self, index: BitfieldIndex<Self>) -> Self {
        *self = self.clone() | Self::from(BitfieldIndex::<Self>::MIN) << index;
        self.clone()
    }

    /// Sets bit at index to 0. Returns copy of the resulting bitfield.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::ALL
    ///     .uncheck_bit(0.try_into()?)
    ///     .uncheck_bit(2.try_into()?)
    ///     .uncheck_bit(4.try_into()?)
    ///     .uncheck_bit(6.try_into()?);
    ///
    /// assert_eq!(bitfield.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn uncheck_bit(&mut self, index: BitfieldIndex<Self>) -> Self {
        *self = self.clone() & !(Self::from(BitfieldIndex::<Self>::MIN) << index);
        self.clone()
    }

    /// Returns iterator over bits of the bitfield in boolean representation.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::from(0b01010100);
    /// let mut iter = Bitfield::bits(&bitfield);
    ///
    /// assert_eq!(iter.next(), Some(false)); // 0
    /// assert_eq!(iter.next(), Some(false)); // 0
    /// assert_eq!(iter.next(), Some(true));  // 1
    /// assert_eq!(iter.next(), Some(false)); // 0
    /// assert_eq!(iter.next(), Some(true));  // 1
    /// assert_eq!(iter.next(), Some(false)); // 0
    /// assert_eq!(iter.next(), Some(true));  // 1
    /// assert_eq!(iter.next(), Some(false)); // 0
    /// assert_eq!(iter.next(), None);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn bits(&self) -> impl Iterator<Item = bool>
    where
        Self: IntoIterator<Item = bool>,
    {
        self.clone().into_iter()
    }

    /// Returns iterator over indeces of the set bits of the bitfield.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::from(0b01010100);
    /// let mut iter = Bitfield::set_indeces(&bitfield);
    ///
    /// assert_eq!(iter.next(), Some(2.try_into()?));
    /// assert_eq!(iter.next(), Some(4.try_into()?));
    /// assert_eq!(iter.next(), Some(6.try_into()?));
    /// assert_eq!(iter.next(), None);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn set_indeces(&self) -> impl Iterator<Item = BitfieldIndex<Self>>
    where
        Self: IntoIterator<Item = bool>,
    {
        self.bits().enumerate().filter_map(|(i, bit)| {
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
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::from(0b01010100);
    /// let mut iter = Bitfield::unset_indeces(&bitfield);
    ///
    /// assert_eq!(iter.next(), Some(0.try_into()?));
    /// assert_eq!(iter.next(), Some(1.try_into()?));
    /// assert_eq!(iter.next(), Some(3.try_into()?));
    /// assert_eq!(iter.next(), Some(5.try_into()?));
    /// assert_eq!(iter.next(), Some(7.try_into()?));
    /// assert_eq!(iter.next(), None);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn unset_indeces(&self) -> impl Iterator<Item = BitfieldIndex<Self>>
    where
        Self: IntoIterator<Item = bool>,
    {
        self.bits().enumerate().filter_map(|(i, bit)| {
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
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::{prelude::{Bitfield, Bitfield8, Flagenum, BitfieldIndex}, error::{ConvError, ConvTarget}};
    ///
    /// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    /// enum E {
    ///     A, // 0
    ///     B, // 1
    ///     D  =  3,
    ///     E, // 4
    /// }
    ///
    /// impl TryFrom<BitfieldIndex<Bitfield8>> for E {
    ///     type Error = ConvError;
    ///
    ///     fn try_from(index: BitfieldIndex<Bitfield8>) -> Result<Self, Self::Error> {
    ///         match index.into_inner() {
    ///             0 => Ok(E::A),
    ///             1 => Ok(E::B),
    ///             3 => Ok(E::D),
    ///             4 => Ok(E::E),
    ///             _ => Err(ConvError::new(ConvTarget::Index(8), ConvTarget::Enum(8))),
    ///         }
    ///     }
    /// }
    ///
    /// impl From<E> for BitfieldIndex<Bitfield8> {
    ///     fn from(value: E) -> Self {
    ///         Self::try_from(value as usize).expect("Enum E should always be a valid index")
    ///     }
    /// }
    ///
    /// impl Flagenum for E {
    ///     type Bitfield = Bitfield8;
    /// }
    ///
    ///                                // E D _ B A
    /// let bitfield = Bitfield8::from(0b_0_1_1_0_1); // implements Bitfield
    /// let mut iter = Bitfield::selected_variants::<E>(&bitfield);
    ///
    /// assert_eq!(iter.next(), Some(E::A));
    /// assert_eq!(iter.next(), Some(E::D));
    /// assert_eq!(iter.next(), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn selected_variants<T>(&self) -> impl Iterator<Item = T>
    where
        T: Flagenum<Bitfield = Self>,
        BitfieldIndex<Self>: From<T>,
        Self: IntoIterator<Item = bool>,
    {
        self.set_indeces().filter_map(|i| T::try_from(i).ok())
    }

    /// Returns iterator over unset bit indeces of the bitfield
    /// converted to target type T, where T implements Flagenum.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::{prelude::{Bitfield, Bitfield8, Flagenum, BitfieldIndex}, error::{ConvError, ConvTarget}};
    ///
    /// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    /// enum E {
    ///     A, // 0
    ///     B, // 1
    ///     D  =  3,
    ///     E, // 4
    /// }
    ///
    /// impl TryFrom<BitfieldIndex<Bitfield8>> for E {
    ///     type Error = ConvError;
    ///
    ///     fn try_from(index: BitfieldIndex<Bitfield8>) -> Result<Self, Self::Error> {
    ///         match index.into_inner() {
    ///             0 => Ok(E::A),
    ///             1 => Ok(E::B),
    ///             3 => Ok(E::D),
    ///             4 => Ok(E::E),
    ///             _ => Err(ConvError::new(ConvTarget::Index(8), ConvTarget::Enum(8))),
    ///         }
    ///     }
    /// }
    ///
    /// impl From<E> for BitfieldIndex<Bitfield8> {
    ///     fn from(value: E) -> Self {
    ///         Self::try_from(value as usize).expect("Enum E should always be a valid index")
    ///     }
    /// }
    ///
    /// impl Flagenum for E {
    ///     type Bitfield = Bitfield8;
    /// }
    ///
    ///                                // E D _ B A
    /// let bitfield = Bitfield8::from(0b_0_1_1_0_1); // implements Bitfield
    /// let mut iter = Bitfield::unselected_variants::<E>(&bitfield);
    ///
    /// assert_eq!(iter.next(), Some(E::B));
    /// assert_eq!(iter.next(), Some(E::E));
    /// assert_eq!(iter.next(), None);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn unselected_variants<T>(&self) -> impl Iterator<Item = T>
    where
        T: Flagenum<Bitfield = Self>,
        BitfieldIndex<Self>: From<T>,
        Self: IntoIterator<Item = bool>,
    {
        self.unset_indeces().filter_map(|i| T::try_from(i).ok())
    }

    /// Returns Set complement (`self′`) of bitfield.<br/>
    /// Alias for `!` operator
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let a = Bitfield8::from(0b11110000);
    /// let b = Bitfield::complement(a);
    ///
    /// assert_eq!(a.into_inner(), 0b11110000);
    /// assert_eq!(b.into_inner(), 0b00001111);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn complement(self) -> Self {
        !self
    }

    /// Returns Set union (`self ∪ other`) of two bitfields.<br/>
    /// Alias for `|` operator
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let a = Bitfield8::from(0b11001100);
    /// let b = Bitfield8::from(0b11110000);
    /// let c = Bitfield::union(a, b);
    ///
    /// assert_eq!(c.into_inner(), 0b11111100);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn union(self, other: Self) -> Self {
        self | other
    }

    /// Returns Set intersection (`self ∩ other`) of two bitfields.<br/>
    /// Alias for `&` operator
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let a = Bitfield8::from(0b11001100);
    /// let b = Bitfield8::from(0b11110000);
    /// let c = Bitfield::intersection(a, b);
    ///
    /// assert_eq!(c.into_inner(), 0b11000000);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn intersection(self, other: Self) -> Self {
        self & other
    }

    /// Returns Set difference (`self \ other`) of two bitfields.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let a = Bitfield8::from(0b11001100);
    /// let b = Bitfield8::from(0b11110000);
    /// let c = Bitfield::difference(a, b);
    ///
    /// assert_eq!(c.into_inner(), 0b00001100);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn difference(self, other: Self) -> Self {
        self & !other
    }

    /// Returns Set symmetric difference (`self Δ other`) of two bitfields.<br/>
    /// Alias for `^` operator
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let a = Bitfield8::from(0b11001100); // implements Bitfield
    /// let b = Bitfield8::from(0b11110000);
    /// let c = Bitfield::sym_difference(a, b);
    ///
    /// assert_eq!(c.into_inner(), 0b00111100);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn sym_difference(self, other: Self) -> Self {
        self ^ other
    }
}
