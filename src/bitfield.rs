//! Module containing Bitfield.

use crate::{
    bit_ref::{BitMut, BitRef},
    error::{ConvError, ConvResult, ConvTarget},
    flags_enum::FlagsEnum,
    index::BitfieldIndex,
};
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

    /// Value of the bitfield with the least significant bit set.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield: Bitfield8 = Bitfield::ONE;
    ///
    /// assert_eq!(bitfield.into_inner(), 0b00000001);
    /// #   Ok(())
    /// # }
    /// ```
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

    /// Constructs Bitfield from BitfieldIndex.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, BitfieldIndex};
    ///
    /// let index: BitfieldIndex<Bitfield8> = 0.try_into()?;
    /// let bitfield: Bitfield8 = Bitfield::from_index(&index);
    ///
    /// assert_eq!(bitfield.into_inner(), 0b00000001);
    ///
    /// let index: BitfieldIndex<Bitfield8> = 3.try_into()?;
    /// let bitfield: Bitfield8 = Bitfield::from_index(&index);
    ///
    /// assert_eq!(bitfield.into_inner(), 0b00001000);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn from_index(index: &BitfieldIndex<Self>) -> Self {
        Self::ONE << *index
    }

    /// Constructs Bitfield from FlagsEnum.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::{prelude::{Bitfield, Bitfield8, FlagsEnum, BitfieldIndex}, error::{ConvError, ConvTarget}};
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
    /// impl FlagsEnum for E {
    ///     type Bitfield = Bitfield8;
    /// }
    ///
    /// let flag = E::A;
    /// let bitfield: Bitfield8 = Bitfield::from_flag(&flag);
    ///
    /// assert_eq!(bitfield.into_inner(), 0b00000001);
    ///
    /// let flag = E::D;
    /// let bitfield: Bitfield8 = Bitfield::from_flag(&flag);
    ///
    /// assert_eq!(bitfield.into_inner(), 0b00001000);
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn from_flag<T>(flag: &T) -> Self
    where
        T: FlagsEnum<Bitfield = Self> + Copy,
        BitfieldIndex<Self>: From<T>,
    {
        Self::ONE << BitfieldIndex::<Self>::from(*flag)
    }

    /// Expands Bitfield to a bigger one.
    ///
    /// # Errors
    /// Size of Res is smaller, than size of Self.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Bitfield16};
    ///
    /// let bitfield8: Bitfield8 = Bitfield8::from(0b00000001);
    /// let bitfield16: Bitfield16 = Bitfield::expand(&bitfield8)?;
    ///
    /// assert_eq!(bitfield16.into_inner(), 0b0000000000000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn expand<Res>(&self) -> ConvResult<Res>
    where
        Res: Bitfield,
    {
        if Self::BIT_SIZE <= Res::BIT_SIZE {
            let result = self
                .bits()
                .enumerate()
                .map(|(i, bit)| (BitfieldIndex::<Res>::try_from(i).unwrap(), bit))
                .fold(Res::new(), |mut acc, (i, bit)| acc.set_bit(i, bit));

            Ok(result)
        } else {
            Err(ConvError::new(
                ConvTarget::Field(Self::BIT_SIZE),
                ConvTarget::Field(Res::BIT_SIZE),
            ))
        }
    }

    /// Expands Bitfield to a bigger one. Uses unsafe optimizations.
    ///
    /// # Errors
    /// Size of Res is smaller, than size of Self.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Bitfield16};
    ///
    /// let bitfield8: Bitfield8 = Bitfield8::from(0b00000001);
    /// let bitfield16: Bitfield16 = Bitfield::fast_expand(&bitfield8)?;
    ///
    /// assert_eq!(bitfield16.into_inner(), 0b0000000000000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn fast_expand<Res>(&self) -> ConvResult<Res>
    where
        Self: Simple,
        Res: Bitfield + Simple,
    {
        if std::mem::size_of::<Self>() <= std::mem::size_of::<Res>() {
            let mut result = Res::new();

            let result_ptr = unsafe { std::mem::transmute(&mut result as *mut Res) };
            let self_ptr = self as *const Self;
            unsafe {
                std::ptr::copy_nonoverlapping(self_ptr, result_ptr, 1);
            }
            Ok(result)
        } else {
            Err(ConvError::new(
                ConvTarget::Field(Self::BIT_SIZE),
                ConvTarget::Field(Res::BIT_SIZE),
            ))
        }
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

    /// Builds Bitfield from slice over T values, where T implements FlagsEnum.
    /// Considers contained variants as set bits.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::{prelude::{Bitfield, Bitfield8, FlagsEnum, BitfieldIndex}, error::{ConvError, ConvTarget}};
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
    /// impl FlagsEnum for E {
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
        T: FlagsEnum<Bitfield = Self>,
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
            acc + if self.bit(i.try_into().unwrap()) {
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
            acc + (if self.bit(i.try_into().unwrap()) {
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
    ///     .set_bit(1.try_into()?, true)
    ///     .set_bit(2.try_into()?, false)
    ///     .set_bit(3.try_into()?, true)
    ///     .set_bit(4.try_into()?, false)
    ///     .set_bit(5.try_into()?, true)
    ///     .set_bit(6.try_into()?, false)
    ///     .set_bit(7.try_into()?, true);
    ///
    /// assert_eq!(bitfield.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn set_bit(&mut self, index: BitfieldIndex<Self>, value: bool) -> Self {
        if value {
            *self = self.clone() | Self::from(BitfieldIndex::<Self>::MIN) << index;
        } else {
            *self = self.clone() & !(Self::from(BitfieldIndex::<Self>::MIN) << index);
        }
        self.clone()
    }

    /// Returns a copy of a bit at index.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::new().set_bit(1.try_into()?, true);
    ///
    /// assert_eq!(Bitfield::bit(&bitfield, 0.try_into()?), false);
    /// assert_eq!(Bitfield::bit(&bitfield, 1.try_into()?), true);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn bit(&self, index: BitfieldIndex<Self>) -> bool {
        let bit = Self::from(BitfieldIndex::<Self>::MIN) << index;
        (self.clone() & bit) != Self::NONE
    }

    /// Returns a [`BitRef`] holding an immutable reference to the bit at index.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::new().set_bit(1.try_into()?, true);
    ///
    /// assert_eq!(*Bitfield::bit_ref(&bitfield, 0.try_into()?), false);
    /// assert_eq!(*Bitfield::bit_ref(&bitfield, 1.try_into()?), true);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn bit_ref(&self, index: BitfieldIndex<Self>) -> BitRef<'_, Self> {
        BitRef(self.bit(index), index, self)
    }

    /// Returns a [`BitMut`] holding a mutable reference to the bit at index.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let mut bitfield = Bitfield8::new();
    ///
    /// assert_eq!(Bitfield::bit(&bitfield, 0.try_into()?), false);
    /// assert_eq!(Bitfield::bit(&bitfield, 1.try_into()?), false);
    ///
    /// *Bitfield::bit_mut(&mut bitfield, 0.try_into()?) = true;
    ///
    /// assert_eq!(Bitfield::bit(&bitfield, 0.try_into()?), true);
    /// assert_eq!(Bitfield::bit(&bitfield, 1.try_into()?), false);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn bit_mut(&mut self, index: BitfieldIndex<Self>) -> BitMut<'_, Self> {
        BitMut(self.bit(index), index, self)
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

    /// Combines two Bitfields to create a bigger one.
    ///
    /// # Errors
    /// Size of Res is smaller, than the sum of size of Self and size of Other.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Bitfield16};
    ///
    /// let bitfield8_1: Bitfield8 = Bitfield8::from(0b00000001);
    /// let bitfield8_2: Bitfield8 = Bitfield8::from(0b00000011);
    /// let bitfield16: Bitfield16 = Bitfield::combine(&bitfield8_1, &bitfield8_2)?;
    ///
    /// assert_eq!(bitfield16.into_inner(), 0b0000001100000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn combine<Other, Res>(&self, other: &Other) -> ConvResult<Res>
    where
        Other: Bitfield,
        Res: Bitfield,
    {
        let combined = Self::BIT_SIZE + Other::BIT_SIZE;
        if Res::BIT_SIZE == combined {
            let result = self
                .bits()
                .enumerate()
                .map(|(i, bit)| (BitfieldIndex::<Res>::try_from(i).unwrap(), bit))
                .fold(Res::new(), |mut acc, (i, bit)| acc.set_bit(i, bit));

            let result = other
                .bits()
                .enumerate()
                .map(|(i, bit)| {
                    (
                        BitfieldIndex::<Res>::try_from(i + Self::BIT_SIZE).unwrap(),
                        bit,
                    )
                })
                .fold(result, |mut acc, (i, bit)| acc.set_bit(i, bit));
            Ok(result)
        } else {
            Err(ConvError::new(
                ConvTarget::Field(combined),
                ConvTarget::Field(Res::BIT_SIZE),
            ))
        }
    }

    /// Splits Bitfield into two smaller ones.
    ///
    /// # Errors
    /// Size of Self is smaller, than the sum of size of Res1 and size of Res2.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Bitfield16};
    ///
    /// let bitfield16: Bitfield16 = Bitfield16::from(0b0000001100000001);
    /// let (bitfield8_1, bitfield8_2): (Bitfield8, Bitfield8) = Bitfield::split(&bitfield16)?;
    ///
    /// assert_eq!(bitfield8_1.into_inner(), 0b00000001);
    /// assert_eq!(bitfield8_2.into_inner(), 0b00000011);
    /// #   Ok(())
    /// # }
    /// ```
    fn split<Res1, Res2>(&self) -> ConvResult<(Res1, Res2)>
    where
        Res1: Bitfield,
        Res2: Bitfield,
    {
        let combined = Res1::BIT_SIZE + Res2::BIT_SIZE;
        if Self::BIT_SIZE == combined {
            let result1 = self
                .bits()
                .take(Res1::BIT_SIZE)
                .enumerate()
                .map(|(i, bit)| (BitfieldIndex::<Res1>::try_from(i).unwrap(), bit))
                .fold(Res1::new(), |mut acc, (i, bit)| acc.set_bit(i, bit));

            let result2 = self
                .bits()
                .skip(Res1::BIT_SIZE)
                .enumerate()
                .map(|(i, bit)| (BitfieldIndex::<Res2>::try_from(i).unwrap(), bit))
                .fold(Res2::new(), |mut acc, (i, bit)| acc.set_bit(i, bit));

            Ok((result1, result2))
        } else {
            Err(ConvError::new(
                ConvTarget::Field(Self::BIT_SIZE),
                ConvTarget::Field(combined),
            ))
        }
    }

    /// Combines two Bitfields to create a bigger one. Uses unsafe optimizations.
    ///
    /// # Errors
    /// Size of Res is smaller, than the sum of size of Self and size of Other.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Bitfield16};
    ///
    /// let bitfield8_1: Bitfield8 = Bitfield8::from(0b00000001);
    /// let bitfield8_2: Bitfield8 = Bitfield8::from(0b00000011);
    /// let bitfield16: Bitfield16 = Bitfield::fast_combine(&bitfield8_1, &bitfield8_2)?;
    ///
    /// assert_eq!(bitfield16.into_inner(), 0b0000001100000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn fast_combine<Other, Res>(&self, other: &Other) -> ConvResult<Res>
    where
        Self: Simple,
        Other: Bitfield + Simple,
        Res: Bitfield + Simple,
    {
        let combined = std::mem::size_of::<Self>() + std::mem::size_of::<Other>();
        if std::mem::size_of::<Res>() == combined {
            let mut result = Res::new();

            let result_ptr = unsafe { std::mem::transmute(&mut result as *mut Res) };
            let self_ptr = self as *const Self;
            unsafe {
                std::ptr::copy_nonoverlapping(self_ptr, result_ptr, 1);
            }

            let result_ptr = unsafe { std::mem::transmute(result_ptr.add(1)) };
            let other_ptr = other as *const Other;
            unsafe {
                std::ptr::copy_nonoverlapping(other_ptr, result_ptr, 1);
            }
            Ok(result)
        } else {
            Err(ConvError::new(
                ConvTarget::Field(combined),
                ConvTarget::Field(Res::BIT_SIZE),
            ))
        }
    }

    /// Splits Bitfield into two smaller ones. Uses unsafe optimizations.
    ///
    /// # Errors
    /// Size of Self is smaller, than the sum of size of Res1 and size of Res2.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Bitfield16};
    ///
    /// let bitfield16: Bitfield16 = Bitfield16::from(0b0000001100000001);
    /// let (bitfield8_1, bitfield8_2): (Bitfield8, Bitfield8) = Bitfield::fast_split(&bitfield16)?;
    ///
    /// assert_eq!(bitfield8_1.into_inner(), 0b00000001);
    /// assert_eq!(bitfield8_2.into_inner(), 0b00000011);
    /// #   Ok(())
    /// # }
    /// ```
    fn fast_split<Res1, Res2>(&self) -> ConvResult<(Res1, Res2)>
    where
        Self: Simple,
        Res1: Bitfield + Simple,
        Res2: Bitfield + Simple,
    {
        let combined = std::mem::size_of::<Res1>() + std::mem::size_of::<Res2>();
        if std::mem::size_of::<Self>() == combined {
            let mut result1 = Res1::new();
            let mut result2 = Res2::new();

            let result1_ptr = &mut result1 as *mut Res1;
            let self_ptr = unsafe { std::mem::transmute(self as *const Self) };
            unsafe {
                std::ptr::copy_nonoverlapping(self_ptr, result1_ptr, 1);
            }

            let result2_ptr = &mut result2 as *mut Res2;
            let self_ptr = unsafe { std::mem::transmute(self_ptr.add(1)) };
            unsafe {
                std::ptr::copy_nonoverlapping(self_ptr, result2_ptr, 1);
            }
            Ok((result1, result2))
        } else {
            Err(ConvError::new(
                ConvTarget::Field(Self::BIT_SIZE),
                ConvTarget::Field(combined),
            ))
        }
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
    fn bits(&self) -> impl Iterator<Item = bool> {
        (0..Self::BIT_SIZE)
            .map(|i| BitfieldIndex::<Self>::try_from(i).unwrap())
            .map(|i| self.bit(i))
    }

    /// Returns iterator over [`BitRef`] holding immutable references
    /// to bits of the bitfield in boolean representation.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::from(0b01010100);
    /// let mut iter = Bitfield::bits_ref(&bitfield);
    ///
    /// assert_eq!(iter.next().as_deref(), Some(&false)); // 0
    /// assert_eq!(iter.next().as_deref(), Some(&false)); // 0
    /// assert_eq!(iter.next().as_deref(), Some(&true));  // 1
    /// assert_eq!(iter.next().as_deref(), Some(&false)); // 0
    /// assert_eq!(iter.next().as_deref(), Some(&true));  // 1
    /// assert_eq!(iter.next().as_deref(), Some(&false)); // 0
    /// assert_eq!(iter.next().as_deref(), Some(&true));  // 1
    /// assert_eq!(iter.next().as_deref(), Some(&false)); // 0
    /// assert_eq!(iter.next(), None);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn bits_ref(&self) -> impl Iterator<Item = BitRef<'_, Self>> {
        (0..Self::BIT_SIZE)
            .map(|i| BitfieldIndex::<Self>::try_from(i).unwrap())
            .map(|i| self.bit_ref(i))
    }

    /// Returns iterator over [`BitMut`] holding mutable references
    /// to bits of the bitfield in boolean representation.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let mut bitfield = Bitfield8::from(0b01010100);
    /// let mut iter = Bitfield::bits_mut(&mut bitfield);
    ///
    /// for mut bit in iter {
    ///     *bit = !*bit;
    /// }
    ///
    /// assert_eq!(bitfield.into_inner(), 0b10101011);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn bits_mut(&mut self) -> impl Iterator<Item = BitMut<'_, Self>> {
        let p = self as *mut Self;
        (0..Self::BIT_SIZE)
            .map(|i| BitfieldIndex::<Self>::try_from(i).unwrap())
            .map(move |i| unsafe { p.as_mut().unwrap().bit_mut(i) })
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
    /// let mut iter = Bitfield::ones(&bitfield);
    ///
    /// assert_eq!(iter.next(), Some(2.try_into()?));
    /// assert_eq!(iter.next(), Some(4.try_into()?));
    /// assert_eq!(iter.next(), Some(6.try_into()?));
    /// assert_eq!(iter.next(), None);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn ones(&self) -> impl Iterator<Item = BitfieldIndex<Self>> {
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
    /// let mut iter = Bitfield::zeros(&bitfield);
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
    fn zeros(&self) -> impl Iterator<Item = BitfieldIndex<Self>> {
        self.bits().enumerate().filter_map(|(i, bit)| {
            if !bit {
                Some(i.try_into().unwrap())
            } else {
                None
            }
        })
    }

    /// Returns iterator over set bit indeces of the bitfield
    /// converted to target type T, where T implements FlagsEnum.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::{prelude::{Bitfield, Bitfield8, FlagsEnum, BitfieldIndex}, error::{ConvError, ConvTarget}};
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
    /// impl FlagsEnum for E {
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
        T: FlagsEnum<Bitfield = Self>,
        BitfieldIndex<Self>: From<T>,
    {
        self.ones().filter_map(|i| T::try_from(i).ok())
    }

    /// Returns iterator over unset bit indeces of the bitfield
    /// converted to target type T, where T implements FlagsEnum.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::{prelude::{Bitfield, Bitfield8, FlagsEnum, BitfieldIndex}, error::{ConvError, ConvTarget}};
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
    /// impl FlagsEnum for E {
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
        T: FlagsEnum<Bitfield = Self>,
        BitfieldIndex<Self>: From<T>,
    {
        self.zeros().filter_map(|i| T::try_from(i).ok())
    }
}

/// Marker trait for simple [`Bitfield`]s.
///
/// Implementors of this trait get access to these methods defined on `Bitfield`:
/// * [`Bitfield::fast_expand()`]
/// * [`Bitfield::fast_combine()`]
/// * [`Bitfield::fast_split()`]
///
/// All the methods above have corresponding versions without `fast_` prefix, which contains no unsafe code
/// and aren't restricted to only `Simple` types.
///
/// # Safety
/// If you implement this trait, you are responsible for making sure, that memory representation of the implementor
/// only contains the bitfield itself and no additional data (e.g. other fields in a struct).
///
/// In general, any one-field tuple structs or one-field C-like structs are good implementors of this trait,
/// but only if the data in that field has consistent memory layout:<br/>
/// E.g. any [`Sized`] owned primitive types or arrays of them, but not tuples, references, pointers etc.<br/>
/// It is `unsafe` to implement this trait for second kind of structs and will lead to memory violations or
/// unintended and undefined behaviour.
///
/// If you're unsure about what this means, use built-in `Bitfield`s (they all implement `Simple`)
/// or do not implement this trait for your custom `Bitfield` (the trade-off should be minimal).
pub unsafe trait Simple: Bitfield {}
