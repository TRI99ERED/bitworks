//! Module containing [`Bitset`].

use crate::{
    bit::{Bit, BitMut, BitRef},
    error::{ConvError, ConvResult, ConvTarget},
    index::Index,
};

pub(crate) const fn bit_len<T>() -> usize
where
    T: Bitset,
{
    T::BYTE_SIZE * 8
}

pub(crate) const fn byte_index<T>(index: Index<T>) -> usize
where
    T: Bitset,
{
    index.into_inner() / 8
}

pub(crate) const fn bit_index<T>(index: Index<T>) -> usize
where
    T: Bitset,
{
    index.into_inner() % 8
}

pub(crate) const fn bitmask<T>(index: Index<T>) -> u8
where
    T: Bitset,
{
    1 << bit_index(index)
}

/// Trait defining common bitset logic.
///
/// This trait is not meant to be implmented on enums, as beyond some extremely rare cases,
/// they won't produce a valid bitset.
///
/// It's recommended to prefer implementing this trait for one-set structs, where that sole set is
/// representing the bitset, as that would allow you to implement [`LeftAligned`] marker on it safely.
/// If you want to get the benefits of `LeftAligned` on any struct, make it a wrapper around
/// one of the `LeftAligned` types and use it's methods. All built-in `Bitset` types are `LeftAligned`.
pub trait Bitset: Sized + Clone + PartialEq + Eq
where
    Self::Repr: Sized + Clone + PartialEq + Eq,
{
    type Repr;

    /// Number of bytes (`size` in bytes) of the `Bitset`.
    ///
    /// If the implementor contains additional data, its bytes
    /// should *NOT* be included when initializing this constant.
    ///
    /// Refer to [core::mem::size_of] if you need actual size of the type in your contexts.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let size_in_bytes = Bitset8::BYTE_SIZE;
    ///
    /// assert_eq!(size_in_bytes, 1);
    /// #   Ok(())
    /// # }
    /// ```
    const BYTE_SIZE: usize;

    /// Value of the `Bitset` with the least significant bit set.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::ONE;
    ///
    /// assert_eq!(bitset.into_inner(), 0b00000001);
    /// #   Ok(())
    /// # }
    /// ```
    const ONE: Self;

    /// Value of the `Bitset` with every bit not set.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::NONE;
    ///
    /// assert_eq!(bitset.into_inner(), 0b00000000);
    /// #   Ok(())
    /// # }
    /// ```
    const NONE: Self;

    /// Value of the `Bitset` with every bit set.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::ALL;
    ///
    /// assert_eq!(bitset.into_inner(), 0b11111111);
    /// #   Ok(())
    /// # }
    /// ```
    const ALL: Self;

    fn new(value: Self::Repr) -> Self;

    /// Build `Bitset` from a mutable reference.<br/>
    /// Useful for chaining bit modifications.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::*;
    ///
    /// let bitset = Bitset8::NONE
    ///     .set_bit(0.try_into()?, One)
    ///     .check_bit(6.try_into()?)
    ///     .uncheck_bit(0.try_into()?)
    ///     .build();
    ///
    /// assert_eq!(bitset.into_inner(), 0b01000000);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn build(&mut self) -> Self {
        self.clone()
    }

    /// Constructs `Bitset` from [`Index`].
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8, Index};
    ///
    /// let index = 0.try_into()?;
    /// let bitset = Bitset8::from_index(&index);
    ///
    /// assert_eq!(bitset.into_inner(), 0b00000001);
    ///
    /// let index = 3.try_into()?;
    /// let bitset = Bitset8::from_index(&index);
    ///
    /// assert_eq!(bitset.into_inner(), 0b00001000);
    /// #   Ok(())
    /// # }
    /// ```
    fn from_index(index: &Index<Self>) -> Self;

    /// Expands `Bitset` to a bigger one.<br/>
    /// If available, you should prefer using [`Bitset::expand_optimized`].
    ///
    /// # Errors
    /// Size of `Res` is smaller, than size of `Self`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8, Bitset16};
    ///
    /// let bitset8 = Bitset8::from(0b00000001);
    /// let bitset16: Bitset16 = bitset8.expand()?;
    ///
    /// assert_eq!(bitset16.into_inner(), 0b0000000000000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn expand<Res>(self) -> ConvResult<Res>
    where
        Res: Bitset,
    {
        if Self::BYTE_SIZE <= Res::BYTE_SIZE {
            let result = self
                .bits_ref()
                .enumerate()
                .map(|(i, bit)| (Index::<Res>::try_from(i).unwrap(), bit))
                .fold(&mut Res::NONE.clone(), |acc, (i, bit)| acc.set_bit(i, *bit))
                .build();

            Ok(result)
        } else {
            Err(ConvError::new(
                ConvTarget::Set(bit_len::<Self>()),
                ConvTarget::Set(bit_len::<Res>()),
            ))
        }
    }

    /// Expands `Bitset` to a bigger one. Uses `unsafe` optimizations.
    ///
    /// # Errors
    /// Size of `Res` is smaller, than size of `Self`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8, Bitset16};
    ///
    /// let bitset8 = Bitset8::from(0b00000001);
    /// let bitset16: Bitset16 = bitset8.expand_optimized()?;
    ///
    /// assert_eq!(bitset16.into_inner(), 0b0000000000000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn expand_optimized<Res>(self) -> ConvResult<Res>
    where
        Self: LeftAligned,
        Res: Bitset + LeftAligned,
    {
        if Self::BYTE_SIZE <= Res::BYTE_SIZE {
            let mut result = Res::NONE.clone();

            unsafe {
                std::ptr::copy_nonoverlapping(
                    &self as *const _ as *const u8,
                    &mut result as *mut _ as *mut u8,
                    Self::BYTE_SIZE,
                );
            }
            Ok(result)
        } else {
            Err(ConvError::new(
                ConvTarget::Set(bit_len::<Self>()),
                ConvTarget::Set(bit_len::<Res>()),
            ))
        }
    }

    /// Builds `Bitset` from collection of [`Bit`] values.<br/>
    /// Maintains the same index order: leftmost `slice` item becomes the least significant bit.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::*;
    ///
    /// // Same index order
    /// let slice: &[Bit] = &[One, Zero, One, Zero, One, Zero, One, Zero];
    /// let bitset = Bitset8::from_bits_col(slice);
    ///
    /// assert_eq!(bitset.into_inner(), 0b01010101);
    /// #   Ok(())
    /// # }
    /// ```
    fn from_bits_col<'a, I>(iter: I) -> Self
    where
        Self: 'a,
        I: IntoIterator<Item = &'a Bit>,
    {
        iter.into_iter()
            .take(bit_len::<Self>())
            .enumerate()
            .map(|(i, b)| (Index::<Self>::try_from(i).unwrap(), *b))
            .fold(&mut Self::NONE.clone(), |acc, (i, b)| acc.set_bit(i, b))
            .build()
    }

    /// Count the number of all set bits.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::from(0b00000111);
    ///
    /// assert_eq!(bitset.count_ones(), 3);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn count_ones(&self) -> usize {
        (0..bit_len::<Self>()).fold(0, |acc, i| {
            acc + if bool::from(*self.bit_ref(i.try_into().unwrap())) {
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
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::from(0b00000111);
    ///
    /// assert_eq!(bitset.count_zeros(), 5);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn count_zeros(&self) -> usize {
        (0..bit_len::<Self>()).fold(0, |acc, i| {
            acc + (if bool::from(*self.bit_ref(i.try_into().unwrap())) {
                0
            } else {
                1
            })
        })
    }

    /// Sets bit at [`index`][Index] to value. Returns a mutable reference to the `Bitset`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::*;
    ///
    /// let bitset = Bitset8::from(0b01010100)
    ///     .set_bit(1.try_into()?, One)
    ///     .set_bit(2.try_into()?, Zero)
    ///     .set_bit(3.try_into()?, One)
    ///     .set_bit(4.try_into()?, Zero)
    ///     .set_bit(5.try_into()?, One)
    ///     .set_bit(6.try_into()?, Zero)
    ///     .set_bit(7.try_into()?, One)
    ///     .build();
    ///
    /// assert_eq!(bitset.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn set_bit(&mut self, index: Index<Self>, value: Bit) -> &mut Self {
        if bool::from(value) {
            self.check_bit(index);
        } else {
            self.uncheck_bit(index);
        }
        self
    }

    /// Sets bit at [`index`][Index] to 1. Returns a mutable reference to the `Bitset`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::NONE
    ///     .clone()
    ///     .check_bit(1.try_into()?)
    ///     .check_bit(3.try_into()?)
    ///     .check_bit(5.try_into()?)
    ///     .check_bit(7.try_into()?)
    ///     .build();
    ///
    /// assert_eq!(bitset.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    fn check_bit(&mut self, index: Index<Self>) -> &mut Self;

    /// Sets bit at [`index`][Index] to 0. Returns a mutable reference to the `Bitset`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::ALL
    ///     .clone()
    ///     .uncheck_bit(0.try_into()?)
    ///     .uncheck_bit(2.try_into()?)
    ///     .uncheck_bit(4.try_into()?)
    ///     .uncheck_bit(6.try_into()?)
    ///     .build();
    ///
    /// assert_eq!(bitset.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    fn uncheck_bit(&mut self, index: Index<Self>) -> &mut Self;

    /// Returns a copy of a bit at [`index`][Index].
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::*;
    ///
    /// let bitset = Bitset8::NONE.set_bit(1.try_into()?, One).build();
    ///
    /// assert_eq!(bitset.bit(0.try_into()?), Zero);
    /// assert_eq!(bitset.bit(1.try_into()?), One);
    /// #   Ok(())
    /// # }
    /// ```
    fn bit(&self, index: Index<Self>) -> Bit;

    /// Returns a [`BitRef`] holding an immutable reference to the bit at [`index`][Index].
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::*;
    ///
    /// let bitset = Bitset8::NONE.set_bit(1.try_into()?, One).build();
    ///
    /// assert_eq!(*bitset.bit_ref(0.try_into()?), Zero);
    /// assert_eq!(*bitset.bit_ref(1.try_into()?), One);
    /// #   Ok(())
    /// # }
    /// ```
    fn bit_ref(&self, index: Index<Self>) -> BitRef<'_, Self>;

    /// Returns a [`BitMut`] holding a mutable reference to the bit at [`index`][Index].
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::*;
    ///
    /// let mut bitset = Bitset8::NONE;
    ///
    /// assert_eq!(bitset.bit(0.try_into()?), Zero);
    /// assert_eq!(bitset.bit(1.try_into()?), Zero);
    ///
    /// *bitset.bit_mut(0.try_into()?) = One;
    ///
    /// assert_eq!(bitset.bit(0.try_into()?), One);
    /// assert_eq!(bitset.bit(1.try_into()?), Zero);
    /// #   Ok(())
    /// # }
    /// ```
    fn bit_mut(&mut self, index: Index<Self>) -> BitMut<'_, Self>;

    /// Returns Set complement (`self′`) of `Bitset`.<br/>
    /// Alias for [`!`] operator
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let a = Bitset8::from(0b11110000);
    /// let b = a.complement();
    ///
    /// assert_eq!(a.into_inner(), 0b11110000);
    /// assert_eq!(b.into_inner(), 0b00001111);
    /// #   Ok(())
    /// # }
    /// ```
    fn complement(self) -> Self;

    /// Returns Set union (`self ∪ other`) of two `Bitset`s.<br/>
    /// Alias for [`|`] operator
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let a = Bitset8::from(0b11001100);
    /// let b = Bitset8::from(0b11110000);
    /// let c = a.union(b);
    ///
    /// assert_eq!(c.into_inner(), 0b11111100);
    /// #   Ok(())
    /// # }
    /// ```
    fn union(self, other: Self) -> Self;

    /// Returns Set intersection (`self ∩ other`) of two `Bitset`s.<br/>
    /// Alias for [`&`] operator
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let a = Bitset8::from(0b11001100);
    /// let b = Bitset8::from(0b11110000);
    /// let c = a.intersection(b);
    ///
    /// assert_eq!(c.into_inner(), 0b11000000);
    /// #   Ok(())
    /// # }
    /// ```
    fn intersection(self, other: Self) -> Self;

    /// Returns Set difference (`self \ other`) of two `Bitset`s.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let a = Bitset8::from(0b11001100);
    /// let b = Bitset8::from(0b11110000);
    /// let c = a.difference(b);
    ///
    /// assert_eq!(c.into_inner(), 0b00001100);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn difference(self, other: Self) -> Self {
        self.intersection(other.complement())
    }

    /// Returns Set symmetric difference (`self Δ other`) of two `Bitset`s.<br/>
    /// Alias for [`^`] operator
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let a = Bitset8::from(0b11001100); // implements Bitset
    /// let b = Bitset8::from(0b11110000);
    /// let c = a.sym_difference(b);
    ///
    /// assert_eq!(c.into_inner(), 0b00111100);
    /// #   Ok(())
    /// # }
    /// ```
    fn sym_difference(self, other: Self) -> Self;

    #[inline(always)]
    fn super_set(self, other: Self) -> bool {
        self.intersection(other.clone()) == other
    }

    #[inline(always)]
    fn intersects(self, other: Self) -> bool {
        self.intersection(other) != Self::NONE
    }

    /// Combines two `Bitset`s to create a bigger one.<br/>
    /// If available, you should prefer using [`Bitset::combine_optimized`].
    ///
    /// # Errors
    /// Size of `Res` is smaller, than the sum of size of `Self` and size of `Other`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8, Bitset16};
    ///
    /// let bitset8_1 = Bitset8::from(0b00000001);
    /// let bitset8_2 = Bitset8::from(0b00000011);
    /// let bitset16: Bitset16 = bitset8_1.combine(bitset8_2)?;
    ///
    /// assert_eq!(bitset16.into_inner(), 0b0000001100000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn combine<Other, Res>(self, other: Other) -> ConvResult<Res>
    where
        Other: Bitset,
        Res: Bitset,
    {
        let combined = Self::BYTE_SIZE + Other::BYTE_SIZE;
        if Res::BYTE_SIZE == combined {
            let mut result = self
                .bits_ref()
                .enumerate()
                .map(|(i, bit)| (Index::<Res>::try_from(i).unwrap(), bit))
                .fold(&mut Res::NONE.clone(), |acc, (i, bit)| acc.set_bit(i, *bit))
                .build();

            let result = other
                .bits_ref()
                .enumerate()
                .map(|(i, bit)| (Index::<Res>::try_from(i + bit_len::<Self>()).unwrap(), bit))
                .fold(&mut result, |acc, (i, bit)| acc.set_bit(i, *bit))
                .build();
            Ok(result)
        } else {
            Err(ConvError::new(
                ConvTarget::Set(combined * 8),
                ConvTarget::Set(bit_len::<Res>()),
            ))
        }
    }

    /// Splits `Bitset` into two smaller ones.<br/>
    /// If available, you should prefer using [`Bitset::split_optimized`].
    ///
    /// # Errors
    /// Size of `Self` is smaller, than the sum of size of `Res1` and size of `Res2`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8, Bitset16};
    ///
    /// let bitset16 = Bitset16::from(0b0000001100000001);
    /// let (bitset8_1, bitset8_2): (Bitset8, Bitset8) = bitset16.split()?;
    ///
    /// assert_eq!(bitset8_1.into_inner(), 0b00000001);
    /// assert_eq!(bitset8_2.into_inner(), 0b00000011);
    /// #   Ok(())
    /// # }
    /// ```
    fn split<Res1, Res2>(self) -> ConvResult<(Res1, Res2)>
    where
        Res1: Bitset,
        Res2: Bitset,
    {
        let combined = Res1::BYTE_SIZE + Res2::BYTE_SIZE;
        if Self::BYTE_SIZE == combined {
            let result1 = self
                .bits_ref()
                .take(bit_len::<Res1>())
                .enumerate()
                .map(|(i, bit)| (Index::<Res1>::try_from(i).unwrap(), bit))
                .fold(&mut Res1::NONE.clone(), |acc, (i, bit)| {
                    acc.set_bit(i, *bit)
                })
                .build();

            let result2 = self
                .bits_ref()
                .skip(bit_len::<Res1>())
                .enumerate()
                .map(|(i, bit)| (Index::<Res2>::try_from(i).unwrap(), bit))
                .fold(&mut Res2::NONE.clone(), |acc, (i, bit)| {
                    acc.set_bit(i, *bit)
                })
                .build();

            Ok((result1, result2))
        } else {
            Err(ConvError::new(
                ConvTarget::Set(bit_len::<Self>()),
                ConvTarget::Set(combined * 8),
            ))
        }
    }

    /// Combines two `Bitset`s to create a bigger one. Uses `unsafe` optimizations.
    ///
    /// # Errors
    /// Size of `Res` is smaller, than the sum of size of `Self` and size of `Other`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8, Bitset16};
    ///
    /// let bitset8_1 = Bitset8::from(0b00000001);
    /// let bitset8_2 = Bitset8::from(0b00000011);
    /// let bitset16: Bitset16 = bitset8_1.combine_optimized(bitset8_2)?;
    ///
    /// assert_eq!(bitset16.into_inner(), 0b0000001100000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn combine_optimized<Other, Res>(self, other: Other) -> ConvResult<Res>
    where
        Self: LeftAligned,
        Other: Bitset + LeftAligned,
        Res: Bitset + LeftAligned,
    {
        let combined = Self::BYTE_SIZE + Other::BYTE_SIZE;

        if Res::BYTE_SIZE == combined {
            let mut result = Res::NONE.clone();

            unsafe {
                std::ptr::copy_nonoverlapping(
                    &self as *const _ as *const u8,
                    &mut result as *mut _ as *mut u8,
                    Self::BYTE_SIZE,
                );

                std::ptr::copy_nonoverlapping(
                    &other as *const _ as *const u8,
                    (&mut result as *mut _ as *mut u8).add(Self::BYTE_SIZE),
                    Other::BYTE_SIZE,
                );
            }
            Ok(result)
        } else {
            Err(ConvError::new(
                ConvTarget::Set(combined * 8),
                ConvTarget::Set(bit_len::<Res>()),
            ))
        }
    }

    /// Splits `Bitset` into two smaller ones. Uses `unsafe` optimizations.
    ///
    /// # Errors
    /// Size of `Self` is smaller, than the sum of size of `Res1` and size of `Res2`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8, Bitset16};
    ///
    /// let bitset16 = Bitset16::from(0b0000001100000001);
    /// let (bitset8_1, bitset8_2): (Bitset8, Bitset8) = bitset16.split_optimized()?;
    ///
    /// assert_eq!(bitset8_1.into_inner(), 0b00000001);
    /// assert_eq!(bitset8_2.into_inner(), 0b00000011);
    /// #   Ok(())
    /// # }
    /// ```
    fn split_optimized<Res1, Res2>(self) -> ConvResult<(Res1, Res2)>
    where
        Self: LeftAligned,
        Res1: Bitset + LeftAligned,
        Res2: Bitset + LeftAligned,
    {
        let combined = Res1::BYTE_SIZE + Res2::BYTE_SIZE;

        if Self::BYTE_SIZE == combined {
            let mut result1 = Res1::NONE.clone();
            let mut result2 = Res2::NONE.clone();

            unsafe {
                std::ptr::copy_nonoverlapping(
                    &self as *const _ as *const u8,
                    &mut result1 as *mut _ as *mut u8,
                    Res1::BYTE_SIZE,
                );

                std::ptr::copy_nonoverlapping(
                    (&self as *const _ as *const u8).add(Res1::BYTE_SIZE),
                    &mut result2 as *mut _ as *mut u8,
                    Res2::BYTE_SIZE,
                );
            }
            Ok((result1, result2))
        } else {
            Err(ConvError::new(
                ConvTarget::Set(bit_len::<Self>()),
                ConvTarget::Set(combined * 8),
            ))
        }
    }

    /// Returns iterator over bits of the `Bitset` in [`Bit`] representation.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::*;
    ///
    /// let bitset = Bitset8::from(0b01010100);
    /// let mut iter = bitset.bits();
    ///
    /// assert_eq!(iter.next(), Some(Zero)); // 0
    /// assert_eq!(iter.next(), Some(Zero)); // 0
    /// assert_eq!(iter.next(), Some(One));  // 1
    /// assert_eq!(iter.next(), Some(Zero)); // 0
    /// assert_eq!(iter.next(), Some(One));  // 1
    /// assert_eq!(iter.next(), Some(Zero)); // 0
    /// assert_eq!(iter.next(), Some(One));  // 1
    /// assert_eq!(iter.next(), Some(Zero)); // 0
    /// assert_eq!(iter.next(), None);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn bits(self) -> impl Iterator<Item = Bit>
    where
        Self: Copy,
    {
        (0..bit_len::<Self>())
            .map(|i| Index::<Self>::try_from(i).unwrap())
            .map(move |i| self.bit(i))
    }

    /// Returns iterator over [`BitRef`] holding immutable references
    /// to bits of the bitset.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::*;
    ///
    /// let bitset = Bitset8::from(0b01010100);
    /// let mut iter = bitset.bits_ref();
    ///
    /// assert_eq!(iter.next().as_deref(), Some(&Zero)); // 0
    /// assert_eq!(iter.next().as_deref(), Some(&Zero)); // 0
    /// assert_eq!(iter.next().as_deref(), Some(&One));  // 1
    /// assert_eq!(iter.next().as_deref(), Some(&Zero)); // 0
    /// assert_eq!(iter.next().as_deref(), Some(&One));  // 1
    /// assert_eq!(iter.next().as_deref(), Some(&Zero)); // 0
    /// assert_eq!(iter.next().as_deref(), Some(&One));  // 1
    /// assert_eq!(iter.next().as_deref(), Some(&Zero)); // 0
    /// assert_eq!(iter.next(), None);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn bits_ref(&self) -> impl Iterator<Item = BitRef<'_, Self>> {
        (0..bit_len::<Self>())
            .map(|i| Index::<Self>::try_from(i).unwrap())
            .map(|i| self.bit_ref(i))
    }

    /// Returns iterator over [`BitMut`] holding mutable references
    /// to bits of the bitset.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let mut bitset = Bitset8::from(0b01010100);
    /// let mut iter = bitset.bits_mut();
    ///
    /// for mut bit in iter {
    ///     *bit = !*bit;
    /// }
    ///
    /// assert_eq!(bitset.into_inner(), 0b10101011);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn bits_mut(&mut self) -> impl Iterator<Item = BitMut<'_, Self>> {
        let p = self as *mut Self;
        (0..bit_len::<Self>())
            .map(|i| Index::<Self>::try_from(i).unwrap())
            .map(move |i| unsafe { p.as_mut().unwrap().bit_mut(i) })
    }

    /// Returns iterator over [`indeces`][Index] of the set bits of the `Bitset`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::from(0b01010100);
    /// let mut iter = bitset.ones();
    ///
    /// assert_eq!(iter.next(), Some(2.try_into()?));
    /// assert_eq!(iter.next(), Some(4.try_into()?));
    /// assert_eq!(iter.next(), Some(6.try_into()?));
    /// assert_eq!(iter.next(), None);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn ones(&self) -> impl Iterator<Item = Index<Self>> {
        self.bits_ref().filter_map(|bit| {
            if bool::from(*bit) {
                Some(BitRef::index(&bit))
            } else {
                None
            }
        })
    }

    /// Returns iterator over [`indeces`][Index] of the unset bits of the `Bitset`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::from(0b01010100);
    /// let mut iter = bitset.zeros();
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
    fn zeros(&self) -> impl Iterator<Item = Index<Self>> {
        self.bits_ref().filter_map(|bit| {
            if bool::from(!*bit) {
                Some(BitRef::index(&bit))
            } else {
                None
            }
        })
    }
}

/// Left-aligned [`Bitset`].
///
/// Implementors of this trait get access to these methods defined on `Bitset`:
/// * [`Bitset::expand_optimized()`]
/// * [`Bitset::combine_optimized()`]
/// * [`Bitset::split_optimized()`]
///
/// All the methods above have corresponding versions without `_optimized` suffix, which contains no `unsafe` code
/// and aren't restricted to only `Simple` types.
///
/// # Safety
/// If you implement this trait, you are responsible for making sure, that part in memory of the implementor,
/// which contains the inner representation of the bitset, is aligned on the left.
/// Alignment here is not the same as Rust struct alignment, so I'll provide an example here
/// of what structs are valid and invalid for implementing this trait:
///
/// ### ✅ LeftAligned Bitset structs:
/// ```
/// struct A(u8); // u8 here represents the bitset.
///
/// struct B { bitset: u8 }
///
/// #[repr(C)]
/// struct C(u8, String); // only u8 here represents the bitset.
///
/// #[repr(C)]
/// struct D { bitset: u8, metadata: String }
/// ```
///
/// ### ❌ *NOT* LeftAligned Bitset structs:
/// ```
/// struct E(u8, String); // exact ordreing is not guaranteed
///
/// struct F { bitset: u8, metadata: String } // exact ordreing is not guaranteed
///
/// #[repr(C)] // ordering is guaranteed, but order is incorrect
/// struct G(String, u8); // only u8 here represents the Bitset.
///
/// #[repr(C)] // ordering is guaranteed, but order is incorrect
/// struct H { metadata: String, bitset: u8 }
/// ```
///
/// In general, any `one-set tuple struct`s or `one-set C-like struct`s are good implementors of this trait,
/// but only if the data in that set has consistent memory layout:<br/>
/// E.g. any [`Sized`] owned primitive types or arrays of them, but not tuples, references, pointers etc.<br/>
/// It is `unsafe` to implement this trait for second kind of structs and will lead to memory violations or
/// unintended and undefined behaviour.
///
/// If you're unsure about what this means, use built-in `Bitset`s (they all implement `Simple`)
/// or do not implement this trait for your custom `Bitset` (the trade-off should be minimal).
pub unsafe trait LeftAligned: Bitset
where
    Self::_Repr: Sized + Clone + PartialEq + Eq,
{
    type _Repr;

    const _BYTE_SIZE: usize;

    const _ONE: Self;

    const _ALL: Self;

    const _NONE: Self;

    fn _new(value: Self::Repr) -> Self;

    fn shift_left(mut self, amount: Index<Self>) -> Self {
        let byte_shift = byte_index(amount);
        let bit_shift = bit_index(amount);

        let ptr = &mut self as *mut _ as *mut u8;

        if byte_shift > 0 {
            unsafe {
                std::ptr::copy(ptr.add(byte_shift), ptr, Self::BYTE_SIZE - byte_shift);
                std::ptr::write_bytes(ptr.add(Self::BYTE_SIZE - byte_shift), 0, byte_shift);
            }
        }

        if bit_shift > 0 {
            let bytes: &mut [u8] = unsafe { std::slice::from_raw_parts_mut(ptr, Self::BYTE_SIZE) };
            let mut carry = 0;
            for byte in bytes.iter_mut().rev() {
                let shifted = *byte << bit_shift | carry;
                carry = *byte >> (8 - bit_shift);
                *byte = shifted;
            }
        }
        self
    }

    fn shift_right(mut self, amount: Index<Self>) -> Self {
        let byte_shift = byte_index(amount);
        let bit_shift = bit_index(amount);

        let ptr = &mut self as *mut _ as *mut u8;

        if byte_shift > 0 {
            unsafe {
                std::ptr::copy(ptr, ptr.add(byte_shift), Self::BYTE_SIZE - byte_shift);
                std::ptr::write_bytes(ptr, 0, byte_shift);
            }
        }

        if bit_shift > 0 {
            let bytes: &mut [u8] = unsafe { std::slice::from_raw_parts_mut(ptr, Self::BYTE_SIZE) };
            let mut carry = 0;
            for byte in bytes.iter_mut() {
                let shifted = *byte >> bit_shift | carry;
                carry = *byte << (8 - bit_shift);
                *byte = shifted;
            }
        }
        self
    }
}

impl<T> Bitset for T
where
    T: LeftAligned + Sized + Clone + PartialEq + Eq,
{
    type Repr = <Self as LeftAligned>::_Repr;
    const BYTE_SIZE: usize = Self::_BYTE_SIZE;
    const ONE: Self = Self::_ONE;
    const NONE: Self = Self::_NONE;
    const ALL: Self = Self::_ALL;

    #[inline(always)]
    fn new(value: Self::Repr) -> Self {
        Self::_new(value)
    }

    #[inline(always)]
    fn from_index(index: &Index<Self>) -> Self {
        Self::NONE.clone().check_bit(*index).clone()
    }

    #[inline(always)]
    fn count_ones(&self) -> usize {
        let bytes: &[u8] =
            unsafe { std::slice::from_raw_parts(self as *const _ as *const u8, Self::BYTE_SIZE) };

        bytes.iter().fold(0, |acc, &byte| acc + byte.count_ones()) as usize
    }

    #[inline(always)]
    fn count_zeros(&self) -> usize {
        let bytes: &[u8] =
            unsafe { std::slice::from_raw_parts(self as *const _ as *const u8, Self::BYTE_SIZE) };

        bytes.iter().fold(0, |acc, &byte| acc + byte.count_zeros()) as usize
    }

    #[inline(always)]
    fn check_bit(&mut self, index: Index<Self>) -> &mut Self {
        let self_ptr = self as *mut _ as *mut u8;
        unsafe {
            let byte = self_ptr.add(byte_index(index));
            *byte |= 1 << bit_index(index);
        }
        self
    }

    #[inline(always)]
    fn uncheck_bit(&mut self, index: Index<Self>) -> &mut Self {
        let self_ptr = self as *mut _ as *mut u8;
        unsafe {
            let byte = self_ptr.add(byte_index(index));
            *byte &= !(1 << bit_index(index));
        }
        self
    }

    #[inline(always)]
    fn bit(&self, index: Index<Self>) -> Bit {
        let self_ptr = self as *const _ as *const u8;
        let byte = unsafe { *self_ptr.add(byte_index(index)) };
        Bit::from(byte & bitmask(index) != 0)
    }

    #[inline(always)]
    fn bit_ref(&self, index: Index<Self>) -> BitRef<'_, Self> {
        let self_ptr = self as *const _ as *const u8;
        let byte = unsafe { *self_ptr.add(byte_index(index)) };
        BitRef(Bit::from(byte & bitmask(index) != 0), index, self)
    }

    #[inline(always)]
    fn bit_mut(&mut self, index: Index<Self>) -> BitMut<'_, Self> {
        let self_ptr = self as *mut _ as *const u8;
        let byte = unsafe { *self_ptr.add(byte_index(index)) };
        BitMut(Bit::from(byte & bitmask(index) != 0), index, self)
    }

    #[inline(always)]
    fn complement(mut self) -> Self {
        let bytes: &mut [u8] = unsafe {
            std::slice::from_raw_parts_mut(&mut self as *mut _ as *mut u8, Self::BYTE_SIZE)
        };

        for byte in bytes.iter_mut() {
            *byte = !*byte;
        }
        self
    }

    #[inline(always)]
    fn union(mut self, other: Self) -> Self {
        let self_bytes: &mut [u8] = unsafe {
            std::slice::from_raw_parts_mut(&mut self as *mut _ as *mut u8, Self::BYTE_SIZE)
        };
        let other_bytes: &[u8] =
            unsafe { std::slice::from_raw_parts(&other as *const _ as *const u8, Self::BYTE_SIZE) };

        for i in 0..Self::BYTE_SIZE {
            self_bytes[i] |= other_bytes[i];
        }
        self
    }

    #[inline(always)]
    fn intersection(mut self, other: Self) -> Self {
        let self_bytes: &mut [u8] = unsafe {
            std::slice::from_raw_parts_mut(&mut self as *mut _ as *mut u8, Self::BYTE_SIZE)
        };
        let other_bytes: &[u8] =
            unsafe { std::slice::from_raw_parts(&other as *const _ as *const u8, Self::BYTE_SIZE) };

        for i in 0..Self::BYTE_SIZE {
            self_bytes[i] &= other_bytes[i];
        }
        self
    }

    #[inline(always)]
    fn difference(mut self, other: Self) -> Self {
        let self_bytes: &mut [u8] = unsafe {
            std::slice::from_raw_parts_mut(&mut self as *mut _ as *mut u8, Self::BYTE_SIZE)
        };
        let other_bytes: &[u8] =
            unsafe { std::slice::from_raw_parts(&other as *const _ as *const u8, Self::BYTE_SIZE) };

        for i in 0..Self::BYTE_SIZE {
            self_bytes[i] &= !other_bytes[i];
        }
        self
    }

    #[inline(always)]
    fn sym_difference(mut self, other: Self) -> Self {
        let self_bytes: &mut [u8] = unsafe {
            std::slice::from_raw_parts_mut(&mut self as *mut _ as *mut u8, Self::BYTE_SIZE)
        };
        let other_bytes: &[u8] =
            unsafe { std::slice::from_raw_parts(&other as *const _ as *const u8, Self::BYTE_SIZE) };

        for i in 0..Self::BYTE_SIZE {
            self_bytes[i] ^= other_bytes[i];
        }
        self
    }
}