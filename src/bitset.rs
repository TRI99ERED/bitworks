//! Module containing [`Bitset`].

use crate::{
    bit::{Bit, BitMut, BitRef},
    index::Index,
    safety_markers::{Combines, SizeMarker, Smaller, Splits},
};

// Length of Bitset in bits.
pub(crate) const fn bit_len<T>() -> usize
where
    T: Bitset,
{
    T::BYTE_SIZE * 8
}

/// Trait defining common bitset logic.
///
/// This trait is not meant to be implmented on enums, as beyond some extremely rare cases,
/// they won't produce a valid bitset.
///
/// It's recommended to prefer implementing this trait for structs, where  the first in order field is
/// representing the bitset, as that would allow you to implement [`LeftAligned`] marker on it safely.
/// If you want to get the benefits of `LeftAligned` on any struct, make it a wrapper around
/// one of the `LeftAligned` types and use it's methods. All built-in `Bitset` types are `LeftAligned`.
pub trait Bitset: Sized + Clone + PartialEq + Eq {
    /// Type, that is the underlying representation of the `Bitset`.<br/>
    /// Usually one of the Rust built-in types, but can be another `Bitset` or even `Self`.
    type Repr: Sized + Clone + PartialEq + Eq;

    /// Marker type representing size ordering. Used for compile time checks on some methods.
    type Size: SizeMarker;

    /// Number of bytes (`size` in bytes) of the bitset part.
    ///
    /// If the implementor contains additional data, its bytes
    /// should *NOT* be included when initializing this constant.
    ///
    /// Refer to [core::mem::size_of] if you need actual size of the type in other contexts.
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

    /// Constructs a new value of the `Bitset` from [`Bitset::Repr`].
    ///
    /// Prefer asignment, if `Self::Repr` is `Self`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::from_repr(1);
    ///
    /// assert_eq!(bitset.into_inner(), 0b00000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn from_repr(repr: Self::Repr) -> Self;

    /// Build `Bitset` from a mutable reference.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::*;
    ///
    /// let bitset = Bitset8::NONE
    ///     .include(Bitset8::new(0b00101111))
    ///     .replace(0.try_into()?, Zero)
    ///     .set(7.try_into()?)
    ///     .unset(2.try_into()?)
    ///     .build();
    ///
    /// assert_eq!(bitset.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn build(&mut self) -> Self {
        self.clone()
    }

    /// Constructs `Bitset` from [`Index`]. The resulting value always has only bit at index set.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
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
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8, Bitset16};
    ///
    /// let bitset8 = Bitset8::new(0b10101010);
    /// let bitset16: Bitset16 = bitset8.expand();
    ///
    /// assert_eq!(bitset16.into_inner(), 0b0000000010101010);
    /// #   Ok(())
    /// # }
    /// ```
    fn expand<Res>(self) -> Res
    where
        Res: Bitset,
        Self::Size: Smaller<Res::Size>,
    {
        let result = self
            .ones()
            .map(|Index(i, ..)| Index::<Res>::from_usize(i))
            .fold(&mut Res::NONE.clone(), |acc, i| acc.set(i))
            .build();

        result
    }

    /// Expands `Bitset` to a bigger one. Uses `unsafe` optimizations.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8, Bitset16};
    ///
    /// let bitset8 = Bitset8::new(0b10101010);
    /// let bitset16: Bitset16 = bitset8.expand_optimized();
    ///
    /// assert_eq!(bitset16.into_inner(), 0b0000000010101010);
    /// #   Ok(())
    /// # }
    /// ```
    fn expand_optimized<Res>(self) -> Res
    where
        Self: LeftAligned,
        Res: Bitset + LeftAligned,
        Self::Size: Smaller<Res::Size>,
    {
        let mut result = Res::NONE.clone();

        unsafe {
            std::ptr::copy_nonoverlapping(
                &self as *const _ as *const u8,
                &mut result as *mut _ as *mut u8,
                Self::BYTE_SIZE,
            );
        }
        result
    }

    /// Builds `Bitset` from the collection of [`Bit`] values.<br/>
    /// Maintains the same index order: first `Bit` item becomes the least significant bit.
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
    /// let bitset = Bitset8::from_iterable(slice);
    ///
    /// assert_eq!(bitset.into_inner(), 0b01010101);
    /// #   Ok(())
    /// # }
    /// ```
    fn from_iterable<'a, I>(iterable: I) -> Self
    where
        Self: 'a,
        I: IntoIterator<Item = &'a Bit>,
    {
        iterable
            .into_iter()
            .take(bit_len::<Self>())
            .enumerate()
            .filter(|(_, &b)| bool::from(b))
            .fold(&mut Self::NONE.clone(), |acc, (i, _)| {
                acc.set(Index::<_>::from_usize(i))
            })
            .build()
    }

    /// Returns the count of all set bits.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::new(0b00000111);
    ///
    /// assert_eq!(bitset.count_ones(), 3);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn count_ones(&self) -> usize {
        self.ones().count()
    }

    /// Returns the number of all unset bits.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::new(0b00000111);
    ///
    /// assert_eq!(bitset.count_zeros(), 5);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn count_zeros(&self) -> usize {
        self.zeros().count()
    }

    /// Replaces the bit at [`index`][Index] to the value. Returns a mutable reference to `self`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::*;
    ///
    /// let bitset = Bitset8::new(0b01010100)
    ///     .replace(1.try_into()?, One)
    ///     .replace(2.try_into()?, Zero)
    ///     .replace(3.try_into()?, One)
    ///     .replace(4.try_into()?, Zero)
    ///     .replace(5.try_into()?, One)
    ///     .replace(6.try_into()?, Zero)
    ///     .replace(7.try_into()?, One)
    ///     .build();
    ///
    /// assert_eq!(bitset.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn replace(&mut self, index: Index<Self>, value: Bit) -> &mut Self {
        if bool::from(value) {
            self.set(index);
        } else {
            self.unset(index);
        }
        self
    }

    /// Sets bit at [`index`][Index]. Returns a mutable reference to `self`.
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
    ///     .set(1.try_into()?)
    ///     .set(3.try_into()?)
    ///     .set(5.try_into()?)
    ///     .set(7.try_into()?)
    ///     .build();
    ///
    /// assert_eq!(bitset.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    fn set(&mut self, index: Index<Self>) -> &mut Self;

    /// Unsets bit at [`index`][Index]. Returns a mutable reference to `self`.
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
    ///     .unset(0.try_into()?)
    ///     .unset(2.try_into()?)
    ///     .unset(4.try_into()?)
    ///     .unset(6.try_into()?)
    ///     .build();
    ///
    /// assert_eq!(bitset.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    fn unset(&mut self, index: Index<Self>) -> &mut Self;

    /// Flips bit at [`index`][Index]. Returns a mutable reference to `self`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::new(0b11110000)
    ///     .flip(1.try_into()?)
    ///     .flip(3.try_into()?)
    ///     .flip(4.try_into()?)
    ///     .flip(6.try_into()?)
    ///     .build();
    ///
    /// assert_eq!(bitset.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    fn flip(&mut self, index: Index<Self>) -> &mut Self;

    /// Includes all set bits of `other` in `self`. Returns a mutable reference to `self`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::*;
    ///
    /// let bitset = Bitset8::new(0b00100010)
    ///     .include(Bitset8::new(0b10001000))
    ///     .build();
    ///
    /// assert_eq!(bitset.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    fn include(&mut self, other: Self) -> &mut Self;

    /// Excludes all set bits of `other` from `self`. Returns a mutable reference to `self`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::*;
    ///
    /// let bitset = Bitset8::new(0b11111110)
    ///     .exclude(Bitset8::new(0b01010100))
    ///     .build();
    ///
    /// assert_eq!(bitset.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    fn exclude(&mut self, other: Self) -> &mut Self;

    /// Returns a copy of the [`Bit`] at [`index`][Index].
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::*;
    ///
    /// let bitset = Bitset8::NONE.set(1.try_into()?).build();
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
    /// let bitset = Bitset8::NONE.set(1.try_into()?).build();
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
    /// Alias for [`!`][core::ops::Not] operator.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let a = Bitset8::new(0b11110000);
    /// let b = a.complement();
    ///
    /// assert_eq!(a.into_inner(), 0b11110000);
    /// assert_eq!(b.into_inner(), 0b00001111);
    /// #   Ok(())
    /// # }
    /// ```
    fn complement(self) -> Self;

    /// Returns Set union (`self ∪ other`) of two `Bitset`s.<br/>
    /// Alias for [`|`][core::ops::BitOr] operator.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let a = Bitset8::new(0b11001100);
    /// let b = Bitset8::new(0b11110000);
    /// let c = a.union(b);
    ///
    /// assert_eq!(c.into_inner(), 0b11111100);
    /// #   Ok(())
    /// # }
    /// ```
    fn union(self, other: Self) -> Self;

    /// Returns Set intersection (`self ∩ other`) of two `Bitset`s.<br/>
    /// Alias for [`&`][core::ops::BitAnd] operator.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let a = Bitset8::new(0b11001100);
    /// let b = Bitset8::new(0b11110000);
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
    /// let a = Bitset8::new(0b11001100);
    /// let b = Bitset8::new(0b11110000);
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
    /// Alias for [`^`][core::ops::BitXor] operator.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let a = Bitset8::new(0b11001100);
    /// let b = Bitset8::new(0b11110000);
    /// let c = a.sym_difference(b);
    ///
    /// assert_eq!(c.into_inner(), 0b00111100);
    /// #   Ok(())
    /// # }
    /// ```
    fn sym_difference(self, other: Self) -> Self;

    /// Returns [`true`], if `self` contains all of the set bits from `other` and [`false`] otherwise.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let a = Bitset8::new(0b11111100);
    /// let b = Bitset8::new(0b11110000);
    /// let c = Bitset8::new(0b00001111);
    ///
    /// assert!(a.includes(&b));
    /// assert!(!a.includes(&c));
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn includes(&self, other: &Self) -> bool {
        for i in other.ones() {
            if !bool::from(self.bit(i)) {
                return false;
            }
        }
        true
    }

    /// Returns [`true`], if `self` shares any set bits with `other` and [`false`] otherwise.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let a = Bitset8::new(0b11111100);
    /// let b = Bitset8::new(0b00001111);
    /// let c = Bitset8::new(0b00000011);
    ///
    /// assert!(a.intersects(&b));
    /// assert!(!a.intersects(&c));
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn intersects(&self, other: &Self) -> bool {
        for i in other.ones() {
            if bool::from(self.bit(i)) {
                return true;
            }
        }
        false
    }

    /// Combines two `Bitset`s to create a bigger one.<br/>
    /// If available, you should prefer using [`Bitset::combine_optimized`].
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8, Bitset16};
    ///
    /// let bitset8_1 = Bitset8::new(0b00000001);
    /// let bitset8_2 = Bitset8::new(0b00000011);
    /// let bitset16: Bitset16 = bitset8_1.combine(bitset8_2);
    ///
    /// assert_eq!(bitset16.into_inner(), 0b0000001100000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn combine<Other, Res>(self, other: Other) -> Res
    where
        Other: Bitset,
        Res: Bitset,
        Self::Size: Combines<Other::Size, Res::Size> + Smaller<Res::Size>,
        Other::Size: Smaller<Res::Size>,
    {
        let mut result = self
            .ones()
            .map(|Index(i, ..)| Index::<Res>::from_usize(i))
            .fold(&mut Res::NONE.clone(), |acc, i| acc.set(i))
            .build();

        let result = other
            .ones()
            .map(|Index(i, ..)| Index::<Res>::from_usize(i + bit_len::<Self>()))
            .fold(&mut result, |acc, i| acc.set(i))
            .build();
        result
    }

    /// Combines two `Bitset`s to create a bigger one. Uses `unsafe` optimizations.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8, Bitset16};
    ///
    /// let bitset8_1 = Bitset8::new(0b00000001);
    /// let bitset8_2 = Bitset8::new(0b00000011);
    /// let bitset16: Bitset16 = bitset8_1.combine_optimized(bitset8_2);
    ///
    /// assert_eq!(bitset16.into_inner(), 0b0000001100000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn combine_optimized<Other, Res>(self, other: Other) -> Res
    where
        Self: LeftAligned,
        Other: Bitset + LeftAligned,
        Res: Bitset + LeftAligned,
        Self::Size: Combines<Other::Size, Res::Size> + Smaller<Res::Size>,
        Other::Size: Smaller<Res::Size>,
    {
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
        result
    }

    /// Splits `Bitset` into two smaller ones.<br/>
    /// If available, you should prefer using [`Bitset::split_optimized`].
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8, Bitset16};
    ///
    /// let bitset16 = Bitset16::from(0b0000001100000001);
    /// let (bitset8_1, bitset8_2): (Bitset8, Bitset8) = bitset16.split();
    ///
    /// assert_eq!(bitset8_1.into_inner(), 0b00000001);
    /// assert_eq!(bitset8_2.into_inner(), 0b00000011);
    /// #   Ok(())
    /// # }
    /// ```
    fn split<Res1, Res2>(self) -> (Res1, Res2)
    where
        Res1: Bitset,
        Res2: Bitset,
        Self::Size: Splits<Res1::Size, Res2::Size>,
        Res1::Size: Smaller<Self::Size>,
        Res2::Size: Smaller<Self::Size>,
    {
        let result1 = self
            .bits_ref()
            .take(bit_len::<Res1>())
            .enumerate()
            .map(|(i, bit)| (Index::<Res1>::from_usize(i), bit))
            .fold(&mut Res1::NONE.clone(), |acc, (i, bit)| {
                acc.replace(i, *bit)
            })
            .build();

        let result2 = self
            .bits_ref()
            .skip(bit_len::<Res1>())
            .enumerate()
            .map(|(i, bit)| (Index::<Res2>::from_usize(i), bit))
            .fold(&mut Res2::NONE.clone(), |acc, (i, bit)| {
                acc.replace(i, *bit)
            })
            .build();

        (result1, result2)
    }

    /// Splits `Bitset` into two smaller ones. Uses `unsafe` optimizations.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8, Bitset16};
    ///
    /// let bitset16 = Bitset16::from(0b0000001100000001);
    /// let (bitset8_1, bitset8_2): (Bitset8, Bitset8) = bitset16.split_optimized();
    ///
    /// assert_eq!(bitset8_1.into_inner(), 0b00000001);
    /// assert_eq!(bitset8_2.into_inner(), 0b00000011);
    /// #   Ok(())
    /// # }
    /// ```
    fn split_optimized<Res1, Res2>(self) -> (Res1, Res2)
    where
        Self: LeftAligned,
        Res1: Bitset + LeftAligned,
        Res2: Bitset + LeftAligned,
        Self::Size: Splits<Res1::Size, Res2::Size>,
        Res1::Size: Smaller<Self::Size>,
        Res2::Size: Smaller<Self::Size>,
    {
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
        (result1, result2)
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
    /// let bitset = Bitset8::new(0b01010100);
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
    fn bits(self) -> impl Iterator<Item = Bit> + DoubleEndedIterator {
        (0..bit_len::<Self>())
            .map(|i| Index::<Self>::from_usize(i))
            .map(move |i| self.bit(i))
    }

    /// Returns iterator over [`BitRef`] holding immutable references
    /// to bits of the `Bitset`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::*;
    ///
    /// let bitset = Bitset8::new(0b01010100);
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
    fn bits_ref(&self) -> impl Iterator<Item = BitRef<'_, Self>> + DoubleEndedIterator {
        (0..bit_len::<Self>())
            .map(|i| Index::<Self>::from_usize(i))
            .map(|i| self.bit_ref(i))
    }

    /// Returns iterator over [`BitMut`] holding mutable references
    /// to bits of the `Bitset`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let mut bitset = Bitset8::new(0b01010101);
    /// let mut iter = bitset.bits_mut();
    ///
    /// for mut bit in iter {
    ///     *bit = !*bit;
    /// }
    ///
    /// assert_eq!(bitset.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn bits_mut(&mut self) -> impl Iterator<Item = BitMut<'_, Self>> + DoubleEndedIterator {
        let p = self as *mut Self;
        (0..bit_len::<Self>())
            .map(|i| Index::<Self>::from_usize(i))
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
    /// let bitset = Bitset8::new(0b01010100);
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
    fn ones(&self) -> impl Iterator<Item = Index<Self>> + DoubleEndedIterator {
        self.bits_ref().filter_map(|bit| {
            if bool::from(*bit) {
                Some(BitRef::index(&bit))
            } else {
                None
            }
        })
    }

    /// Returns iterator over [`indeces`][Index] of the not set bits of the `Bitset`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::new(0b01010100);
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
    fn zeros(&self) -> impl Iterator<Item = Index<Self>> + DoubleEndedIterator {
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
/// Implementors of this trait get blanket implementation of `Bitset`.
/// They also get access to these methods defined on `Bitset`:
/// * [`Bitset::expand_optimized()`]
/// * [`Bitset::combine_optimized()`]
/// * [`Bitset::split_optimized()`]
///
/// All the methods above have corresponding versions without `_optimized` suffix, which contains no `unsafe` code
/// and aren't restricted to only `LeftAligned` types.
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
/// struct E(u8, String); // exact ordering is not guaranteed
///
/// struct F { bitset: u8, metadata: String } // exact ordering is not guaranteed
///
/// #[repr(C)] // ordering is guaranteed, but order is incorrect
/// struct G(String, u8); // only u8 here represents the Bitset.
///
/// #[repr(C)] // ordering is guaranteed, but order is incorrect
/// struct H { metadata: String, bitset: u8 }
/// ```
///
/// In general, any `one-field tuple struct`s or `one-field C-like struct`s are good implementors of this trait,
/// but only if the data in that set has consistent memory layout:<br/>
/// E.g. any [`Sized`] owned primitive types or arrays of them, but *NOT* tuples, references, pointers,
/// non-LeftAligned structs etc.<br/>
/// It is `unsafe` to implement this trait for second kind of structs and will lead to memory violations or
/// unintended and undefined behaviour.
///
/// If you're unsure about what this means, use built-in `Bitset`s (they all implement `LeftAligned`)
/// or do not implement this trait for your custom `Bitset` and use unoptimized methods.
/// Alternatively you can make a wrapper around one of the built-in bitsets and implement `Bitset` on it,
/// delegating all of the methods to inner type's.
pub unsafe trait LeftAligned: Bitset + Sized + Clone + PartialEq + Eq {
    #[doc(hidden)]
    /// Type, that is the underlying representation of the `Bitset`.<br/>
    /// Usually one of the Rust built-in types, but can be `Self`.
    ///
    /// Used to set corresponding field [`Bitset::Repr`].
    type _Repr: Sized + Clone + PartialEq + Eq;

    #[doc(hidden)]
    /// Marker type representing size ordering. Used for compile time checks on some methods.
    ///
    /// Used to set corresponding field [`Bitset::Size`].
    type _Size: SizeMarker;

    #[doc(hidden)]
    /// Number of bytes (`size` in bytes) of the bitset part.
    ///
    /// Used to set corresponding field [`Bitset::BYTE_SIZE`].
    ///
    /// If the implementor contains additional data, its bytes
    /// should *NOT* be included when initializing this constant.
    ///
    /// Refer to [core::mem::size_of] if you need actual size of the type in other contexts.
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
    const _BYTE_SIZE: usize;

    #[doc(hidden)]
    /// Value of the `Bitset` with every bit not set.
    ///
    /// Used to set corresponding field [`Bitset::NONE`].
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
    const _NONE: Self;

    #[doc(hidden)]
    /// Value of the `Bitset` with every bit not set.
    ///
    /// Used to set corresponding field [`Bitset::ALL`].
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
    const _ALL: Self;

    #[doc(hidden)]
    /// Constructs a new value of the `Bitset` from [`Bitset::Repr`].
    ///
    /// Used to implement corresponding method [`Bitset::from_repr`].
    ///
    /// Prefer asignment, if `Self::Repr` is `Self`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset8};
    ///
    /// let bitset = Bitset8::new(1);
    ///
    /// assert_eq!(bitset.into_inner(), 0b00000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn _from_repr(value: Self::Repr) -> Self;

    /// Shifts bit representation of the `Bitset` left by amount.
    /// Has signature and use identical to [`core::ops::Shl<Index<Self>>`][core::ops::Shl].
    fn shift_left(mut self, amount: Index<Self>) -> Self {
        let byte_shift = amount.byte_index();
        let bit_shift = amount.bit_index();

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

    /// Shifts bit representation of the `Bitset` right by amount.
    /// Has signature and use identical to [`core::ops::Shr<Index<Self>>`][core::ops::Shr].
    fn shift_right(mut self, amount: Index<Self>) -> Self {
        let byte_shift = amount.byte_index();
        let bit_shift = amount.bit_index();

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
    type Size = <Self as LeftAligned>::_Size;
    const BYTE_SIZE: usize = Self::_BYTE_SIZE;
    const NONE: Self = Self::_NONE;
    const ALL: Self = Self::_ALL;

    #[inline(always)]
    fn from_repr(value: Self::Repr) -> Self {
        Self::_from_repr(value)
    }

    #[inline(always)]
    fn from_index(index: &Index<Self>) -> Self {
        Self::NONE.clone().set(*index).clone()
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
    fn set(&mut self, index: Index<Self>) -> &mut Self {
        let self_ptr = self as *mut _ as *mut u8;
        unsafe {
            let byte = self_ptr.add(index.byte_index());
            *byte |= index.bitmask();
        }
        self
    }

    #[inline(always)]
    fn unset(&mut self, index: Index<Self>) -> &mut Self {
        let self_ptr = self as *mut _ as *mut u8;
        unsafe {
            let byte = self_ptr.add(index.byte_index());
            *byte &= !index.bitmask();
        }
        self
    }

    #[inline(always)]
    fn flip(&mut self, index: Index<Self>) -> &mut Self {
        let self_ptr = self as *mut _ as *mut u8;
        unsafe {
            let byte = self_ptr.add(index.byte_index());
            *byte ^= index.bitmask();
        }
        self
    }

    #[inline(always)]
    fn include(&mut self, other: Self) -> &mut Self {
        let self_bytes: &mut [u8] =
            unsafe { std::slice::from_raw_parts_mut(self as *mut _ as *mut u8, Self::BYTE_SIZE) };
        let other_bytes: &[u8] =
            unsafe { std::slice::from_raw_parts(&other as *const _ as *const u8, Self::BYTE_SIZE) };

        for i in 0..Self::BYTE_SIZE {
            self_bytes[i] |= other_bytes[i];
        }
        self
    }

    #[inline(always)]
    fn exclude(&mut self, other: Self) -> &mut Self {
        let self_bytes: &mut [u8] =
            unsafe { std::slice::from_raw_parts_mut(self as *mut _ as *mut u8, Self::BYTE_SIZE) };
        let other_bytes: &[u8] =
            unsafe { std::slice::from_raw_parts(&other as *const _ as *const u8, Self::BYTE_SIZE) };

        for i in 0..Self::BYTE_SIZE {
            self_bytes[i] &= !other_bytes[i];
        }
        self
    }

    #[inline(always)]
    fn bit(&self, index: Index<Self>) -> Bit {
        let self_ptr = self as *const _ as *const u8;
        let byte = unsafe { *self_ptr.add(index.byte_index()) };
        Bit::from(byte & index.bitmask() != 0)
    }

    #[inline(always)]
    fn bit_ref(&self, index: Index<Self>) -> BitRef<'_, Self> {
        let self_ptr = self as *const _ as *const u8;
        let byte = unsafe { *self_ptr.add(index.byte_index()) };
        BitRef(Bit::from(byte & index.bitmask() != 0), index, self)
    }

    #[inline(always)]
    fn bit_mut(&mut self, index: Index<Self>) -> BitMut<'_, Self> {
        let self_ptr = self as *mut _ as *const u8;
        let byte = unsafe { *self_ptr.add(index.byte_index()) };
        BitMut(Bit::from(byte & index.bitmask() != 0), index, self)
    }

    #[inline]
    fn complement(mut self) -> Self {
        let bytes: &mut [u8] = unsafe {
            std::slice::from_raw_parts_mut(&mut self as *mut _ as *mut u8, Self::BYTE_SIZE)
        };

        for byte in bytes.iter_mut() {
            *byte = !*byte;
        }
        self
    }

    #[inline]
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

    #[inline]
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

    #[inline]
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

    #[inline]
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

    #[inline]
    fn includes(&self, other: &Self) -> bool {
        let self_bytes: &[u8] =
            unsafe { std::slice::from_raw_parts(self as *const _ as *const u8, Self::BYTE_SIZE) };
        let other_bytes: &[u8] =
            unsafe { std::slice::from_raw_parts(other as *const _ as *const u8, Self::BYTE_SIZE) };

        for i in 0..Self::BYTE_SIZE {
            if self_bytes[i] & other_bytes[i] != other_bytes[i] {
                return false;
            }
        }
        true
    }

    #[inline]
    fn intersects(&self, other: &Self) -> bool {
        let self_bytes: &[u8] =
            unsafe { std::slice::from_raw_parts(self as *const _ as *const u8, Self::BYTE_SIZE) };
        let other_bytes: &[u8] =
            unsafe { std::slice::from_raw_parts(other as *const _ as *const u8, Self::BYTE_SIZE) };

        for i in 0..Self::BYTE_SIZE {
            if self_bytes[i] & other_bytes[i] != 0 {
                return true;
            }
        }
        false
    }
}
