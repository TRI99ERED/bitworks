//! Module containing [`Bitfield`].

use crate::{
    bit_ref::{BitMut, BitRef},
    error::{ConvError, ConvResult, ConvTarget},
    // flags_enum::FlagsEnum,
    index::Index,
};

pub const fn bit_len<T>() -> usize
where
    T: Bitfield,
{
    T::BYTE_SIZE * 8
}

pub(crate) const fn byte_index<T>(index: Index<T>) -> usize
where
    T: Bitfield,
{
    index.into_inner() / 8
}

pub(crate) const fn bit_index<T>(index: Index<T>) -> usize
where
    T: Bitfield,
{
    index.into_inner() % 8
}

pub(crate) const fn bitmask<T>(index: Index<T>) -> u8
where
    T: Bitfield,
{
    1 << bit_index(index)
}

/// Trait defining common bitfield logic.
///
/// This trait is not meant to be implmented on enums, as beyond some extremely rare cases,
/// they won't produce a valid bitfield.
///
/// It's recommended to prefer implementing this trait for one-field structs, where that sole field is
/// representing the bitfield, as that would allow you to implement [`LeftAligned`] marker on it safely.
pub trait Bitfield: Sized + Clone + PartialEq + Eq {
    /// Number of bits (`size` in bits) of the `Bitfield`.
    ///
    /// If implementor contsina addidtional data, it's bits
    /// should `NOT` be included when defining this constant
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let size_in_bits = Bitfield8::BYTE_SIZE;
    ///
    /// assert_eq!(size_in_bits, 1);
    /// #   Ok(())
    /// # }
    /// ```
    const BYTE_SIZE: usize;

    /// Value of the `Bitfield` with the least significant bit set.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::ONE;
    ///
    /// assert_eq!(bitfield.into_inner(), 0b00000001);
    /// #   Ok(())
    /// # }
    /// ```
    const ONE: Self;

    /// Value of the `Bitfield` with every bit unset.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::NONE;
    ///
    /// assert_eq!(bitfield.into_inner(), 0b00000000);
    /// #   Ok(())
    /// # }
    /// ```
    const NONE: Self;

    /// Value of the `Bitfield` with every bit set.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::ALL;
    ///
    /// assert_eq!(bitfield.into_inner(), 0b11111111);
    /// #   Ok(())
    /// # }
    /// ```
    const ALL: Self;

    /// Build `Bitfield` from a mutable reference.<br/>
    /// Useful for chaining bit modifications.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::NONE
    ///     .set_bit(0.try_into()?, true)
    ///     .check_bit(6.try_into()?)
    ///     .uncheck_bit(0.try_into()?)
    ///     .build();
    ///
    /// assert_eq!(bitfield.into_inner(), 0b01000000);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn build(&mut self) -> Self {
        self.clone()
    }

    /// Constructs `Bitfield` from [`Index`].
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Index};
    ///
    /// let index = 0.try_into()?;
    /// let bitfield = Bitfield8::from_index(&index);
    ///
    /// assert_eq!(bitfield.into_inner(), 0b00000001);
    ///
    /// let index = 3.try_into()?;
    /// let bitfield = Bitfield8::from_index(&index);
    ///
    /// assert_eq!(bitfield.into_inner(), 0b00001000);
    /// #   Ok(())
    /// # }
    /// ```
    fn from_index(index: &Index<Self>) -> Self;

    // /// Constructs `Bitfield` from `T`, where `T` implements [`FlagsEnum`].
    // ///
    // /// # Examples
    // /// ```rust
    // /// # use std::error::Error;
    // /// #
    // /// # fn main() -> Result<(), Box<dyn Error>> {
    // /// use simple_bitfield::{prelude::{Bitfield, Bitfield8, FlagsEnum, Index}, error::{ConvError, ConvTarget}};
    // ///
    // /// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    // /// enum E {
    // ///     A, // 0
    // ///     B, // 1
    // ///     D  =  3,
    // ///     E, // 4
    // /// }
    // ///
    // /// impl TryFrom<Index<Bitfield8>> for E {
    // ///     type Error = ConvError;
    // ///
    // ///     fn try_from(index: Index<Bitfield8>) -> Result<Self, Self::Error> {
    // ///         match index.into_inner() {
    // ///             0 => Ok(E::A),
    // ///             1 => Ok(E::B),
    // ///             3 => Ok(E::D),
    // ///             4 => Ok(E::E),
    // ///             _ => Err(ConvError::new(ConvTarget::Index(8), ConvTarget::Enum(8))),
    // ///         }
    // ///     }
    // /// }
    // ///
    // /// impl From<E> for Index<Bitfield8> {
    // ///     fn from(value: E) -> Self {
    // ///         Self::try_from(value as usize).expect("Enum E should always be a valid index")
    // ///     }
    // /// }
    // ///
    // /// impl FlagsEnum for E {
    // ///     type Bitfield = Bitfield8;
    // /// }
    // ///
    // /// let flag = E::A;
    // /// let bitfield = Bitfield8::from_flag(&flag);
    // ///
    // /// assert_eq!(bitfield.into_inner(), 0b00000001);
    // ///
    // /// let flag = E::D;
    // /// let bitfield = Bitfield8::from_flag(&flag);
    // ///
    // /// assert_eq!(bitfield.into_inner(), 0b00001000);
    // /// # Ok(())
    // /// # }
    // /// ```
    // #[inline(always)]
    // fn from_flag<T>(flag: &T) -> Self
    // where
    //     T: FlagsEnum<Bitfield = Self> + Copy,
    //     Index<Self>: From<T>,
    // {
    //     Self::ONE << Index::<Self>::from(*flag)
    // }

    /// Expands `Bitfield` to a bigger one.<br/>
    /// If available, you should prefer using [`Bitfield::fast_expand`].
    ///
    /// # Errors
    /// Size of `Res` is smaller, than size of `Self`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Bitfield16};
    ///
    /// let bitfield8 = Bitfield8::from(0b00000001);
    /// let bitfield16: Bitfield16 = bitfield8.expand()?;
    ///
    /// assert_eq!(bitfield16.into_inner(), 0b0000000000000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn expand<Res>(self) -> ConvResult<Res>
    where
        Res: Bitfield,
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
                ConvTarget::Field(bit_len::<Self>()),
                ConvTarget::Field(bit_len::<Res>()),
            ))
        }
    }

    /// Expands `Bitfield` to a bigger one. Uses `unsafe` optimizations.
    ///
    /// # Errors
    /// Size of `Res` is smaller, than size of `Self`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Bitfield16};
    ///
    /// let bitfield8 = Bitfield8::from(0b00000001);
    /// let bitfield16: Bitfield16 = bitfield8.expand_optimized()?;
    ///
    /// assert_eq!(bitfield16.into_inner(), 0b0000000000000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn expand_optimized<Res>(self) -> ConvResult<Res>
    where
        Self: LeftAligned,
        Res: Bitfield + LeftAligned,
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
                ConvTarget::Field(bit_len::<Self>()),
                ConvTarget::Field(bit_len::<Res>()),
            ))
        }
    }

    /// Builds `Bitfield` from [`slice`] over [`bool`]ean values.<br/>
    /// Maintains the same index order: leftmost `slice` item becomes the least significant bit.
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
    /// let bitfield = Bitfield8::from_bits_ref(slice);
    ///
    /// assert_eq!(bitfield.into_inner(), 0b01010101);
    /// #   Ok(())
    /// # }
    /// ```
    fn from_bits_ref<'a, I>(iter: I) -> Self
    where
        I: IntoIterator<Item = &'a bool>,
    {
        iter.into_iter()
            .take(bit_len::<Self>())
            .enumerate()
            .map(|(i, &b)| (Index::<Self>::try_from(i).unwrap(), b))
            .fold(&mut Self::NONE.clone(), |acc, (i, b)| acc.set_bit(i, b))
            .build()
    }

    // /// Builds `Bitfield` from slice over `T` values, where `T` implements [`FlagsEnum`].<br/>
    // /// Considers contained variants as set bits.
    // ///
    // /// # Examples
    // /// ```rust
    // /// # use std::error::Error;
    // /// #
    // /// # fn main() -> Result<(), Box<dyn Error>> {
    // /// use simple_bitfield::{prelude::{Bitfield, Bitfield8, FlagsEnum, Index}, error::{ConvError, ConvTarget}};
    // ///
    // /// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    // /// enum E {
    // ///     A, // 0
    // ///     B, // 1
    // ///     D  =  3,
    // ///     E, // 4
    // /// }
    // ///
    // /// impl TryFrom<Index<Bitfield8>> for E {
    // ///     type Error = ConvError;
    // ///
    // ///     fn try_from(index: Index<Bitfield8>) -> Result<Self, Self::Error> {
    // ///         match index.into_inner() {
    // ///             0 => Ok(E::A),
    // ///             1 => Ok(E::B),
    // ///             3 => Ok(E::D),
    // ///             4 => Ok(E::E),
    // ///             _ => Err(ConvError::new(ConvTarget::Index(8), ConvTarget::Enum(8))),
    // ///         }
    // ///     }
    // /// }
    // ///
    // /// impl From<E> for Index<Bitfield8> {
    // ///     fn from(value: E) -> Self {
    // ///         Self::try_from(value as usize).expect("Enum E should always be a valid index")
    // ///     }
    // /// }
    // ///
    // /// impl FlagsEnum for E {
    // ///     type Bitfield = Bitfield8;
    // /// }
    // ///
    // /// let slice: &[E] = &[E::A, E::E, E::D];
    // /// let bitfield = Bitfield8::from_selected_variants_ref(slice);
    // ///
    // /// assert_eq!(bitfield.into_inner(), 0b00011001);
    // /// #   Ok(())
    // /// # }
    // /// ```
    // fn from_selected_variants_ref<'a, I, T>(iter: I) -> Self
    // where
    //     I: IntoIterator<Item = &'a T>,
    //     T: FlagsEnum<Bitfield = Self> + Copy + 'a,
    //     Index<Self>: From<T>,
    //     Self: FromIterator<T>,
    // {
    //     let mut bitfield = Self::NONE;
    //     let mut seen_indices = BTreeSet::new();

    //     for &e in iter {
    //         let index = Index::<Self>::from(e);
    //         if !seen_indices.contains(&index) {
    //             seen_indices.insert(index);
    //             bitfield.check_bit(index);
    //         }
    //     }
    //     bitfield
    // }

    // /// Builds `Bitfield` from slice over `T` values, where `T` implements [`FlagsEnum`].<br/>
    // /// Considers contained variants as unset bits.
    // ///
    // /// # Examples
    // /// ```rust
    // /// # use std::error::Error;
    // /// #
    // /// # fn main() -> Result<(), Box<dyn Error>> {
    // /// use simple_bitfield::{prelude::{Bitfield, Bitfield8, FlagsEnum, Index}, error::{ConvError, ConvTarget}};
    // ///
    // /// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    // /// enum E {
    // ///     A, // 0
    // ///     B, // 1
    // ///     D  =  3,
    // ///     E, // 4
    // /// }
    // ///
    // /// impl TryFrom<Index<Bitfield8>> for E {
    // ///     type Error = ConvError;
    // ///
    // ///     fn try_from(index: Index<Bitfield8>) -> Result<Self, Self::Error> {
    // ///         match index.into_inner() {
    // ///             0 => Ok(E::A),
    // ///             1 => Ok(E::B),
    // ///             3 => Ok(E::D),
    // ///             4 => Ok(E::E),
    // ///             _ => Err(ConvError::new(ConvTarget::Index(8), ConvTarget::Enum(8))),
    // ///         }
    // ///     }
    // /// }
    // ///
    // /// impl From<E> for Index<Bitfield8> {
    // ///     fn from(value: E) -> Self {
    // ///         Self::try_from(value as usize).expect("Enum E should always be a valid index")
    // ///     }
    // /// }
    // ///
    // /// impl FlagsEnum for E {
    // ///     type Bitfield = Bitfield8;
    // /// }
    // ///
    // /// let slice: &[E] = &[E::A, E::E, E::D];
    // /// let bitfield = Bitfield8::from_unselected_variants_ref(slice);
    // ///
    // /// assert_eq!(bitfield.into_inner(), 0b11100110);
    // /// #   Ok(())
    // /// # }
    // /// ```
    // fn from_unselected_variants_ref<'a, I, T>(iter: I) -> Self
    // where
    //     I: IntoIterator<Item = &'a T>,
    //     T: FlagsEnum<Bitfield = Self> + Copy + 'a,
    //     Index<Self>: From<T>,
    //     Self: FromIterator<T>,
    // {
    //     let mut bitfield = Self::ALL;
    //     let mut seen_indices = BTreeSet::new();

    //     for &e in iter {
    //         let index = Index::<Self>::from(e);
    //         if !seen_indices.contains(&index) {
    //             seen_indices.insert(index);
    //             bitfield.uncheck_bit(index);
    //         }
    //     }
    //     bitfield
    // }

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
    /// assert_eq!(bitfield.count_ones(), 3);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn count_ones(&self) -> usize {
        (0..bit_len::<Self>()).fold(0, |acc, i| {
            acc + if *self.bit_ref(i.try_into().unwrap()) {
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
    /// assert_eq!(bitfield.count_zeros(), 5);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    fn count_zeros(&self) -> usize {
        (0..bit_len::<Self>()).fold(0, |acc, i| {
            acc + (if *self.bit_ref(i.try_into().unwrap()) {
                0
            } else {
                1
            })
        })
    }

    /// Sets bit at [`index`][Index] to value. Returns copy of the resulting `Bitfield`.
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
    ///     .set_bit(7.try_into()?, true)
    ///     .build();
    ///
    /// assert_eq!(bitfield.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    fn set_bit(&mut self, index: Index<Self>, value: bool) -> &mut Self;

    /// Sets bit at [`index`][Index] to 1. Returns copy of the resulting `Bitfield`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::NONE
    ///     .clone()
    ///     .check_bit(1.try_into()?)
    ///     .check_bit(3.try_into()?)
    ///     .check_bit(5.try_into()?)
    ///     .check_bit(7.try_into()?)
    ///     .build();
    ///
    /// assert_eq!(bitfield.into_inner(), 0b10101010);
    /// #   Ok(())
    /// # }
    /// ```
    fn check_bit(&mut self, index: Index<Self>) -> &mut Self;

    /// Sets bit at [`index`][Index] to 0. Returns copy of the resulting `Bitfield`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::ALL
    ///     .clone()
    ///     .uncheck_bit(0.try_into()?)
    ///     .uncheck_bit(2.try_into()?)
    ///     .uncheck_bit(4.try_into()?)
    ///     .uncheck_bit(6.try_into()?)
    ///     .build();
    ///
    /// assert_eq!(bitfield.into_inner(), 0b10101010);
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
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::NONE.set_bit(1.try_into()?, true).build();
    ///
    /// assert_eq!(bitfield.bit(0.try_into()?), false);
    /// assert_eq!(bitfield.bit(1.try_into()?), true);
    /// #   Ok(())
    /// # }
    /// ```
    fn bit(self, index: Index<Self>) -> bool;

    /// Returns a [`BitRef`] holding an immutable reference to the bit at [`index`][Index].
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::NONE.set_bit(1.try_into()?, true).build();
    ///
    /// assert_eq!(*bitfield.bit_ref(0.try_into()?), false);
    /// assert_eq!(*bitfield.bit_ref(1.try_into()?), true);
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
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let mut bitfield = Bitfield8::NONE;
    ///
    /// assert_eq!(bitfield.bit(0.try_into()?), false);
    /// assert_eq!(bitfield.bit(1.try_into()?), false);
    ///
    /// *bitfield.bit_mut(0.try_into()?) = true;
    ///
    /// assert_eq!(bitfield.bit(0.try_into()?), true);
    /// assert_eq!(bitfield.bit(1.try_into()?), false);
    /// #   Ok(())
    /// # }
    /// ```
    fn bit_mut(&mut self, index: Index<Self>) -> BitMut<'_, Self>;

    /// Returns Set complement (`self′`) of `Bitfield`.<br/>
    /// Alias for [`!`] operator
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let a = Bitfield8::from(0b11110000);
    /// let b = a.complement();
    ///
    /// assert_eq!(a.into_inner(), 0b11110000);
    /// assert_eq!(b.into_inner(), 0b00001111);
    /// #   Ok(())
    /// # }
    /// ```
    fn complement(self) -> Self;

    /// Returns Set union (`self ∪ other`) of two `Bitfield`s.<br/>
    /// Alias for [`|`] operator
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
    /// let c = a.union(b);
    ///
    /// assert_eq!(c.into_inner(), 0b11111100);
    /// #   Ok(())
    /// # }
    /// ```
    fn union(self, other: Self) -> Self;

    /// Returns Set intersection (`self ∩ other`) of two `Bitfield`s.<br/>
    /// Alias for [`&`] operator
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
    /// let c = a.intersection(b);
    ///
    /// assert_eq!(c.into_inner(), 0b11000000);
    /// #   Ok(())
    /// # }
    /// ```
    fn intersection(self, other: Self) -> Self;

    /// Returns Set difference (`self \ other`) of two `Bitfield`s.
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

    /// Returns Set symmetric difference (`self Δ other`) of two `Bitfield`s.<br/>
    /// Alias for [`^`] operator
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

    /// Combines two `Bitfield`s to create a bigger one.<br/>
    /// If available, you should prefer using [`Bitfield::fast_combine`].
    ///
    /// # Errors
    /// Size of `Res` is smaller, than the sum of size of `Self` and size of `Other`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Bitfield16};
    ///
    /// let bitfield8_1 = Bitfield8::from(0b00000001);
    /// let bitfield8_2 = Bitfield8::from(0b00000011);
    /// let bitfield16: Bitfield16 = bitfield8_1.combine(bitfield8_2)?;
    ///
    /// assert_eq!(bitfield16.into_inner(), 0b0000001100000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn combine<Other, Res>(self, other: Other) -> ConvResult<Res>
    where
        Other: Bitfield,
        Res: Bitfield,
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
                ConvTarget::Field(combined * 8),
                ConvTarget::Field(bit_len::<Res>()),
            ))
        }
    }

    /// Splits `Bitfield` into two smaller ones.<br/>
    /// If available, you should prefer using [`Bitfield::fast_split`].
    ///
    /// # Errors
    /// Size of `Self` is smaller, than the sum of size of `Res1` and size of `Res2`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Bitfield16};
    ///
    /// let bitfield16 = Bitfield16::from(0b0000001100000001);
    /// let (bitfield8_1, bitfield8_2): (Bitfield8, Bitfield8) = bitfield16.split()?;
    ///
    /// assert_eq!(bitfield8_1.into_inner(), 0b00000001);
    /// assert_eq!(bitfield8_2.into_inner(), 0b00000011);
    /// #   Ok(())
    /// # }
    /// ```
    fn split<Res1, Res2>(self) -> ConvResult<(Res1, Res2)>
    where
        Res1: Bitfield,
        Res2: Bitfield,
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
                ConvTarget::Field(bit_len::<Self>()),
                ConvTarget::Field(combined * 8),
            ))
        }
    }

    /// Combines two `Bitfield`s to create a bigger one. Uses `unsafe` optimizations.
    ///
    /// # Errors
    /// Size of `Res` is smaller, than the sum of size of `Self` and size of `Other`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Bitfield16};
    ///
    /// let bitfield8_1 = Bitfield8::from(0b00000001);
    /// let bitfield8_2 = Bitfield8::from(0b00000011);
    /// let bitfield16: Bitfield16 = bitfield8_1.combine_optimized(bitfield8_2)?;
    ///
    /// assert_eq!(bitfield16.into_inner(), 0b0000001100000001);
    /// #   Ok(())
    /// # }
    /// ```
    fn combine_optimized<Other, Res>(self, other: Other) -> ConvResult<Res>
    where
        Self: LeftAligned,
        Other: Bitfield + LeftAligned,
        Res: Bitfield + LeftAligned,
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
                ConvTarget::Field(combined * 8),
                ConvTarget::Field(bit_len::<Res>()),
            ))
        }
    }

    /// Splits `Bitfield` into two smaller ones. Uses `unsafe` optimizations.
    ///
    /// # Errors
    /// Size of `Self` is smaller, than the sum of size of `Res1` and size of `Res2`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8, Bitfield16};
    ///
    /// let bitfield16 = Bitfield16::from(0b0000001100000001);
    /// let (bitfield8_1, bitfield8_2): (Bitfield8, Bitfield8) = bitfield16.split_optimized()?;
    ///
    /// assert_eq!(bitfield8_1.into_inner(), 0b00000001);
    /// assert_eq!(bitfield8_2.into_inner(), 0b00000011);
    /// #   Ok(())
    /// # }
    /// ```
    fn split_optimized<Res1, Res2>(self) -> ConvResult<(Res1, Res2)>
    where
        Self: LeftAligned,
        Res1: Bitfield + LeftAligned,
        Res2: Bitfield + LeftAligned,
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
                ConvTarget::Field(bit_len::<Self>()),
                ConvTarget::Field(combined * 8),
            ))
        }
    }

    /// Returns iterator over bits of the `Bitfield` in [`bool`]ean representation.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::from(0b01010100);
    /// let mut iter = bitfield.bits();
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
    fn bits(self) -> impl Iterator<Item = bool>
    where
        Self: Copy,
    {
        (0..bit_len::<Self>())
            .map(|i| Index::<Self>::try_from(i).unwrap())
            .map(move |i| self.bit(i))
    }

    /// Returns iterator over [`BitRef`] holding immutable references
    /// to bits of the bitfield in [`bool`]ean representation.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::from(0b01010100);
    /// let mut iter = bitfield.bits_ref();
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
        (0..bit_len::<Self>())
            .map(|i| Index::<Self>::try_from(i).unwrap())
            .map(|i| self.bit_ref(i))
    }

    /// Returns iterator over [`BitMut`] holding mutable references
    /// to bits of the bitfield in [`bool`]ean representation.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let mut bitfield = Bitfield8::from(0b01010100);
    /// let mut iter = bitfield.bits_mut();
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
        (0..bit_len::<Self>())
            .map(|i| Index::<Self>::try_from(i).unwrap())
            .map(move |i| unsafe { p.as_mut().unwrap().bit_mut(i) })
    }

    /// Returns iterator over [`indeces`][Index] of the set bits of the `Bitfield`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::from(0b01010100);
    /// let mut iter = bitfield.ones();
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
        self.bits_ref().enumerate().filter_map(|(i, bit)| {
            if *bit {
                Some(i.try_into().unwrap())
            } else {
                None
            }
        })
    }

    /// Returns iterator over [`indeces`][Index] of the unset bits of the `Bitfield`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::{Bitfield, Bitfield8};
    ///
    /// let bitfield = Bitfield8::from(0b01010100);
    /// let mut iter = bitfield.zeros();
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
        self.bits_ref().enumerate().filter_map(|(i, bit)| {
            if !*bit {
                Some(i.try_into().unwrap())
            } else {
                None
            }
        })
    }

    // /// Returns iterator over set bit [`indeces`][Index] of the `Bitfield`
    // /// converted to target type `T`, where `T` implements [`FlagsEnum`].
    // ///
    // /// # Examples
    // /// ```rust
    // /// # use std::error::Error;
    // /// #
    // /// # fn main() -> Result<(), Box<dyn Error>> {
    // /// use simple_bitfield::{prelude::{Bitfield, Bitfield8, FlagsEnum, Index}, error::{ConvError, ConvTarget}};
    // ///
    // /// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    // /// enum E {
    // ///     A, // 0
    // ///     B, // 1
    // ///     D  =  3,
    // ///     E, // 4
    // /// }
    // ///
    // /// impl TryFrom<Index<Bitfield8>> for E {
    // ///     type Error = ConvError;
    // ///
    // ///     fn try_from(index: Index<Bitfield8>) -> Result<Self, Self::Error> {
    // ///         match index.into_inner() {
    // ///             0 => Ok(E::A),
    // ///             1 => Ok(E::B),
    // ///             3 => Ok(E::D),
    // ///             4 => Ok(E::E),
    // ///             _ => Err(ConvError::new(ConvTarget::Index(8), ConvTarget::Enum(8))),
    // ///         }
    // ///     }
    // /// }
    // ///
    // /// impl From<E> for Index<Bitfield8> {
    // ///     fn from(value: E) -> Self {
    // ///         Self::try_from(value as usize).expect("Enum E should always be a valid index")
    // ///     }
    // /// }
    // ///
    // /// impl FlagsEnum for E {
    // ///     type Bitfield = Bitfield8;
    // /// }
    // ///
    // ///                                // E D _ B A
    // /// let bitfield = Bitfield8::from(0b_0_1_1_0_1);
    // /// let mut iter = bitfield.selected_variants::<E>();
    // ///
    // /// assert_eq!(iter.next(), Some(E::A));
    // /// assert_eq!(iter.next(), Some(E::D));
    // /// assert_eq!(iter.next(), None);
    // /// # Ok(())
    // /// # }
    // /// ```
    // #[inline(always)]
    // fn selected_variants<T>(&self) -> impl Iterator<Item = T>
    // where
    //     T: FlagsEnum<Bitfield = Self>,
    //     Index<Self>: From<T>,
    // {
    //     self.ones().filter_map(|i| T::try_from(i).ok())
    // }

    // /// Returns iterator over unset bit [`indeces`][Index] of the `Bitfield`
    // /// converted to target type `T`, where `T` implements [`FlagsEnum`].
    // ///
    // /// # Examples
    // /// ```rust
    // /// # use std::error::Error;
    // /// #
    // /// # fn main() -> Result<(), Box<dyn Error>> {
    // /// use simple_bitfield::{prelude::{Bitfield, Bitfield8, FlagsEnum, Index}, error::{ConvError, ConvTarget}};
    // ///
    // /// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    // /// enum E {
    // ///     A, // 0
    // ///     B, // 1
    // ///     D  =  3,
    // ///     E, // 4
    // /// }
    // ///
    // /// impl TryFrom<Index<Bitfield8>> for E {
    // ///     type Error = ConvError;
    // ///
    // ///     fn try_from(index: Index<Bitfield8>) -> Result<Self, Self::Error> {
    // ///         match index.into_inner() {
    // ///             0 => Ok(E::A),
    // ///             1 => Ok(E::B),
    // ///             3 => Ok(E::D),
    // ///             4 => Ok(E::E),
    // ///             _ => Err(ConvError::new(ConvTarget::Index(8), ConvTarget::Enum(8))),
    // ///         }
    // ///     }
    // /// }
    // ///
    // /// impl From<E> for Index<Bitfield8> {
    // ///     fn from(value: E) -> Self {
    // ///         Self::try_from(value as usize).expect("Enum E should always be a valid index")
    // ///     }
    // /// }
    // ///
    // /// impl FlagsEnum for E {
    // ///     type Bitfield = Bitfield8;
    // /// }
    // ///
    // ///                                // E D _ B A
    // /// let bitfield = Bitfield8::from(0b_0_1_1_0_1);
    // /// let mut iter = bitfield.unselected_variants::<E>();
    // ///
    // /// assert_eq!(iter.next(), Some(E::B));
    // /// assert_eq!(iter.next(), Some(E::E));
    // /// assert_eq!(iter.next(), None);
    // /// #   Ok(())
    // /// # }
    // /// ```
    // #[inline(always)]
    // fn unselected_variants<T>(&self) -> impl Iterator<Item = T>
    // where
    //     T: FlagsEnum<Bitfield = Self>,
    //     Index<Self>: From<T>,
    // {
    //     self.zeros().filter_map(|i| T::try_from(i).ok())
    // }
}

/// Left-aligned [`Bitfield`].
///
/// Implementors of this trait get access to these methods defined on `Bitfield`:
/// * [`Bitfield::expand_optimized()`]
/// * [`Bitfield::combine_optimized()`]
/// * [`Bitfield::split_optimized()`]
///
/// All the methods above have corresponding versions without `_optimized` suffix, which contains no `unsafe` code
/// and aren't restricted to only `Simple` types.
///
/// # Safety
/// If you implement this trait, you are responsible for making sure, that part in memory of the implementor,
/// which contains the inner representation of the bitfield, is aligned on the left.
/// Alignment here is not the same as Rust struct alignment, so I'll provide an example here
/// of what structs are valid and invalid for implementing this trait:
///
/// ### ✅ LeftAligned Bitfield structs:
/// ```
/// struct A(u8); // u8 here represents the bitfield.
///
/// struct B { bitfield: u8 }
///
/// #[repr(C)]
/// struct C(u8, String); // only u8 here represents the bitfield.
///
/// #[repr(C)]
/// struct D { bitfield: u8, metadata: String }
/// ```
///
/// ### ❌ *NOT* LeftAligned Bitfield structs:
/// ```
/// struct E(u8, String); // exact ordreing is not guaranteed
///
/// struct F { bitfield: u8, metadata: String } // exact ordreing is not guaranteed
///
/// #[repr(C)] // ordering is guaranteed, but order is incorrect
/// struct G(String, u8); // only u8 here represents the Bitfield.
///
/// #[repr(C)] // ordering is guaranteed, but order is incorrect
/// struct H { metadata: String, bitfield: u8 }
/// ```
///
/// In general, any `one-field tuple struct`s or `one-field C-like struct`s are good implementors of this trait,
/// but only if the data in that field has consistent memory layout:<br/>
/// E.g. any [`Sized`] owned primitive types or arrays of them, but not tuples, references, pointers etc.<br/>
/// It is `unsafe` to implement this trait for second kind of structs and will lead to memory violations or
/// unintended and undefined behaviour.
///
/// If you're unsure about what this means, use built-in `Bitfield`s (they all implement `Simple`)
/// or do not implement this trait for your custom `Bitfield` (the trade-off should be minimal).
pub unsafe trait LeftAligned: Bitfield {
    const _BYTE_SIZE: usize;
    const _ONE: Self;
    const _ALL: Self;
    const _NONE: Self;

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

/// Marker trait for simple [`Bitfield`]s.
///
/// Implementors of this trait must also implement [`LeftAligned`] and get blanket implementation of
/// `Bitfield`.
///
/// # Safety
/// If you implement this trait, you are responsible for making sure, that part in memory of the implementor,
/// which contains the inner representation of the bitfield, is aligned on the right.
/// Alignment here is not the same as Rust struct alignment, so I'll provide an example here
/// of what structs are valid and invalid for implementing this trait:
///
/// ### ✅ RightAligned Bitfield structs:
/// ```
/// struct A(u8); // u8 here represents the bitfield.
///
/// struct B { bitfield: u8 }
///
/// #[repr(C)]
/// struct C(String, u8); // only u8 here represents the bitfield.
///
/// #[repr(C)]
/// struct D { metadata: String, bitfield: u8 }
/// ```
///
/// ### ❌ *NOT* RightAligned Bitfield structs:
/// ```
/// struct E(String, u8); // exact ordreing is not guaranteed
///
/// struct F { metadata: String, bitfield: u8 } // exact ordreing is not guaranteed
///
/// #[repr(C)] // ordering is guaranteed, but order is incorrect
/// struct G(u8, String); // only u8 here represents the Bitfield.
///
/// #[repr(C)] // ordering is guaranteed, but order is incorrect
/// struct H { bitfield: u8, metadata: String }
/// ```
///
/// In general, any `one-field tuple struct`s or `one-field C-like struct`s are good implementors of this trait,
/// but only if the data in that field has consistent memory layout:<br/>
/// E.g. any [`Sized`] owned primitive types or arrays of them, but not tuples, references, pointers etc.<br/>
/// It is `unsafe` to implement this trait for second kind of structs and will lead to memory violations or
/// unintended and undefined behaviour.
///
/// If you're unsure about what this means, use built-in `Bitfield`s (they all implement `Simple`)
/// or do not implement this trait for your custom `Bitfield` (the trade-off should be minimal).
#[deprecated]
pub unsafe trait RightAligned: LeftAligned {}

#[deprecated]
pub unsafe trait Simple: Bitfield {}

impl<T> Bitfield for T
where
    T: LeftAligned + Sized + Clone + PartialEq + Eq,
{
    const BYTE_SIZE: usize = Self::_BYTE_SIZE;

    const ONE: Self = Self::_ONE;

    const NONE: Self = Self::_NONE;

    const ALL: Self = Self::_ALL;

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
    fn set_bit(&mut self, index: Index<Self>, value: bool) -> &mut Self {
        let self_ptr = self as *mut _ as *mut u8;
        unsafe {
            let byte = self_ptr.add(byte_index(index));
            if value {
                *byte |= 1 << bit_index(index);
            } else {
                *byte &= !(1 << bit_index(index));
            }
        }
        self
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
    fn bit(self, index: Index<Self>) -> bool {
        let self_ptr = &self as *const _ as *const u8;
        let byte = unsafe { *self_ptr.add(byte_index(index)) };
        byte & bitmask(index) != 0
    }

    #[inline(always)]
    fn bit_ref(&self, index: Index<Self>) -> BitRef<'_, Self> {
        let self_ptr = self as *const _ as *const u8;
        let byte = unsafe { *self_ptr.add(byte_index(index)) };
        BitRef(byte & bitmask(index) != 0, index, self)
    }

    #[inline(always)]
    fn bit_mut(&mut self, index: Index<Self>) -> BitMut<'_, Self> {
        let self_ptr = self as *mut _ as *const u8;
        let byte = unsafe { *self_ptr.add(byte_index(index)) };
        BitMut(byte & bitmask(index) != 0, index, self)
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
