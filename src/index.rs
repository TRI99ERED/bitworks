//! Module containing BitfieldIndex.

use crate::{
    error::{ConvError, ConvResult, ConvTarget},
    prelude::Bitfield,
};
use std::{cmp::Ordering, marker::PhantomData};

/// Struct meant to safely index the T, where T implements Bitfield.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BitfieldIndex<T: Bitfield>(usize, PhantomData<T>);

impl<T> BitfieldIndex<T>
where
    T: Bitfield,
{
    /// Value of 1 for `BitfieldIndex`.<br/>
    /// Shortcut from having to use `BitfieldIndex::<T>::try_from(1).unwrap()`
    pub const ONE: Self = Self(1, PhantomData);

    /// Minimum value for `BitfieldIndex`.<br/>
    /// Shortcut from having to use `BitfieldIndex::<T>::try_from(usize::MIN).unwrap()`
    pub const MIN: Self = Self(0, PhantomData);

    /// Maximum value for `BitfieldIndex`.<br/>
    /// Shortcut from having to use `BitfieldIndex::<T>::try_from(T::BITS - 1).unwrap()`
    pub const MAX: Self = Self(T::BIT_SIZE - 1, PhantomData);

    /// Returns value of `BitfieldIndex`.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield8, BitfieldIndex};
    ///
    /// fn example() {
    ///     let index = BitfieldIndex::<Bitfield8>::MAX;
    ///     assert_eq!(index.into_inner(), 7);
    /// }
    /// ```
    #[inline(always)]
    pub fn into_inner(&self) -> usize {
        self.0
    }

    /// Returns optional `BitfieldIndex`, that is sum of self and other, or `None` on overflow.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield8, BitfieldIndex};
    ///
    /// fn example() {
    ///     let a = BitfieldIndex::<Bitfield8>::ONE;
    ///     let b = BitfieldIndex::<Bitfield8>::ONE;
    ///     let c = a.checked_add(b);
    ///     assert_eq!(c.unwrap().into_inner(), 2);
    ///
    ///     let d = BitfieldIndex::<Bitfield8>::MAX;
    ///     let e = BitfieldIndex::<Bitfield8>::ONE;
    ///     let f = d.checked_add(e);
    ///     assert_eq!(f, None);
    /// }
    /// ```
    #[inline(always)]
    pub fn checked_add(&self, other: Self) -> Option<Self> {
        self.0
            .checked_add(other.0)
            .filter(|&i| i < T::BIT_SIZE)
            .map(|i| Self(i, PhantomData))
    }

    /// Returns optional `BitfieldIndex`, that is difference of self and other, or `None` on overflow.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield8, BitfieldIndex};
    ///
    /// fn example() {
    ///     let a = BitfieldIndex::<Bitfield8>::MAX;
    ///     let b = BitfieldIndex::<Bitfield8>::ONE;
    ///     let c = a.checked_sub(b);
    ///     assert_eq!(c.unwrap().into_inner(), 6);
    ///
    ///     let d = BitfieldIndex::<Bitfield8>::MIN;
    ///     let e = BitfieldIndex::<Bitfield8>::ONE;
    ///     let f = d.checked_sub(e);
    ///     assert_eq!(f, None);
    /// }
    /// ```
    #[inline(always)]
    pub fn checked_sub(&self, other: Self) -> Option<Self> {
        self.0.checked_sub(other.0).map(|i| Self(i, PhantomData))
    }

    /// Returns `BitfieldIndex`, that is sum of self and other, or `BitfieldIndex::<T>::MAX` on overflow.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield8, BitfieldIndex};
    ///
    /// fn example() {
    ///     let a = BitfieldIndex::<Bitfield8>::ONE;
    ///     let b = BitfieldIndex::<Bitfield8>::ONE;
    ///     let c = a.saturating_add(b);
    ///     assert_eq!(c.into_inner(), 2);
    ///
    ///     let d = BitfieldIndex::<Bitfield8>::MAX;
    ///     let e = BitfieldIndex::<Bitfield8>::ONE;
    ///     let f = d.saturating_add(e);
    ///     assert_eq!(f.into_inner(), 7);
    /// }
    /// ```
    #[inline(always)]
    pub fn saturating_add(&self, other: Self) -> Self {
        self.checked_add(other).unwrap_or(Self::MAX)
    }

    /// Returns `BitfieldIndex`, that is difference of self and other, or `BitfieldIndex::<T>::MIN` on overflow.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield8, BitfieldIndex};
    ///
    /// fn example() {
    ///     let a = BitfieldIndex::<Bitfield8>::MAX;
    ///     let b = BitfieldIndex::<Bitfield8>::ONE;
    ///     let c = a.saturating_sub(b);
    ///     assert_eq!(c.into_inner(), 6);
    ///
    ///     let d = BitfieldIndex::<Bitfield8>::MIN;
    ///     let e = BitfieldIndex::<Bitfield8>::ONE;
    ///     let f = d.saturating_sub(e);
    ///     assert_eq!(f.into_inner(), 0);
    /// }
    /// ```
    #[inline(always)]
    pub fn saturating_sub(&self, other: Self) -> Self {
        self.checked_sub(other).unwrap_or(Self::MIN)
    }

    /// Saturating conversion between BifieldIndeces.
    #[inline(always)]
    pub fn to_other<U>(self) -> BitfieldIndex<U>
    where
        U: Bitfield,
    {
        if U::BIT_SIZE >= T::BIT_SIZE {
            BitfieldIndex::<U>(self.0, PhantomData)
        } else {
            BitfieldIndex::<U>::MAX
        }
    }

    /// Attempted conversion between BifieldIndeces.
    #[inline(always)]
    pub fn try_to_other<U>(self) -> ConvResult<BitfieldIndex<U>>
    where
        U: Bitfield,
    {
        if U::BIT_SIZE >= T::BIT_SIZE {
            Ok(BitfieldIndex::<U>(self.0, PhantomData))
        } else {
            BitfieldIndex::<U>::try_from(self.0).map_err(|_| {
                ConvError::new(
                    ConvTarget::Index(U::BIT_SIZE),
                    ConvTarget::Index(T::BIT_SIZE),
                )
            })
        }
    }

    /// Range unsafe sum of self and other.
    #[inline(always)]
    pub(crate) fn __add(&self, other: Self) -> Self {
        Self(self.0 + other.0, PhantomData)
    }

    /// Range unsafe difference of self and other.
    #[inline(always)]
    pub(crate) fn __sub(&self, other: Self) -> Self {
        Self(self.0 - other.0, PhantomData)
    }
}

impl<T> TryFrom<usize> for BitfieldIndex<T>
where
    T: Bitfield,
{
    type Error = ConvError;

    #[inline(always)]
    fn try_from(value: usize) -> Result<Self, Self::Error> {
        if value < T::BIT_SIZE {
            Ok(Self(value, PhantomData))
        } else {
            Err(ConvError::new(
                ConvTarget::Raw(value),
                ConvTarget::Index(T::BIT_SIZE),
            ))
        }
    }
}

impl<T> From<BitfieldIndex<T>> for usize
where
    T: Bitfield,
{
    #[inline(always)]
    fn from(value: BitfieldIndex<T>) -> Self {
        value.0
    }
}

impl<T> PartialOrd for BitfieldIndex<T>
where
    T: Bitfield,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for BitfieldIndex<T>
where
    T: Bitfield,
{
    fn cmp(&self, other: &Self) -> Ordering {
        match self.0.cmp(&other.0) {
            Ordering::Equal => {}
            ord => return ord,
        }
        self.1.cmp(&other.1)
    }
}
