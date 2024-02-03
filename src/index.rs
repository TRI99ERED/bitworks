//! Module containing BitfieldIndex.

use crate::prelude::Bitfield;
use std::{cmp::Ordering, marker::PhantomData};

/// Struct meant to safely index the T, where T implements Bitfield.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
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
    pub const MAX: Self = Self(T::BITS - 1, PhantomData);

    /// Returns value of `BitfieldIndex`.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield8, BitfieldIndex};
    ///
    /// fn example() {
    ///     let index = BitfieldIndex::<Bitfield8>::MAX;
    ///     assert_eq!(index.value(), 7);
    /// }
    /// ```
    #[inline(always)]
    pub fn value(&self) -> usize {
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
    ///     assert_eq!(c.unwrap().value(), 2);
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
            .filter(|&i| i < T::BITS)
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
    ///     assert_eq!(c.unwrap().value(), 6);
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
    ///     assert_eq!(c.value(), 2);
    ///
    ///     let d = BitfieldIndex::<Bitfield8>::MAX;
    ///     let e = BitfieldIndex::<Bitfield8>::ONE;
    ///     let f = d.saturating_add(e);
    ///     assert_eq!(f.value(), 7);
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
    ///     assert_eq!(c.value(), 6);
    ///
    ///     let d = BitfieldIndex::<Bitfield8>::MIN;
    ///     let e = BitfieldIndex::<Bitfield8>::ONE;
    ///     let f = d.saturating_sub(e);
    ///     assert_eq!(f.value(), 0);
    /// }
    /// ```
    #[inline(always)]
    pub fn saturating_sub(&self, other: Self) -> Self {
        self.checked_sub(other).unwrap_or(Self::MIN)
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
    type Error = String;

    #[inline(always)]
    fn try_from(value: usize) -> Result<Self, Self::Error> {
        if value < T::BITS {
            Ok(Self(value, PhantomData))
        } else {
            Err(format!("value has to be in bounds of 0..{}", T::BITS))
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
