//! Module containing [`Index`].

use crate::{
    error::{ConvError, ConvResult, ConvTarget},
    prelude::Bitfield,
};
use std::{cmp::Ordering, fmt::Debug, hash::Hash, marker::PhantomData};

/// Struct meant to safely index the `T`, where `T` implements [`Bitfield`].
#[derive(Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Index<T: Bitfield>(pub(crate) usize, pub(crate) PhantomData<T>);

impl<T> Index<T>
where
    T: Bitfield,
{
    /// Value of 1 for `Index`.<br/>
    /// Shortcut from having to use `Index::<T>::try_from(1).unwrap()`
    pub const ONE: Self = Self(1, PhantomData);

    /// Minimum value for `Index`.<br/>
    /// Shortcut from having to use `Index::<T>::try_from(usize::MIN).unwrap()`
    pub const MIN: Self = Self(0, PhantomData);

    /// Maximum value for `Index`.<br/>
    /// Shortcut from having to use `Index::<T>::try_from(T::BITS - 1).unwrap()`
    pub const MAX: Self = Self(crate::bitfield::bit_len::<T>() - 1, PhantomData);

    /// Returns value of `Index` as [`usize`].
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield8, Index};
    ///
    /// fn example() {
    ///     let index = Index::<Bitfield8>::MAX;
    ///     assert_eq!(index.into_inner(), 7);
    /// }
    /// ```
    #[inline(always)]
    pub const fn into_inner(&self) -> usize {
        self.0
    }

    /// Returns [`Some`] `Index`, that is sum of `self` and `other`, or [`None`] on overflow.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield8, Index};
    ///
    /// fn example() {
    ///     let a = Index::<Bitfield8>::ONE;
    ///     let b = Index::<Bitfield8>::ONE;
    ///     let c = a.checked_add(b);
    ///     assert_eq!(c.unwrap().into_inner(), 2);
    ///
    ///     let d = Index::<Bitfield8>::MAX;
    ///     let e = Index::<Bitfield8>::ONE;
    ///     let f = d.checked_add(e);
    ///     assert_eq!(f, None);
    /// }
    /// ```
    #[inline(always)]
    pub fn checked_add(&self, other: Self) -> Option<Self> {
        self.0
            .checked_add(other.0)
            .filter(|&i| i < crate::bitfield::bit_len::<T>())
            .map(|i| Self(i, PhantomData))
    }

    /// Returns [`Some`] `Index`, that is difference of `self` and `other`, or [`None`] on overflow.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield8, Index};
    ///
    /// fn example() {
    ///     let a = Index::<Bitfield8>::MAX;
    ///     let b = Index::<Bitfield8>::ONE;
    ///     let c = a.checked_sub(b);
    ///     assert_eq!(c.unwrap().into_inner(), 6);
    ///
    ///     let d = Index::<Bitfield8>::MIN;
    ///     let e = Index::<Bitfield8>::ONE;
    ///     let f = d.checked_sub(e);
    ///     assert_eq!(f, None);
    /// }
    /// ```
    #[inline(always)]
    pub fn checked_sub(&self, other: Self) -> Option<Self> {
        self.0.checked_sub(other.0).map(|i| Self(i, PhantomData))
    }

    /// Returns `Index`, that is sum of `self` and `other`,
    /// or [`Index::<T>::MAX`] on overflow.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield8, Index};
    ///
    /// fn example() {
    ///     let a = Index::<Bitfield8>::ONE;
    ///     let b = Index::<Bitfield8>::ONE;
    ///     let c = a.saturating_add(b);
    ///     assert_eq!(c.into_inner(), 2);
    ///
    ///     let d = Index::<Bitfield8>::MAX;
    ///     let e = Index::<Bitfield8>::ONE;
    ///     let f = d.saturating_add(e);
    ///     assert_eq!(f.into_inner(), 7);
    /// }
    /// ```
    #[inline(always)]
    pub fn saturating_add(&self, other: Self) -> Self {
        self.checked_add(other).unwrap_or(Self::MAX)
    }

    /// Returns `Index`, that is difference of `self` and `other`,
    /// or [`Index::<T>::MIN`] on overflow.
    ///
    /// # Examples
    /// ```
    /// use simple_bitfield::prelude::{Bitfield8, Index};
    ///
    /// fn example() {
    ///     let a = Index::<Bitfield8>::MAX;
    ///     let b = Index::<Bitfield8>::ONE;
    ///     let c = a.saturating_sub(b);
    ///     assert_eq!(c.into_inner(), 6);
    ///
    ///     let d = Index::<Bitfield8>::MIN;
    ///     let e = Index::<Bitfield8>::ONE;
    ///     let f = d.saturating_sub(e);
    ///     assert_eq!(f.into_inner(), 0);
    /// }
    /// ```
    #[inline(always)]
    pub fn saturating_sub(&self, other: Self) -> Self {
        self.checked_sub(other).unwrap_or(Self::MIN)
    }

    /// Saturating conversion between `BifieldIndex`es.
    #[inline(always)]
    pub const fn to_other<U>(self) -> Index<U>
    where
        U: Bitfield,
    {
        if crate::bitfield::bit_len::<U>() >= crate::bitfield::bit_len::<T>() {
            Index::<U>(self.0, PhantomData)
        } else {
            Index::<U>::MAX
        }
    }

    /// Attempted conversion between `BifieldIndex`es.
    ///
    /// # Errors
    /// `U::BIT_SIZE` is smaller, than `T::BIT_SIZE`.
    #[inline(always)]
    pub fn try_to_other<U>(self) -> ConvResult<Index<U>>
    where
        U: Bitfield,
    {
        if crate::bitfield::bit_len::<U>() >= crate::bitfield::bit_len::<T>() {
            Ok(Index::<U>(self.0, PhantomData))
        } else {
            Index::<U>::try_from(self.0).map_err(|_| {
                ConvError::new(
                    ConvTarget::Index(crate::bitfield::bit_len::<U>()),
                    ConvTarget::Index(crate::bitfield::bit_len::<T>()),
                )
            })
        }
    }

    // Range unsafe sum of `self` and `other`.
    #[inline(always)]
    pub(crate) const fn __add(&self, other: Self) -> Self {
        Self(self.0 + other.0, PhantomData)
    }

    // Range unsafe difference of `self` and `other`.
    #[inline(always)]
    pub(crate) const fn __sub(&self, other: Self) -> Self {
        Self(self.0 - other.0, PhantomData)
    }
}

impl<T> TryFrom<usize> for Index<T>
where
    T: Bitfield,
{
    type Error = ConvError;

    #[inline(always)]
    fn try_from(value: usize) -> Result<Self, Self::Error> {
        if value < crate::bitfield::bit_len::<T>() {
            Ok(Self(value, PhantomData))
        } else {
            Err(ConvError::new(
                ConvTarget::Raw(value),
                ConvTarget::Index(crate::bitfield::bit_len::<T>()),
            ))
        }
    }
}

impl<T> From<Index<T>> for usize
where
    T: Bitfield,
{
    #[inline(always)]
    fn from(value: Index<T>) -> Self {
        value.0
    }
}

impl<T> Clone for Index<T>
where
    T: Bitfield,
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Index<T> where T: Bitfield {}

impl<T> PartialOrd for Index<T>
where
    T: Bitfield,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for Index<T>
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

impl<T> PartialEq for Index<T>
where
    T: Bitfield,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}

impl<T> Eq for Index<T> where T: Bitfield {}

impl<T> Debug for Index<T>
where
    T: Bitfield,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Index<Bitfield{}>({})",
            crate::bitfield::bit_len::<T>(),
            self.0
        )
    }
}

impl<T> Hash for Index<T>
where
    T: Bitfield,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
