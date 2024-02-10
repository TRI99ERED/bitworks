//! Module containing [`Index`].

use crate::{
    bitset,
    error::{ConvError, ConvResult, ConvTarget},
    prelude::Bitset,
};
use std::{cmp::Ordering, fmt::Debug, hash::Hash, marker::PhantomData};

/// Struct meant to safely index the `T`, where `T` implements [`Bitset`].
#[derive(Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Index<T: Bitset>(pub(crate) usize, pub(crate) PhantomData<T>);

impl<T> Index<T>
where
    T: Bitset,
{
    /// Value of 1 for `Index`.<br/>
    /// Shortcut from having to use `Index::<T>::from_usize(1)`
    pub const ONE: Self = Self(1, PhantomData);

    /// Minimum value for `Index`.<br/>
    /// Shortcut from having to use `Index::<T>::from_usize(usize::MIN)`
    pub const MIN: Self = Self(0, PhantomData);

    /// Maximum value for `Index`.<br/>
    /// Shortcut from having to use `Index::<T>::from_usize(T::BITS - 1)`
    pub const MAX: Self = Self(bitset::bit_len::<T>() - 1, PhantomData);

    /// Constructs a valid `Index<T>` value from usize.
    ///
    /// Only use this, if you're certain, that resulting index will be valid.<br/>
    /// Valid inputs to this function are in range `0..(T::BYTE_SIZE * 8)`.
    /// This function exists solely to avoid situations, where you are certain of
    /// the validity and don't want to write:<br/>
    /// `Index::<T>::try_from_usize(value).expect("value should be in range")`
    ///
    /// # Panics
    /// This function panics, if the `value` supplied is outside the range `0..(T::BYTE_SIZE * 8)`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Index};
    ///
    /// let index = Index::<Bitset8>::from_usize(7);
    /// assert_eq!(index.into_inner(), 7);
    /// #   Ok(())
    /// # }
    /// ```
    pub const fn from_usize(value: usize) -> Self {
        if value < bitset::bit_len::<T>() {
            Self(value, PhantomData)
        } else {
            panic!("value was out of range 0..(T::BYTE_SIZE * 8)",)
        }
    }

    /// Tries constructing an `Index<T>` value from usize.
    ///
    /// Meant to be used in situations, where you're uncertain, if the `value` supplied would make
    /// a valid `Index<T>` value.
    ///
    /// # Errors
    /// This function errors, if the `value` supplied is outside the range `0..(T::BYTE_SIZE * 8)`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Index};
    ///
    /// let index = Index::<Bitset8>::try_from_usize(7)?;
    /// assert_eq!(index.into_inner(), 7);
    /// #   Ok(())
    /// # }
    /// ```
    pub const fn try_from_usize(value: usize) -> ConvResult<Self> {
        if value < bitset::bit_len::<T>() {
            Ok(Self(value, PhantomData))
        } else {
            Err(ConvError::new(
                ConvTarget::Raw(value),
                ConvTarget::Index(bitset::bit_len::<T>()),
            ))
        }
    }

    /// Returns value of `Index` as [`usize`].
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Index};
    ///
    /// let index = Index::<Bitset8>::MAX;
    /// assert_eq!(index.into_inner(), 7);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub const fn into_inner(&self) -> usize {
        self.0
    }

    /// Returns [`Some`] `Index`, that is sum of `self` and `other`, or [`None`] on overflow.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Index};
    ///
    /// let a = Index::<Bitset8>::ONE;
    /// let b = Index::<Bitset8>::ONE;
    /// let c = a.checked_add(b);
    /// assert_eq!(c.unwrap().into_inner(), 2);
    ///
    /// let d = Index::<Bitset8>::MAX;
    /// let e = Index::<Bitset8>::ONE;
    /// let f = d.checked_add(e);
    /// assert_eq!(f, None);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn checked_add(&self, other: Self) -> Option<Self> {
        self.0
            .checked_add(other.0)
            .filter(|&i| i < crate::bitset::bit_len::<T>())
            .map(|i| Self(i, PhantomData))
    }

    /// Returns [`Some`] `Index`, that is difference of `self` and `other`, or [`None`] on overflow.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Index};
    ///
    /// let a = Index::<Bitset8>::MAX;
    /// let b = Index::<Bitset8>::ONE;
    /// let c = a.checked_sub(b);
    /// assert_eq!(c.unwrap().into_inner(), 6);
    ///
    /// let d = Index::<Bitset8>::MIN;
    /// let e = Index::<Bitset8>::ONE;
    /// let f = d.checked_sub(e);
    /// assert_eq!(f, None);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn checked_sub(&self, other: Self) -> Option<Self> {
        self.0.checked_sub(other.0).map(|i| Self(i, PhantomData))
    }

    /// Returns `Index`, that is sum of `self` and `other`,
    /// or [`Index::<T>::MAX`] on overflow.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Index};
    ///
    /// let a = Index::<Bitset8>::ONE;
    /// let b = Index::<Bitset8>::ONE;
    /// let c = a.saturating_add(b);
    /// assert_eq!(c.into_inner(), 2);
    ///
    /// let d = Index::<Bitset8>::MAX;
    /// let e = Index::<Bitset8>::ONE;
    /// let f = d.saturating_add(e);
    /// assert_eq!(f.into_inner(), 7);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn saturating_add(&self, other: Self) -> Self {
        self.checked_add(other).unwrap_or(Self::MAX)
    }

    /// Returns `Index`, that is difference of `self` and `other`,
    /// or [`Index::<T>::MIN`] on overflow.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Index};
    ///
    /// let a = Index::<Bitset8>::MAX;
    /// let b = Index::<Bitset8>::ONE;
    /// let c = a.saturating_sub(b);
    /// assert_eq!(c.into_inner(), 6);
    ///
    /// let d = Index::<Bitset8>::MIN;
    /// let e = Index::<Bitset8>::ONE;
    /// let f = d.saturating_sub(e);
    /// assert_eq!(f.into_inner(), 0);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn saturating_sub(&self, other: Self) -> Self {
        self.checked_sub(other).unwrap_or(Self::MIN)
    }

    /// Saturating conversion between `BisetIndex`es.
    #[inline(always)]
    pub const fn to_other<U>(self) -> Index<U>
    where
        U: Bitset,
    {
        if crate::bitset::bit_len::<U>() >= crate::bitset::bit_len::<T>() {
            Index::<U>(self.0, PhantomData)
        } else {
            Index::<U>::MAX
        }
    }

    /// Attempted conversion between `BisetIndex`es.
    ///
    /// # Errors
    /// `U::BIT_SIZE` is smaller, than `T::BIT_SIZE`.
    #[inline(always)]
    pub fn try_to_other<U>(self) -> ConvResult<Index<U>>
    where
        U: Bitset,
    {
        if crate::bitset::bit_len::<U>() >= crate::bitset::bit_len::<T>() {
            Ok(Index::<U>(self.0, PhantomData))
        } else {
            Index::<U>::try_from(self.0).map_err(|_| {
                ConvError::new(
                    ConvTarget::Index(bitset::bit_len::<U>()),
                    ConvTarget::Index(bitset::bit_len::<T>()),
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
    T: Bitset,
{
    type Error = ConvError;

    #[inline(always)]
    fn try_from(value: usize) -> Result<Self, Self::Error> {
        Self::try_from_usize(value)
    }
}

impl<T> From<Index<T>> for usize
where
    T: Bitset,
{
    #[inline(always)]
    fn from(value: Index<T>) -> Self {
        value.0
    }
}

impl<T> Clone for Index<T>
where
    T: Bitset,
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Index<T> where T: Bitset {}

impl<T> PartialOrd for Index<T>
where
    T: Bitset,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for Index<T>
where
    T: Bitset,
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
    T: Bitset,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}

impl<T> Eq for Index<T> where T: Bitset {}

impl<T> Debug for Index<T>
where
    T: Bitset,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Index<Bitset{}>({})",
            crate::bitset::bit_len::<T>(),
            self.0
        )
    }
}

impl<T> Hash for Index<T>
where
    T: Bitset,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
