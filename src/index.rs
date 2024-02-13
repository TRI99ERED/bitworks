//! Module containing [`Index`].

use crate::{
    bitset,
    error::{ConvError, ConvResult, ConvTarget},
    prelude::Bitset,
};
use std::{cmp::Ordering, fmt::Debug, hash::Hash, marker::PhantomData};

/// Struct allowing to safely index `T`, where `T` implements [`Bitset`].
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
    /// use bitworks::prelude::{Bitset8, Index, Index8};
    ///
    /// let index = Index8::from_usize(7);
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
    /// use bitworks::prelude::{Bitset8, Index, Index8};
    ///
    /// let index = Index8::try_from_usize(7)?;
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
    /// use bitworks::prelude::{Bitset8, Index, Index8};
    ///
    /// let index = Index8::MAX;
    /// assert_eq!(index.into_inner(), 7);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub const fn into_inner(&self) -> usize {
        self.0
    }

    /// Returns [`Some`] `Index`, that is the sum of `self` and `other`, or [`None`] on overflow.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Index, Index8};
    ///
    /// let a = Index8::ONE;
    /// let b = Index8::ONE;
    /// let c = a.checked_add(b);
    /// assert_eq!(c.unwrap().into_inner(), 2);
    ///
    /// let d = Index8::MAX;
    /// let e = Index8::ONE;
    /// let f = d.checked_add(e);
    /// assert_eq!(f, None);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub const fn checked_add(&self, other: Self) -> Option<Self> {
        match self.0.checked_add(other.0) {
            Some(i) if i < crate::bitset::bit_len::<T>() => Some(Self(i, PhantomData)),
            _ => None,
        }
    }

    /// Returns [`Some`] `Index`, that is the difference of `self` and `other`, or [`None`] on overflow.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Index, Index8};
    ///
    /// let a = Index8::MAX;
    /// let b = Index8::ONE;
    /// let c = a.checked_sub(b);
    /// assert_eq!(c.unwrap().into_inner(), 6);
    ///
    /// let d = Index8::MIN;
    /// let e = Index8::ONE;
    /// let f = d.checked_sub(e);
    /// assert_eq!(f, None);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub const fn checked_sub(&self, other: Self) -> Option<Self> {
        match self.0.checked_sub(other.0) {
            Some(i) => Some(Self(i, PhantomData)),
            _ => None,
        }
    }

    /// Returns `Index`, that is sum of `self` and `other`,
    /// or [`Index::<T>::MAX`] on overflow.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Index, Index8};
    ///
    /// let a = Index8::ONE;
    /// let b = Index8::ONE;
    /// let c = a.saturating_add(b);
    /// assert_eq!(c.into_inner(), 2);
    ///
    /// let d = Index8::MAX;
    /// let e = Index8::ONE;
    /// let f = d.saturating_add(e);
    /// assert_eq!(f.into_inner(), 7);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub const fn saturating_add(&self, other: Self) -> Self {
        match self.checked_add(other) {
            Some(i) => i,
            _ => Self::MAX,
        }
    }

    /// Returns `Index`, that is difference of `self` and `other`,
    /// or [`Index::<T>::MIN`] on overflow.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Index, Index8};
    ///
    /// let a = Index8::MAX;
    /// let b = Index8::ONE;
    /// let c = a.saturating_sub(b);
    /// assert_eq!(c.into_inner(), 6);
    ///
    /// let d = Index8::MIN;
    /// let e = Index8::ONE;
    /// let f = d.saturating_sub(e);
    /// assert_eq!(f.into_inner(), 0);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub const fn saturating_sub(&self, other: Self) -> Self {
        match self.checked_sub(other) {
            Some(i) => i,
            _ => Self::MIN,
        }
    }

    /// Conversion between indeces.
    ///
    /// # Panics
    /// Panics if `U::BIT_SIZE` is smaller, than `T::BIT_SIZE`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Bitset16, Index, Index8, Index16};
    ///
    /// let a16 = Index16::from_usize(7);
    /// let b16 = Index16::from_usize(8);
    ///
    /// let a8: Index8 = a16.to_other();
    /// assert_eq!(a8.into_inner(), 7);
    ///
    /// // The following will panic!
    /// // let b8: Index8 = b16.to_other();
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn to_other<U>(self) -> Index<U>
    where
        U: Bitset,
    {
        if Index::<U>::MAX.into_inner() >= self.into_inner() {
            Index::<U>(self.0, PhantomData)
        } else {
            panic!(
                "overflow on conversion from Index (value: {}, max: {}) to Index (max: {})",
                self.into_inner(),
                bitset::bit_len::<T>() - 1,
                bitset::bit_len::<U>() - 1
            )
        }
    }

    /// Conversion between indeces, with saturation on overflow.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Bitset16, Index, Index8, Index16};
    ///
    /// let a16 = Index16::from_usize(7);
    /// let b16 = Index16::from_usize(8);
    ///
    /// let a8: Index8 = a16.to_other_saturating();
    /// assert_eq!(a8.into_inner(), 7);
    ///
    /// let b8: Index8 = b16.to_other_saturating();
    /// assert_eq!(b8.into_inner(), 7);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn to_other_saturating<U>(self) -> Index<U>
    where
        U: Bitset,
    {
        if Index::<U>::MAX.into_inner() >= self.into_inner() {
            Index::<U>(self.0, PhantomData)
        } else {
            Index::<U>::MAX
        }
    }

    /// Attempted conversion between `BisetIndex`es.
    ///
    /// # Errors
    /// `U::BIT_SIZE` is smaller, than `T::BIT_SIZE`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Bitset16, Index, Index8, Index16};
    ///
    /// let a16 = Index16::from_usize(7);
    /// let b16 = Index16::from_usize(8);
    ///
    /// let a8 = a16.try_to_other::<Bitset8>();
    /// assert_eq!(a8.ok(), Some(Index8::from_usize(7)));
    ///
    /// let b8 = b16.try_to_other::<Bitset8>();
    /// assert_eq!(b8.ok(), None);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn try_to_other<U>(self) -> ConvResult<Index<U>>
    where
        U: Bitset,
    {
        if Index::<U>::MAX.into_inner() >= self.into_inner() {
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

    /// Returns index of byte, where the given index falls into.
    ///
    /// This function is useful in cases, where you are working with `Bitset`
    /// as with an array of bytes. As `Index` is always valid, this function will
    /// return a valid index of the byte in the `Bitset`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Bitset16, Index, Index16};
    ///
    /// let a = Index16::from_usize(7);
    /// let b = Index16::from_usize(8);
    ///
    /// assert_eq!(a.byte_index(), 0); // 7 / 8 = 0
    /// assert_eq!(b.byte_index(), 1); // 8 / 8 = 1
    /// #   Ok(())
    /// # }
    /// ```
    pub const fn byte_index(self) -> usize {
        self.into_inner() / 8
    }

    /// Returns index of bit within it's byte.
    ///
    /// This function is useful in cases, where you are working with `Bitset`
    /// as with an array of bytes. As `Index` is always valid, this function will
    /// return a valid index of the bit in it's byte in the `Bitset`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Bitset16, Index, Index16};
    ///
    /// let a = Index16::from_usize(7);
    /// let b = Index16::from_usize(8);
    ///
    /// assert_eq!(a.bit_index(), 7); // 7 % 8 = 7
    /// assert_eq!(b.bit_index(), 0); // 8 % 8 = 0
    /// #   Ok(())
    /// # }
    /// ```
    pub const fn bit_index(self) -> usize {
        self.into_inner() % 8
    }

    /// Returns a bitmask, with only given index bit set within it's byte.
    ///
    /// This function is useful in cases, where you are working with `Bitset`
    /// as with an array of bytes. As `Index` is always valid, this function will
    /// return a valid bitmask. This function is defined as (1 << [`Index::bit_index`]).
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset8, Bitset16, Index, Index16};
    ///
    /// let a = Index16::from_usize(7);
    /// let b = Index16::from_usize(8);
    ///
    /// assert_eq!(a.bitmask(), 0b10000000); // 1 << 7
    /// assert_eq!(b.bitmask(), 0b00000001); // 1 << 0
    /// #   Ok(())
    /// # }
    /// ```
    pub const fn bitmask(self) -> u8 {
        1 << self.bit_index()
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
