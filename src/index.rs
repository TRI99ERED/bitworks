use crate::prelude::Bitfield;
use std::marker::PhantomData;

#[derive(Clone, Copy, PartialEq, Eq, Debug, PartialOrd, Ord, Hash)]
pub struct BitfieldIndex<T: Bitfield>(usize, PhantomData<T>);

impl<T> BitfieldIndex<T>
where
    T: Bitfield,
{
    pub const ONE: Self = Self(1, PhantomData);
    pub const MIN: Self = Self(0, PhantomData);
    pub const MAX: Self = Self(T::BITS - 1, PhantomData);

    #[inline(always)]
    pub fn value(&self) -> usize {
        self.0
    }

    #[inline(always)]
    pub fn checked_add(&self, other: Self) -> Option<Self> {
        self.0
            .checked_add(other.0)
            .filter(|&i| i < T::BITS)
            .map(|i| Self(i, PhantomData))
    }

    #[inline(always)]
    pub fn checked_sub(&self, other: Self) -> Option<Self> {
        self.0.checked_sub(other.0).map(|i| Self(i, PhantomData))
    }

    #[inline(always)]
    pub fn saturating_add(&self, other: Self) -> Self {
        self.checked_add(other).unwrap_or(Self::MAX)
    }

    #[inline(always)]
    pub fn saturating_sub(&self, other: Self) -> Self {
        self.checked_sub(other).unwrap_or(Self::MIN)
    }

    #[inline(always)]
    pub(crate) fn __add(&self, other: Self) -> Self {
        Self(self.0 + other.0, PhantomData)
    }

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
