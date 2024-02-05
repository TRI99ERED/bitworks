use crate::{bitfield::Bitfield, prelude::BitfieldIndex};
use std::{
    fmt::Debug,
    ops::{Deref, DerefMut},
};

/// Smart pointer granting immutable access to a bit in [`Bitfield`].
#[derive(PartialEq, Eq)]
pub struct BitRef<'a, T: Bitfield + 'a>(
    pub(crate) bool,
    pub(crate) BitfieldIndex<T>,
    pub(crate) &'a T,
);

impl<'a, T: 'a> BitRef<'a, T>
where
    T: Bitfield,
    Self: 'a,
{
    /// Returns index of the bit, referenced by `BitRef`.
    pub fn index(&'a self) -> BitfieldIndex<T> {
        self.1
    }
}

impl<'a, T: 'a> Deref for BitRef<'a, T>
where
    T: Bitfield,
    Self: 'a,
{
    type Target = bool;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a, T: 'a> AsRef<bool> for BitRef<'a, T>
where
    T: Bitfield,
    Self: 'a,
{
    fn as_ref(&self) -> &bool {
        &self.0
    }
}

impl<'a, T: 'a> Clone for BitRef<'a, T>
where
    T: Bitfield,
    Self: 'a,
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T: 'a> Copy for BitRef<'a, T> where T: Bitfield {}

impl<'a, T: 'a> Debug for BitRef<'a, T>
where
    T: Bitfield,
    Self: 'a,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("BitRef")
            .field(&self.0)
            .field(&self.1)
            .finish()
    }
}

/// Smart pointer granting mutable access to a bit in [`Bitfield`].
#[derive(PartialEq, Eq)]
pub struct BitMut<'a, T: Bitfield + 'a>(
    pub(crate) bool,
    pub(crate) BitfieldIndex<T>,
    pub(crate) &'a mut T,
);

impl<'a, T: 'a> BitMut<'a, T>
where
    T: Bitfield,
    Self: 'a,
{
    /// Returns index of the bit, referenced by `BitMut`.
    pub fn index(&'a self) -> BitfieldIndex<T> {
        self.1
    }
}

impl<'a, T: 'a> Drop for BitMut<'a, T>
where
    T: Bitfield,
    Self: 'a,
{
    fn drop(&mut self) {
        self.2.set_bit(self.1, self.0);
    }
}

impl<'a, T: 'a> Deref for BitMut<'a, T>
where
    T: Bitfield,
    Self: 'a,
{
    type Target = bool;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a, T: 'a> DerefMut for BitMut<'a, T>
where
    T: Bitfield,
    Self: 'a,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a, T: 'a> AsRef<bool> for BitMut<'a, T>
where
    T: Bitfield,
    Self: 'a,
{
    fn as_ref(&self) -> &bool {
        &self.0
    }
}

impl<'a, T: 'a> AsMut<bool> for BitMut<'a, T>
where
    T: Bitfield,
    Self: 'a,
{
    fn as_mut(&mut self) -> &mut bool {
        &mut self.0
    }
}

impl<'a, T: 'a> Debug for BitMut<'a, T>
where
    T: Bitfield,
    Self: 'a,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("BitMut")
            .field(&self.0)
            .field(&self.1)
            .finish()
    }
}
