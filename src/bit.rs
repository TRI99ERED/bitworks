//! Module containing [`Bit`] enum as well as [`BitRef`] and [`BitMut`] smart pointers.

use crate::{bitset::Bitset, prelude::Index};
use std::{
    fmt::{Debug, Display},
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Deref, DerefMut, Not},
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Bit {
    Zero,
    One,
}

pub use Bit::*;

impl Not for Bit {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Zero => One,
            One => Zero,
        }
    }
}

impl BitAnd for Bit {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        if self == One && rhs == One {
            One
        } else {
            Zero
        }
    }
}

impl BitAndAssign for Bit {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = if *self == One && rhs == One {
            One
        } else {
            Zero
        }
    }
}

impl BitOr for Bit {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        if self == One || rhs == One {
            One
        } else {
            Zero
        }
    }
}

impl BitOrAssign for Bit {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = if *self == One || rhs == One {
            One
        } else {
            Zero
        }
    }
}

impl BitXor for Bit {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        if self != rhs {
            One
        } else {
            Zero
        }
    }
}

impl BitXorAssign for Bit {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = if *self != rhs { One } else { Zero }
    }
}

impl From<bool> for Bit {
    #[inline(always)]
    fn from(value: bool) -> Self {
        match value {
            true => One,
            false => Zero,
        }
    }
}

impl From<Bit> for bool {
    #[inline(always)]
    fn from(value: Bit) -> Self {
        match value {
            Zero => false,
            One => true,
        }
    }
}

impl Display for Bit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match *self {
                Zero => 0,
                One => 1,
            }
        )
    }
}

/// Smart pointer granting immutable access to a bit in [`Bitset`].
#[derive(PartialEq, Eq)]
pub struct BitRef<'a, T: Bitset + 'a>(pub(crate) Bit, pub(crate) Index<T>, pub(crate) &'a T);

impl<'a, T: 'a> BitRef<'a, T>
where
    T: Bitset,
    Self: 'a,
{
    /// Constructs a new value of `BitRef`
    pub fn new(value: Bit, index: Index<T>, owner: &'a T) -> Self {
        Self(value, index, owner)
    }

    /// Returns index of the bit, referenced by `BitRef`.
    pub fn index(bit_ref: &'a Self) -> Index<T> {
        bit_ref.1
    }
}

impl<'a, T: 'a> Deref for BitRef<'a, T>
where
    T: Bitset,
    Self: 'a,
{
    type Target = Bit;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a, T: 'a> AsRef<Bit> for BitRef<'a, T>
where
    T: Bitset,
    Self: 'a,
{
    fn as_ref(&self) -> &Bit {
        &self.0
    }
}

impl<'a, T: 'a> Clone for BitRef<'a, T>
where
    T: Bitset,
    Self: 'a,
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T: 'a> Copy for BitRef<'a, T> where T: Bitset {}

impl<'a, T: 'a> Debug for BitRef<'a, T>
where
    T: Bitset,
    Self: 'a,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("BitRef").field(&self.0).field(&self.1).finish()
    }
}

impl<'a, T: 'a> Display for BitRef<'a, T>
where
    T: Bitset,
    Self: 'a,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self.0 {
                Zero => 0,
                One => 1,
            }
        )
    }
}

/// Smart pointer granting mutable access to a bit in [`Bitset`].
#[derive(PartialEq, Eq)]
pub struct BitMut<'a, T: Bitset + 'a>(pub(crate) Bit, pub(crate) Index<T>, pub(crate) &'a mut T);

impl<'a, T: 'a> BitMut<'a, T>
where
    T: Bitset,
    Self: 'a,
{
    /// Constructs a new value of `BitMut`
    pub fn new(value: Bit, index: Index<T>, owner: &'a mut T) -> Self {
        Self(value, index, owner)
    }

    /// Returns index of the bit, referenced by `BitMut`.
    pub fn index(bit_mut: &'a Self) -> Index<T> {
        bit_mut.1
    }
}

impl<'a, T: 'a> Drop for BitMut<'a, T>
where
    T: Bitset,
    Self: 'a,
{
    fn drop(&mut self) {
        self.2.set_bit(self.1, self.0);
    }
}

impl<'a, T: 'a> Deref for BitMut<'a, T>
where
    T: Bitset,
    Self: 'a,
{
    type Target = Bit;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a, T: 'a> DerefMut for BitMut<'a, T>
where
    T: Bitset,
    Self: 'a,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a, T: 'a> AsRef<Bit> for BitMut<'a, T>
where
    T: Bitset,
    Self: 'a,
{
    fn as_ref(&self) -> &Bit {
        &self.0
    }
}

impl<'a, T: 'a> AsMut<Bit> for BitMut<'a, T>
where
    T: Bitset,
    Self: 'a,
{
    fn as_mut(&mut self) -> &mut Bit {
        &mut self.0
    }
}

impl<'a, T: 'a> Debug for BitMut<'a, T>
where
    T: Bitset,
    Self: 'a,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("BitMut").field(&self.0).field(&self.1).finish()
    }
}

impl<'a, T: 'a> Display for BitMut<'a, T>
where
    T: Bitset,
    Self: 'a,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self.0 {
                Zero => 0,
                One => 1,
            }
        )
    }
}
