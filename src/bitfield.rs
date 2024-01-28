use std::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
    ShrAssign,
};

use crate::private::{BitfieldHelper, BitfieldMarker};

pub trait Bitfield<T>:
    Sized
    + BitfieldMarker
    + BitfieldHelper<T>
    + Default
    + Copy
    + Clone
    + From<T>
    + Into<T>
    + BitAnd<Output = Self>
    + BitAndAssign
    + BitOr<Output = Self>
    + BitOrAssign
    + BitXor<Output = Self>
    + BitXorAssign
    + Not<Output = Self>
where
    T: Sized
        + Copy
        + Clone
        + Not<Output = T>
        + PartialEq
        + Eq
        + BitAnd<T, Output = T>
        + BitAndAssign<T>
        + BitOr<T, Output = T>
        + BitOrAssign<T>
        + BitXor<T, Output = T>
        + BitXorAssign<T>
        + Shl<usize, Output = T>
        + Shl<T, Output = T>
        + ShlAssign<T>
        + Shr<usize, Output = T>
        + Shr<T, Output = T>
        + ShrAssign<T>
        + TryFrom<usize>,
{
    fn new() -> Self {
        Self::default()
    }

    fn build(&mut self) -> Self {
        *self
    }

    fn set_flag(&mut self, pos: usize, flag: bool) -> &mut Self {
        if flag {
            *self |= (Self::BIT << pos).into();
        } else {
            *self &= (!(Self::BIT << pos)).into();
        }
        self
    }

    fn get_flag(&self, pos: usize) -> bool {
        let bit = Self::BIT << pos;
        (<Self as Into<T>>::into(*self) & bit) != Self::EMPTY
    }

    fn check_flag(&mut self, pos: usize) -> &mut Self {
        *self |= (Self::BIT << pos).into();
        self
    }

    fn uncheck_flag(&mut self, pos: usize) -> &mut Self {
        *self &= (!(Self::BIT << pos)).into();
        self
    }

    fn complement(self) -> Self {
        !self
    }

    fn union(self, other: Self) -> Self {
        self | other
    }

    fn intersection(self, other: Self) -> Self {
        self & other
    }

    fn difference(self, other: Self) -> Self {
        self & !other
    }

    fn sym_difference(self, other: Self) -> Self {
        self.difference(other) | other.difference(self)
    }
}
