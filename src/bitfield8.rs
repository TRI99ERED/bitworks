use crate::{
    bitfield::Bitfield,
    error::{BitfieldError, ConvTarget},
    flagenum::Flagenum,
    iter::BitIter,
    prelude::{Bitfield128, Bitfield16, Bitfield32, Bitfield64},
};
use std::{
    fmt::Display,
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
        ShrAssign,
    },
};

type Inner = u8;
const BITS: usize = 8;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub struct Bitfield8(Inner);

impl Bitfield8 {
    pub fn value(&self) -> Inner {
        self.0
    }
}

impl Bitfield for Bitfield8 {
    const IDENT: Self = Self(1);
    const EMPTY: Self = Self(Inner::MIN);
    const ALL: Self = Self(Inner::MAX);
    const BITS: usize = BITS;

    fn count_set(&self) -> usize {
        self.0.count_ones() as usize
    }

    fn count_unset(&self) -> usize {
        self.0.count_zeros() as usize
    }

    fn set_enum_iter<E>(&self) -> impl Iterator<Item = E>
    where
        E: Flagenum<Bitfield = Self>,
    {
        self.set_pos_iter()
            .filter_map(|i| Inner::try_from(i).ok())
            .filter_map(|i| E::try_from(Self::from(i)).ok())
    }

    fn unset_enum_iter<E>(&self) -> impl Iterator<Item = E>
    where
        E: Flagenum<Bitfield = Self>,
    {
        self.unset_pos_iter()
            .filter_map(|i| Inner::try_from(i).ok())
            .filter_map(|i| E::try_from(Self::from(i)).ok())
    }
}

impl From<Inner> for Bitfield8 {
    fn from(value: Inner) -> Self {
        Self(value)
    }
}

impl From<Bitfield8> for Inner {
    fn from(value: Bitfield8) -> Self {
        value.0
    }
}

impl BitAnd for Bitfield8 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl BitAndAssign for Bitfield8 {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0
    }
}

impl BitOr for Bitfield8 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for Bitfield8 {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0
    }
}

impl BitXor for Bitfield8 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self(self.0 ^ rhs.0)
    }
}

impl BitXorAssign for Bitfield8 {
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0
    }
}

impl Not for Bitfield8 {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

impl Shl<usize> for Bitfield8 {
    type Output = Self;

    fn shl(self, rhs: usize) -> Self::Output {
        Self::from(self.0.shl(rhs))
    }
}

impl ShlAssign<usize> for Bitfield8 {
    fn shl_assign(&mut self, rhs: usize) {
        *self = self.shl(rhs)
    }
}

impl Shr<usize> for Bitfield8 {
    type Output = Self;

    fn shr(self, rhs: usize) -> Self::Output {
        Self::from(self.0.shr(rhs))
    }
}

impl ShrAssign<usize> for Bitfield8 {
    fn shr_assign(&mut self, rhs: usize) {
        *self = self.shr(rhs)
    }
}

impl Display for Bitfield8 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#010b}", self.0)
    }
}

impl IntoIterator for Bitfield8 {
    type Item = bool;

    type IntoIter = BitIter<Inner>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            bitfield: self.0,
            index: 0,
        }
    }
}

impl FromIterator<bool> for Bitfield8 {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut bitfield: Self = Self::new();
        for (i, bit) in iter.into_iter().take(BITS).enumerate() {
            if bit {
                bitfield.0 |= 1 << (i as Inner);
            }
        }
        bitfield
    }
}

impl TryFrom<Bitfield16> for Bitfield8 {
    type Error = BitfieldError;

    fn try_from(value: Bitfield16) -> Result<Self, Self::Error> {
        Inner::try_from(value.value())
            .map(Self::from)
            .map_err(|_| BitfieldError::conv_error(ConvTarget::Bitfield16, ConvTarget::Bitfield8))
    }
}

impl TryFrom<Bitfield32> for Bitfield8 {
    type Error = BitfieldError;

    fn try_from(value: Bitfield32) -> Result<Self, Self::Error> {
        Inner::try_from(value.value())
            .map(Self::from)
            .map_err(|_| BitfieldError::conv_error(ConvTarget::Bitfield32, ConvTarget::Bitfield8))
    }
}

impl TryFrom<Bitfield64> for Bitfield8 {
    type Error = BitfieldError;

    fn try_from(value: Bitfield64) -> Result<Self, Self::Error> {
        Inner::try_from(value.value())
            .map(Self::from)
            .map_err(|_| BitfieldError::conv_error(ConvTarget::Bitfield64, ConvTarget::Bitfield8))
    }
}

impl TryFrom<Bitfield128> for Bitfield8 {
    type Error = BitfieldError;

    fn try_from(value: Bitfield128) -> Result<Self, Self::Error> {
        Inner::try_from(value.value())
            .map(Self::from)
            .map_err(|_| BitfieldError::conv_error(ConvTarget::Bitfield128, ConvTarget::Bitfield8))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type Tested = Bitfield8;

    #[test]
    fn construction() {
        let bitfield = Tested::new().set_bit(0, true).check_bit(1).uncheck_bit(0);

        assert_eq!(bitfield, 0b00000010.into());
    }

    #[test]
    fn conversion_from_integer() {
        let bitfield: Tested = 0b10101010.into();

        assert_eq!(bitfield.0, 0b10101010);
    }

    #[test]
    fn value() {
        let bitfield: Tested = 0b10101010.into();

        assert_eq!(bitfield.0, bitfield.value());
    }

    #[test]
    fn bit_set_to_true() {
        let mut bitfield: Tested = 0b10101010.into();

        bitfield.set_bit(6, true);

        assert_eq!(bitfield.0, 0b11101010);
    }

    #[test]
    fn bit_set_to_false() {
        let mut bitfield: Tested = 0b10101010.into();

        bitfield.set_bit(7, false);

        assert_eq!(bitfield.0, 0b00101010);
    }

    #[test]
    fn get_bit() {
        let bitfield: Tested = 0b10101010.into();

        assert_eq!(bitfield.get_bit(0), false);
        assert_eq!(bitfield.get_bit(1), true);
    }

    #[test]
    fn bit_check() {
        let mut bitfield: Tested = 0b10101010.into();

        bitfield.check_bit(6);

        assert_eq!(bitfield.0, 0b11101010);
    }

    #[test]
    fn bit_uncheck() {
        let mut bitfield: Tested = 0b10101010.into();

        bitfield.uncheck_bit(7);

        assert_eq!(bitfield.0, 0b00101010);
    }

    #[test]
    fn count_set() {
        let bitfield: Tested = 0b11100000.into();

        assert_eq!(bitfield.count_set(), 3);
    }

    #[test]
    fn count_unset() {
        let bitfield: Tested = 0b11100000.into();

        assert_eq!(bitfield.count_unset(), 5);
    }

    #[test]
    fn shl() {
        let bitfield: Tested = 0b00000001.into();

        assert_eq!(bitfield << 1, 0b00000010.into());

        let mut bitfield: Tested = 0b00000001.into();
        bitfield <<= 1;

        assert_eq!(bitfield, 0b00000010.into());
    }

    #[test]
    fn shr() {
        let bitfield: Tested = 0b00000010.into();

        assert_eq!(bitfield >> 1, 0b00000001.into());

        let mut bitfield: Tested = 0b00000010.into();
        bitfield >>= 1;

        assert_eq!(bitfield, 0b00000001.into());
    }

    #[test]
    fn not() {
        let a: Tested = 0b11110000.into();

        assert_eq!(!a, 0b00001111.into());
    }

    #[test]
    fn bit_and() {
        let a: Tested = 0b11110000.into();
        let b: Tested = 0b11001100.into();

        assert_eq!(a & b, 0b11000000.into());

        let mut a: Tested = 0b11110000.into();
        let b: Tested = 0b11001100.into();
        a &= b;

        assert_eq!(a, 0b11000000.into());
    }

    #[test]
    fn bit_or() {
        let a: Tested = 0b11110000.into();
        let b: Tested = 0b11001100.into();

        assert_eq!(a | b, 0b11111100.into());

        let mut a: Tested = 0b11110000.into();
        let b: Tested = 0b11001100.into();
        a |= b;

        assert_eq!(a, 0b11111100.into());
    }

    #[test]
    fn bit_xor() {
        let a: Tested = 0b11110000.into();
        let b: Tested = 0b11001100.into();

        assert_eq!(a ^ b, 0b00111100.into());

        let mut a: Tested = 0b11110000.into();
        let b: Tested = 0b11001100.into();
        a ^= b;

        assert_eq!(a, 0b00111100.into());
    }

    #[test]
    fn complement() {
        let a: Tested = 0b11110000.into();

        assert_eq!(a.complement(), 0b00001111.into());
    }

    #[test]
    fn intersection() {
        let a: Tested = 0b11110000.into();
        let b: Tested = 0b11001100.into();

        assert_eq!(a.intersection(b), 0b11000000.into());
    }

    #[test]
    fn union() {
        let a: Tested = 0b11110000.into();
        let b: Tested = 0b11001100.into();

        assert_eq!(a.union(b), 0b11111100.into());
    }

    #[test]
    fn difference() {
        let a: Tested = 0b11110000.into();
        let b: Tested = 0b11001100.into();

        assert_eq!(a.difference(b), 0b00110000.into());
    }

    #[test]
    fn sym_difference() {
        let a: Tested = 0b11110000.into();
        let b: Tested = 0b11001100.into();

        assert_eq!(a.sym_difference(b), 0b00111100.into());
    }

    #[test]
    fn bit_iter() {
        let bitfield: Tested = 0b11110000.into();
        let mut bit_iter = bitfield.bit_iter();

        assert_eq!(bit_iter.next(), Some(false));
        assert_eq!(bit_iter.next(), Some(false));
        assert_eq!(bit_iter.next(), Some(false));
        assert_eq!(bit_iter.next(), Some(false));
        assert_eq!(bit_iter.next(), Some(true));
        assert_eq!(bit_iter.next(), Some(true));
        assert_eq!(bit_iter.next(), Some(true));
        assert_eq!(bit_iter.next(), Some(true));
        assert_eq!(bit_iter.next(), None);
    }

    #[test]
    fn collect_from_bit_iter() {
        let a: Tested = 0b11110000.into();
        let bit_iter = a.bit_iter();
        let b: Tested = bit_iter.collect();

        assert_eq!(b, 0b11110000.into());

        let arr = [true, false, true, false, true, false, true, false];
        let bitfield: Tested = arr
            .into_iter()
            // Need to reverse to get the same visual representation, because
            // array's .into_iter() makes iterator from left to right,
            // but .collect() will collect from right to left here.
            .rev()
            .collect();

        assert_eq!(bitfield, 0b10101010.into());
    }

    #[test]
    fn set_pos_iter() {
        let bitfield: Tested = 0b11110000.into();
        let mut set_pos_iter = bitfield.set_pos_iter();

        assert_eq!(set_pos_iter.next(), Some(4));
        assert_eq!(set_pos_iter.next(), Some(5));
        assert_eq!(set_pos_iter.next(), Some(6));
        assert_eq!(set_pos_iter.next(), Some(7));
        assert_eq!(set_pos_iter.next(), None);
    }

    #[test]
    fn unset_pos_iter() {
        let bitfield: Tested = 0b11110000.into();
        let mut unset_pos_iter = bitfield.unset_pos_iter();

        assert_eq!(unset_pos_iter.next(), Some(0));
        assert_eq!(unset_pos_iter.next(), Some(1));
        assert_eq!(unset_pos_iter.next(), Some(2));
        assert_eq!(unset_pos_iter.next(), Some(3));
        assert_eq!(unset_pos_iter.next(), None);
    }

    #[test]
    fn from_slice() {
        // Same index order
        let slice: &[bool] = &[true, false, true, false, true, false, true, false];
        let bitfield: Tested = Tested::from_slice(slice);

        assert_eq!(bitfield, 0b01010101.into());
    }
}
