use crate::{
    bitfield::Bitfield,
    error::{BitfieldError, ConvTarget},
    iter::BitIter,
    prelude::{Bitfield128, Bitfield16, Bitfield64, Bitfield8, BitfieldIndex},
};
use std::{
    fmt::Display,
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
        ShrAssign,
    },
};

type Inner = u32;
const BITS: usize = 32;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Bitfield32(Inner);

impl Bitfield32 {
    #[inline(always)]
    pub fn value(&self) -> Inner {
        self.0
    }
}

impl Bitfield for Bitfield32 {
    const ONE: Self = Self(1);
    const EMPTY: Self = Self(Inner::MIN);
    const ALL: Self = Self(Inner::MAX);
    const BITS: usize = BITS;

    #[inline(always)]
    fn count_set(&self) -> usize {
        self.0.count_ones() as usize
    }

    #[inline(always)]
    fn count_unset(&self) -> usize {
        self.0.count_zeros() as usize
    }
}

impl From<Inner> for Bitfield32 {
    #[inline(always)]
    fn from(value: Inner) -> Self {
        Self(value)
    }
}

impl From<Bitfield32> for Inner {
    #[inline(always)]
    fn from(value: Bitfield32) -> Self {
        value.0
    }
}

impl From<BitfieldIndex<Bitfield32>> for Bitfield32 {
    fn from(value: BitfieldIndex<Bitfield32>) -> Self {
        Self::ONE << value
    }
}

impl BitAnd for Bitfield32 {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl BitAndAssign for Bitfield32 {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0
    }
}

impl BitOr for Bitfield32 {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for Bitfield32 {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0
    }
}

impl BitXor for Bitfield32 {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self::Output {
        Self(self.0 ^ rhs.0)
    }
}

impl BitXorAssign for Bitfield32 {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0
    }
}

impl Not for Bitfield32 {
    type Output = Self;

    #[inline(always)]
    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

impl Shl<BitfieldIndex<Self>> for Bitfield32 {
    type Output = Self;

    #[inline(always)]
    fn shl(self, rhs: BitfieldIndex<Self>) -> Self::Output {
        Self::from(self.0.shl(rhs.value()))
    }
}

impl ShlAssign<BitfieldIndex<Self>> for Bitfield32 {
    #[inline(always)]
    fn shl_assign(&mut self, rhs: BitfieldIndex<Self>) {
        *self = self.shl(rhs)
    }
}

impl Shr<BitfieldIndex<Self>> for Bitfield32 {
    type Output = Self;

    #[inline(always)]
    fn shr(self, rhs: BitfieldIndex<Self>) -> Self::Output {
        Self::from(self.0.shr(rhs.value()))
    }
}

impl ShrAssign<BitfieldIndex<Self>> for Bitfield32 {
    #[inline(always)]
    fn shr_assign(&mut self, rhs: BitfieldIndex<Self>) {
        *self = self.shr(rhs)
    }
}

impl Display for Bitfield32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#034b}", self.0)
    }
}

impl IntoIterator for Bitfield32 {
    type Item = bool;

    type IntoIter = BitIter<Self>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter::new(self, BitfieldIndex::<Self>::MIN)
    }
}

impl FromIterator<bool> for Bitfield32 {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut bitfield: Self = Self::from(0);
        for (i, bit) in iter.into_iter().take(BITS).enumerate() {
            bitfield.0 |= (if bit { 1 } else { 0 }) << (i as Inner);
        }
        bitfield
    }
}

impl From<Bitfield8> for Bitfield32 {
    #[inline(always)]
    fn from(value: Bitfield8) -> Self {
        Self(value.value() as Inner)
    }
}

impl From<Bitfield16> for Bitfield32 {
    #[inline(always)]
    fn from(value: Bitfield16) -> Self {
        Self(value.value() as Inner)
    }
}

impl TryFrom<Bitfield64> for Bitfield32 {
    type Error = BitfieldError;

    #[inline(always)]
    fn try_from(value: Bitfield64) -> Result<Self, Self::Error> {
        Inner::try_from(value.value())
            .map(Self::from)
            .map_err(|_| BitfieldError::conv_error(ConvTarget::Bitfield64, ConvTarget::Bitfield32))
    }
}

impl TryFrom<Bitfield128> for Bitfield32 {
    type Error = BitfieldError;

    #[inline(always)]
    fn try_from(value: Bitfield128) -> Result<Self, Self::Error> {
        Inner::try_from(value.value())
            .map(Self::from)
            .map_err(|_| BitfieldError::conv_error(ConvTarget::Bitfield128, ConvTarget::Bitfield32))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type Tested = Bitfield32;

    #[test]
    fn construction() {
        let bitfield = Tested::new()
            .set_bit(0.try_into().unwrap(), true)
            .check_bit(1.try_into().unwrap())
            .uncheck_bit(0.try_into().unwrap());

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

        bitfield.set_bit(6.try_into().unwrap(), true);

        assert_eq!(bitfield.0, 0b11101010);
    }

    #[test]
    fn bit_set_to_false() {
        let mut bitfield: Tested = 0b10101010.into();

        bitfield.set_bit(7.try_into().unwrap(), false);

        assert_eq!(bitfield.0, 0b00101010);
    }

    #[test]
    fn get_bit() {
        let bitfield: Tested = 0b10101010.into();

        assert_eq!(bitfield.get_bit(0.try_into().unwrap()), false);
        assert_eq!(bitfield.get_bit(1.try_into().unwrap()), true);
    }

    #[test]
    fn bit_check() {
        let mut bitfield: Tested = 0b10101010.into();

        bitfield.check_bit(6.try_into().unwrap());

        assert_eq!(bitfield.0, 0b11101010);
    }

    #[test]
    fn bit_uncheck() {
        let mut bitfield: Tested = 0b10101010.into();

        bitfield.uncheck_bit(7.try_into().unwrap());

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

        assert_eq!(bitfield.count_unset(), 29);
    }

    #[test]
    fn shl() {
        let bitfield: Tested = 0b00000001.into();

        assert_eq!(bitfield << 1.try_into().unwrap(), 0b00000010.into());

        let mut bitfield: Tested = 0b00000001.into();
        bitfield <<= 1.try_into().unwrap();

        assert_eq!(bitfield, 0b00000010.into());
    }

    #[test]
    fn shr() {
        let bitfield: Tested = 0b00000010.into();

        assert_eq!(bitfield >> 1.try_into().unwrap(), 0b00000001.into());

        let mut bitfield: Tested = 0b00000010.into();
        bitfield >>= 1.try_into().unwrap();

        assert_eq!(bitfield, 0b00000001.into());
    }

    #[test]
    fn not() {
        let a: Tested = Tested::EMPTY;

        assert_eq!(!a, Tested::ALL);
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
        let a: Tested = Tested::EMPTY;

        assert_eq!(a.complement(), Tested::ALL);
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

        for _ in 8..32 {
            assert_eq!(bit_iter.next(), Some(false));
        }

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
        let mut set_pos_iter = bitfield.set_index_iter();

        assert_eq!(set_pos_iter.next(), Some(4.try_into().unwrap()));
        assert_eq!(set_pos_iter.next(), Some(5.try_into().unwrap()));
        assert_eq!(set_pos_iter.next(), Some(6.try_into().unwrap()));
        assert_eq!(set_pos_iter.next(), Some(7.try_into().unwrap()));
        assert_eq!(set_pos_iter.next(), None);
    }

    #[test]
    fn unset_pos_iter() {
        let bitfield: Tested = 0b11110000.into();
        let mut unset_pos_iter = bitfield.unset_index_iter();

        assert_eq!(unset_pos_iter.next(), Some(0.try_into().unwrap()));
        assert_eq!(unset_pos_iter.next(), Some(1.try_into().unwrap()));
        assert_eq!(unset_pos_iter.next(), Some(2.try_into().unwrap()));
        assert_eq!(unset_pos_iter.next(), Some(3.try_into().unwrap()));

        for i in 8..32 {
            assert_eq!(unset_pos_iter.next(), Some(i.try_into().unwrap()));
        }

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
