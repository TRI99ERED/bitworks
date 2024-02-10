//! Module containing [`Bitfield16`].

use crate::{
    bit::Bit,
    bitfield::{Bitfield, LeftAligned},
    error::{ConvError, ConvTarget},
    prelude::{Bitfield128, Bitfield32, Bitfield64, Bitfield8, ByteField, Index},
};
use std::{
    fmt::{Binary, Debug, Display, LowerHex, Octal, UpperHex},
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
        ShrAssign,
    },
};

type Inner = u16;
type BIndex = Index<Bitfield16>;
const BITS: usize = 16;

/// [`Bitfield`] of size 16.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
pub struct Bitfield16(pub(crate) Inner);

impl Bitfield16 {
    /// Returns the inner representation of `Bitfield16`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::Bitfield16;
    ///
    /// let bitfield = Bitfield16::from(19);
    /// let inner: u16 = bitfield.into_inner();
    ///
    /// assert_eq!(inner, 19);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub const fn into_inner(&self) -> Inner {
        self.0
    }
}

unsafe impl LeftAligned for Bitfield16 {
    type _Repr = Inner;
    const _BYTE_SIZE: usize = 2;
    const _ONE: Self = Self(1);
    const _ALL: Self = Self(Inner::MAX);
    const _NONE: Self = Self(Inner::MIN);

    #[inline(always)]
    fn _new(value: Self::Repr) -> Self {
        Self(value)
    }
}

impl From<Inner> for Bitfield16 {
    #[inline(always)]
    fn from(value: Inner) -> Self {
        Self(value)
    }
}

impl From<Bitfield16> for Inner {
    #[inline(always)]
    fn from(value: Bitfield16) -> Self {
        value.0
    }
}

impl From<BIndex> for Bitfield16 {
    #[inline(always)]
    fn from(value: BIndex) -> Self {
        Self(1) << value
    }
}

impl From<ByteField<2>> for Bitfield16 {
    #[inline(always)]
    fn from(value: ByteField<2>) -> Self {
        unsafe { std::mem::transmute_copy(&value) }
    }
}

impl From<Bitfield8> for Bitfield16 {
    #[inline(always)]
    fn from(value: Bitfield8) -> Self {
        Self(value.into_inner() as Inner)
    }
}

impl TryFrom<Bitfield32> for Bitfield16 {
    type Error = ConvError;

    #[inline(always)]
    fn try_from(value: Bitfield32) -> Result<Self, Self::Error> {
        Inner::try_from(value.into_inner())
            .map(Self::from)
            .map_err(|_| ConvError::new(ConvTarget::Field(32), ConvTarget::Field(16)))
    }
}

impl TryFrom<Bitfield64> for Bitfield16 {
    type Error = ConvError;

    #[inline(always)]
    fn try_from(value: Bitfield64) -> Result<Self, Self::Error> {
        Inner::try_from(value.into_inner())
            .map(Self::from)
            .map_err(|_| ConvError::new(ConvTarget::Field(64), ConvTarget::Field(16)))
    }
}

impl TryFrom<Bitfield128> for Bitfield16 {
    type Error = ConvError;

    #[inline(always)]
    fn try_from(value: Bitfield128) -> Result<Self, Self::Error> {
        Inner::try_from(value.into_inner())
            .map(Self::from)
            .map_err(|_| ConvError::new(ConvTarget::Field(128), ConvTarget::Field(16)))
    }
}

impl Not for Bitfield16 {
    type Output = Self;

    #[inline(always)]
    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

impl BitAnd for Bitfield16 {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl BitAndAssign for Bitfield16 {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}

impl BitOr for Bitfield16 {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for Bitfield16 {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl BitXor for Bitfield16 {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self::Output {
        Self(self.0 ^ rhs.0)
    }
}

impl BitXorAssign for Bitfield16 {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0;
    }
}

impl Shl<BIndex> for Bitfield16 {
    type Output = Self;

    #[inline(always)]
    fn shl(self, rhs: BIndex) -> Self::Output {
        Self::from(self.0.shl(rhs.into_inner()))
    }
}

impl ShlAssign<BIndex> for Bitfield16 {
    #[inline(always)]
    fn shl_assign(&mut self, rhs: BIndex) {
        *self = self.shl(rhs);
    }
}

impl Shr<BIndex> for Bitfield16 {
    type Output = Self;

    #[inline(always)]
    fn shr(self, rhs: BIndex) -> Self::Output {
        Self::from(self.0.shr(rhs.into_inner()))
    }
}

impl ShrAssign<BIndex> for Bitfield16 {
    #[inline(always)]
    fn shr_assign(&mut self, rhs: BIndex) {
        *self = self.shr(rhs);
    }
}

impl BitAnd<BIndex> for Bitfield16 {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: BIndex) -> Self::Output {
        Self(self.0 & Self::from(rhs).0)
    }
}

impl BitAndAssign<BIndex> for Bitfield16 {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: BIndex) {
        self.0 &= Self::from(rhs).0;
    }
}

impl BitOr<BIndex> for Bitfield16 {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: BIndex) -> Self::Output {
        Self(self.0 | Self::from(rhs).0)
    }
}

impl BitOrAssign<BIndex> for Bitfield16 {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: BIndex) {
        self.0 |= Self::from(rhs).0;
    }
}

impl BitXor<BIndex> for Bitfield16 {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: BIndex) -> Self::Output {
        Self(self.0 ^ Self::from(rhs).0)
    }
}

impl BitXorAssign<BIndex> for Bitfield16 {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: BIndex) {
        self.0 ^= Self::from(rhs).0;
    }
}

impl FromIterator<Bit> for Bitfield16 {
    fn from_iter<T: IntoIterator<Item = Bit>>(iter: T) -> Self {
        iter.into_iter()
            .take(BITS)
            .enumerate()
            .filter_map(|(i, bit)| if bool::from(bit) { Some(i) } else { None })
            .filter_map(|i| BIndex::try_from(i).ok())
            .fold(Self::NONE, |acc, i| acc | Self(1) << i)
    }
}

impl Debug for Bitfield16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bitfield16({:#018b})", self.0)
    }
}

impl Display for Bitfield16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:016b}", self.0)
    }
}

impl Binary for Bitfield16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#018b}", self.0)
    }
}

impl Octal for Bitfield16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#08o}", self.0)
    }
}

impl UpperHex for Bitfield16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#06X}", self.0)
    }
}

impl LowerHex for Bitfield16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#06x}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use crate::{bit::Bit::*, prelude::Bitfield};

    use super::*;
    type Tested = Bitfield16;
    type TestResult = Result<(), Box<dyn Error>>;

    #[test]
    fn construction() -> TestResult {
        let bitfield = Tested::NONE
            .clone()
            .set_bit(0.try_into()?, One)
            .check_bit(1.try_into()?)
            .uncheck_bit(0.try_into()?)
            .build();

        assert_eq!(bitfield, 0b00000010.into());
        Ok(())
    }

    #[test]
    fn conversion_from_integer() {
        let bitfield: Tested = 0b10101010.into();

        assert_eq!(bitfield.0, 0b10101010);
    }

    #[test]
    fn conversion_from_index() {
        let bitfield = Tested::from(Index::<Tested>::MIN);

        assert_eq!(bitfield.0, 1);
    }

    #[test]
    fn into_inner() {
        let bitfield: Tested = 0b10101010.into();

        assert_eq!(bitfield.0, bitfield.into_inner());
    }

    #[test]
    fn bit_set_to_true() -> TestResult {
        let mut bitfield: Tested = 0b10101010.into();

        bitfield.set_bit(6.try_into()?, One);

        assert_eq!(bitfield.0, 0b11101010);
        Ok(())
    }

    #[test]
    fn bit_set_to_false() -> TestResult {
        let mut bitfield: Tested = 0b10101010.into();

        bitfield.set_bit(7.try_into()?, Zero);

        assert_eq!(bitfield.0, 0b00101010);
        Ok(())
    }

    #[test]
    fn bit() -> TestResult {
        let bitfield: Tested = 0b10101010.into();

        assert_eq!(bitfield.bit(0.try_into()?), Zero);
        assert_eq!(bitfield.bit(1.try_into()?), One);
        Ok(())
    }

    #[test]
    fn bit_check() -> TestResult {
        let mut bitfield: Tested = 0b10101010.into();

        bitfield.check_bit(6.try_into()?);

        assert_eq!(bitfield.0, 0b11101010);
        Ok(())
    }

    #[test]
    fn bit_uncheck() -> TestResult {
        let mut bitfield: Tested = 0b10101010.into();

        bitfield.uncheck_bit(7.try_into()?);

        assert_eq!(bitfield.0, 0b00101010);
        Ok(())
    }

    #[test]
    fn bit_ref() -> TestResult {
        let bitfield: Tested = 0b10101010.into();

        assert_eq!(*bitfield.bit_ref(0.try_into()?), Zero);
        assert_eq!(*bitfield.bit_ref(1.try_into()?), One);
        Ok(())
    }

    #[test]
    fn bit_mut() -> TestResult {
        let mut bitfield: Tested = 0b10101010.into();

        assert_eq!(*bitfield.bit_ref(0.try_into()?), Zero);
        assert_eq!(*bitfield.bit_ref(1.try_into()?), One);

        *bitfield.bit_mut(0.try_into()?) = One;
        *bitfield.bit_mut(1.try_into()?) = Zero;

        assert_eq!(*bitfield.bit_ref(0.try_into()?), One);
        assert_eq!(*bitfield.bit_ref(1.try_into()?), Zero);
        Ok(())
    }

    #[test]
    fn count_ones() {
        let bitfield: Tested = 0b11100000.into();

        assert_eq!(bitfield.count_ones(), 3);
    }

    #[test]
    fn count_zeros() {
        let bitfield: Tested = 0b11100000.into();

        assert_eq!(bitfield.count_zeros(), 13);
    }

    #[test]
    fn shl() -> TestResult {
        let bitfield: Tested = 0b00000001.into();

        assert_eq!(bitfield << 1.try_into()?, 0b00000010.into());

        let mut bitfield: Tested = 0b00000001.into();
        bitfield <<= 1.try_into()?;

        assert_eq!(bitfield, 0b00000010.into());
        Ok(())
    }

    #[test]
    fn shr() -> TestResult {
        let bitfield: Tested = 0b00000010.into();

        assert_eq!(bitfield >> 1.try_into()?, 0b00000001.into());

        let mut bitfield: Tested = 0b00000010.into();
        bitfield >>= 1.try_into()?;

        assert_eq!(bitfield, 0b00000001.into());
        Ok(())
    }

    #[test]
    fn not() {
        let a: Tested = Tested::NONE;

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
        let a: Tested = Tested::NONE;

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
    fn bits() {
        let bitfield: Tested = 0b11110000.into();
        let mut iter = bitfield.bits();

        assert_eq!(iter.next(), Some(Zero));
        assert_eq!(iter.next(), Some(Zero));
        assert_eq!(iter.next(), Some(Zero));
        assert_eq!(iter.next(), Some(Zero));
        assert_eq!(iter.next(), Some(One));
        assert_eq!(iter.next(), Some(One));
        assert_eq!(iter.next(), Some(One));
        assert_eq!(iter.next(), Some(One));

        for _ in 8..16 {
            assert_eq!(iter.next(), Some(Zero));
        }

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn bits_ref() {
        let bitfield: Tested = 0b11110000.into();
        let mut iter = bitfield.bits_ref();

        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));

        for _ in 8..16 {
            assert_eq!(iter.next().as_deref(), Some(&Zero));
        }

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn bits_mut() {
        let mut bitfield: Tested = 0b11110000.into();

        let mut iter = bitfield.bits_ref();

        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));

        for _ in 8..16 {
            assert_eq!(iter.next().as_deref(), Some(&Zero));
        }

        assert_eq!(iter.next(), None);
        drop(iter);

        for mut bit in bitfield.bits_mut() {
            *bit = !*bit;
        }

        let mut iter = bitfield.bits_ref();

        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));

        for _ in 8..16 {
            assert_eq!(iter.next().as_deref(), Some(&One));
        }

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn collect_from_bits() {
        let a: Tested = 0b11110000.into();
        let iter = a.bits();
        let b: Tested = iter.collect();

        assert_eq!(b, 0b11110000.into());

        let arr = [One, Zero, One, Zero, One, Zero, One, Zero];
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
    fn ones() -> TestResult {
        let bitfield: Tested = 0b11110000.into();
        let mut iter = bitfield.ones();

        assert_eq!(iter.next(), Some(4.try_into()?));
        assert_eq!(iter.next(), Some(5.try_into()?));
        assert_eq!(iter.next(), Some(6.try_into()?));
        assert_eq!(iter.next(), Some(7.try_into()?));
        assert_eq!(iter.next(), None);
        Ok(())
    }

    #[test]
    fn zeros() -> TestResult {
        let bitfield: Tested = 0b11110000.into();
        let mut iter = bitfield.zeros();

        assert_eq!(iter.next(), Some(0.try_into()?));
        assert_eq!(iter.next(), Some(1.try_into()?));
        assert_eq!(iter.next(), Some(2.try_into()?));
        assert_eq!(iter.next(), Some(3.try_into()?));

        for i in 8..16 {
            assert_eq!(iter.next(), Some(i.try_into()?));
        }

        assert_eq!(iter.next(), None);
        Ok(())
    }

    #[test]
    fn from_slice_bool() {
        // Same index order
        let slice: &[Bit] = &[One, Zero, One, Zero, One, Zero, One, Zero];
        let bitfield: Tested = Tested::from_bits_ref(slice);

        assert_eq!(bitfield, 0b01010101.into());
    }

    #[test]
    fn test_send() {
        fn assert_send<T: Send>() {}
        assert_send::<Tested>();
    }

    #[test]
    fn test_sync() {
        fn assert_sync<T: Sync>() {}
        assert_sync::<Tested>();
    }

    #[test]
    fn expand() -> TestResult {
        let bitfield1 = Bitfield16::from(0b00011011);
        let bitfield2: Bitfield32 = bitfield1.expand()?;

        assert_eq!(bitfield2, Bitfield32::from(0b00011011));

        let bitfield1 = Bitfield16::from(0b00011011);
        let bitfield2: Bitfield64 = bitfield1.expand()?;

        assert_eq!(bitfield2, Bitfield64::from(0b00011011));

        let bitfield1 = Bitfield16::from(0b00011011);
        let bitfield2: Bitfield128 = bitfield1.expand()?;

        assert_eq!(bitfield2, Bitfield128::from(0b00011011));

        Ok(())
    }

    #[test]
    fn fast_expand() -> TestResult {
        let bitfield1 = Bitfield16::from(0b00011011);
        let bitfield2: Bitfield32 = bitfield1.expand_optimized()?;

        assert_eq!(bitfield2, Bitfield32::from(0b00011011));

        let bitfield1 = Bitfield16::from(0b00011011);
        let bitfield2: Bitfield64 = bitfield1.expand_optimized()?;

        assert_eq!(bitfield2, Bitfield64::from(0b00011011));

        let bitfield1 = Bitfield16::from(0b00011011);
        let bitfield2: Bitfield128 = bitfield1.expand_optimized()?;

        assert_eq!(bitfield2, Bitfield128::from(0b00011011));

        Ok(())
    }

    #[test]
    fn combine() -> TestResult {
        let bitfield1 = Bitfield16::NONE.clone().check_bit(1.try_into()?).build();
        let bitfield2 = Bitfield16::NONE.clone().check_bit(1.try_into()?).build();

        let bitfield3: Bitfield32 = bitfield1.combine(bitfield2)?;

        assert_eq!(
            bitfield3,
            Bitfield32::NONE
                .clone()
                .check_bit(1.try_into()?)
                .check_bit(17.try_into()?)
                .build()
        );
        Ok(())
    }

    #[test]
    fn split() -> TestResult {
        let bitfield1 = Bitfield32::NONE
            .clone()
            .set_bit(1.try_into()?, One)
            .set_bit((16 + 1).try_into()?, One)
            .build();
        let (bitfield2, bitfield3): (Bitfield16, Bitfield16) = bitfield1.split()?;

        assert_eq!(
            bitfield2,
            Bitfield16::NONE.clone().set_bit(1.try_into()?, One).build()
        );
        assert_eq!(
            bitfield3,
            Bitfield16::NONE.clone().set_bit(1.try_into()?, One).build()
        );
        Ok(())
    }

    #[test]
    fn fast_combine() -> TestResult {
        let bitfield1 = Bitfield16::NONE.clone().set_bit(1.try_into()?, One).build();
        let bitfield2 = Bitfield16::NONE.clone().set_bit(1.try_into()?, One).build();

        let bitfield3: Bitfield32 = bitfield1.combine_optimized(bitfield2)?;

        assert_eq!(
            bitfield3,
            Bitfield32::NONE
                .clone()
                .set_bit(1.try_into()?, One)
                .set_bit((16 + 1).try_into()?, One)
                .build()
        );
        Ok(())
    }

    #[test]
    fn fast_split() -> TestResult {
        let bitfield1 = Bitfield32::NONE
            .clone()
            .set_bit(1.try_into()?, One)
            .set_bit((16 + 1).try_into()?, One)
            .build();
        let (bitfield2, bitfield3): (Bitfield16, Bitfield16) = bitfield1.split_optimized()?;

        assert_eq!(
            bitfield2,
            Bitfield16::NONE.clone().set_bit(1.try_into()?, One).build()
        );
        assert_eq!(
            bitfield3,
            Bitfield16::NONE.clone().set_bit(1.try_into()?, One).build()
        );
        Ok(())
    }
}
