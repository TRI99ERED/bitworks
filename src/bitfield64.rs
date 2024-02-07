//! Module containing [`Bitfield64`].

use crate::{
    bit_ref::{BitMut, BitRef}, bitfield::{Bitfield, Simple}, error::{ConvError, ConvTarget}, prelude::{Bitfield128, Bitfield16, Bitfield32, Bitfield8, ByteField, FlagsEnum, Index}
};
use std::{
    collections::BTreeSet,
    fmt::{Binary, Display, LowerHex, Octal, UpperHex},
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
        ShrAssign,
    },
};

type Inner = u64;
type BIndex = Index<Bitfield64>;
const BITS: usize = 64;

/// [`Bitfield`] of size 64.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Bitfield64(pub(crate) Inner);

impl Bitfield64 {
    #[inline(always)]
    pub const fn new(n: Inner) -> Self {
        Self(n)
    }

    /// Returns the inner representation of `Bitfield64`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use simple_bitfield::prelude::Bitfield64;
    ///
    /// let bitfield = Bitfield64::from(19);
    /// let inner: u64 = bitfield.into_inner();
    ///
    /// assert_eq!(inner, 19);
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn into_inner(&self) -> Inner {
        self.0
    }
}

impl Bitfield for Bitfield64 {
    const BIT_SIZE: usize = BITS;
    const ONE: Self = Self(1);
    const NONE: Self = Self(Inner::MIN);
    const ALL: Self = Self(Inner::MAX);

    #[inline(always)]
    fn count_ones(&self) -> usize {
        self.0.count_ones() as usize
    }

    #[inline(always)]
    fn count_zeros(&self) -> usize {
        self.0.count_zeros() as usize
    }

    #[inline(always)]
    fn bit_ref(&self, index: BIndex) -> BitRef<'_, Self> {
        let mask = Self::from(BIndex::MIN) << index;
        BitRef((*self & mask) != Self::NONE, index, self)
    }

    #[inline(always)]
    fn bit_mut(&mut self, index: BIndex) -> BitMut<'_, Self> {
        let mask = Self::from(BIndex::MIN) << index;
        BitMut((*self & mask) != Self::NONE, index, self)
    }
}

unsafe impl Simple for Bitfield64 {}

impl From<Inner> for Bitfield64 {
    #[inline(always)]
    fn from(value: Inner) -> Self {
        Self(value)
    }
}

impl From<Bitfield64> for Inner {
    #[inline(always)]
    fn from(value: Bitfield64) -> Self {
        value.0
    }
}

impl From<BIndex> for Bitfield64 {
    #[inline(always)]
    fn from(value: BIndex) -> Self {
        Self(1) << value
    }
}

impl<T> From<T> for Bitfield64
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex: From<T>,
{
    #[inline(always)]
    fn from(value: T) -> Self {
        Self(1) << BIndex::from(value)
    }
}

impl From<ByteField<8>> for Bitfield64 {
    #[inline(always)]
    fn from(value: ByteField<8>) -> Self {
        unsafe { std::mem::transmute_copy(&value) }
    }
}

impl From<Bitfield8> for Bitfield64 {
    #[inline(always)]
    fn from(value: Bitfield8) -> Self {
        Self(value.into_inner() as Inner)
    }
}

impl From<Bitfield16> for Bitfield64 {
    #[inline(always)]
    fn from(value: Bitfield16) -> Self {
        Self(value.into_inner() as Inner)
    }
}

impl From<Bitfield32> for Bitfield64 {
    #[inline(always)]
    fn from(value: Bitfield32) -> Self {
        Self(value.into_inner() as Inner)
    }
}

impl TryFrom<Bitfield128> for Bitfield64 {
    type Error = ConvError;

    #[inline(always)]
    fn try_from(value: Bitfield128) -> Result<Self, Self::Error> {
        Inner::try_from(value.into_inner())
            .map(Self::from)
            .map_err(|_| ConvError::new(ConvTarget::Field(128), ConvTarget::Field(64)))
    }
}

impl Not for Bitfield64 {
    type Output = Self;

    #[inline(always)]
    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

impl BitAnd for Bitfield64 {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl BitAndAssign for Bitfield64 {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}

impl BitOr for Bitfield64 {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for Bitfield64 {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl BitXor for Bitfield64 {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self::Output {
        Self(self.0 ^ rhs.0)
    }
}

impl BitXorAssign for Bitfield64 {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0;
    }
}

impl Shl<BIndex> for Bitfield64 {
    type Output = Self;

    #[inline(always)]
    fn shl(self, rhs: BIndex) -> Self::Output {
        Self::from(self.0.shl(rhs.into_inner()))
    }
}

impl ShlAssign<BIndex> for Bitfield64 {
    #[inline(always)]
    fn shl_assign(&mut self, rhs: BIndex) {
        *self = self.shl(rhs);
    }
}

impl Shr<BIndex> for Bitfield64 {
    type Output = Self;

    #[inline(always)]
    fn shr(self, rhs: BIndex) -> Self::Output {
        Self::from(self.0.shr(rhs.into_inner()))
    }
}

impl ShrAssign<BIndex> for Bitfield64 {
    #[inline(always)]
    fn shr_assign(&mut self, rhs: BIndex) {
        *self = self.shr(rhs);
    }
}

impl BitAnd<BIndex> for Bitfield64 {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: BIndex) -> Self::Output {
        Self(self.0 & Self::from(rhs).0)
    }
}

impl BitAndAssign<BIndex> for Bitfield64 {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: BIndex) {
        self.0 &= Self::from(rhs).0;
    }
}

impl BitOr<BIndex> for Bitfield64 {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: BIndex) -> Self::Output {
        Self(self.0 | Self::from(rhs).0)
    }
}

impl BitOrAssign<BIndex> for Bitfield64 {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: BIndex) {
        self.0 |= Self::from(rhs).0;
    }
}

impl BitXor<BIndex> for Bitfield64 {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: BIndex) -> Self::Output {
        Self(self.0 ^ Self::from(rhs).0)
    }
}

impl BitXorAssign<BIndex> for Bitfield64 {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: BIndex) {
        self.0 ^= Self::from(rhs).0;
    }
}

impl<T> BitAnd<T> for Bitfield64
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex: From<T>,
{
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: T) -> Self::Output {
        Self(self.0 & Self::from(rhs).0)
    }
}

impl<T> BitAndAssign<T> for Bitfield64
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex: From<T>,
{
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: T) {
        self.0 &= Self::from(rhs).0;
    }
}

impl<T> BitOr<T> for Bitfield64
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex: From<T>,
{
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: T) -> Self::Output {
        Self(self.0 | Self::from(rhs).0)
    }
}

impl<T> BitOrAssign<T> for Bitfield64
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex: From<T>,
{
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: T) {
        self.0 |= Self::from(rhs).0;
    }
}

impl<T> BitXor<T> for Bitfield64
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex: From<T>,
{
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: T) -> Self::Output {
        Self(self.0 ^ Self::from(rhs).0)
    }
}

impl<T> BitXorAssign<T> for Bitfield64
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex: From<T>,
{
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: T) {
        self.0 ^= Self::from(rhs).0;
    }
}

impl FromIterator<bool> for Bitfield64 {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut bitfield: Self = Self::from(0);
        for (i, bit) in iter.into_iter().take(BITS).enumerate() {
            bitfield.0 |= (if bit { 1 } else { 0 }) << (i as Inner);
        }
        bitfield
    }
}

impl<A> FromIterator<A> for Bitfield64
where
    A: FlagsEnum<Bitfield = Self>,
    BIndex: From<A>,
{
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        let mut bitfield = Self::NONE;
        let mut seen_indices = BTreeSet::new();

        for e in iter {
            let index = BIndex::from(e);
            if !seen_indices.contains(&index) {
                seen_indices.insert(index);
                bitfield |= Self(1) << index;
            }
        }
        bitfield
    }
}

impl Display for Bitfield64 {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:064b}", self.0)
    }
}

impl Binary for Bitfield64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#066b}", self.0)
    }
}

impl Octal for Bitfield64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#026o}", self.0)
    }
}

impl UpperHex for Bitfield64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#018X}", self.0)
    }
}

impl LowerHex for Bitfield64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#018x}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use super::*;
    type Tested = Bitfield64;
    type TestResult = Result<(), Box<dyn Error>>;

    #[test]
    fn construction() -> TestResult {
        let bitfield = Tested::NONE.clone()
            .set_bit(0.try_into()?, true)
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

        bitfield.set_bit(6.try_into()?, true);

        assert_eq!(bitfield.0, 0b11101010);
        Ok(())
    }

    #[test]
    fn bit_set_to_false() -> TestResult {
        let mut bitfield: Tested = 0b10101010.into();

        bitfield.set_bit(7.try_into()?, false);

        assert_eq!(bitfield.0, 0b00101010);
        Ok(())
    }

    #[test]
    fn bit() -> TestResult {
        let bitfield: Tested = 0b10101010.into();

        assert_eq!(bitfield.bit(0.try_into()?), false);
        assert_eq!(bitfield.bit(1.try_into()?), true);
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

        assert_eq!(*bitfield.bit_ref(0.try_into()?), false);
        assert_eq!(*bitfield.bit_ref(1.try_into()?), true);
        Ok(())
    }

    #[test]
    fn bit_mut() -> TestResult {
        let mut bitfield: Tested = 0b10101010.into();

        assert_eq!(*bitfield.bit_ref(0.try_into()?), false);
        assert_eq!(*bitfield.bit_ref(1.try_into()?), true);

        *bitfield.bit_mut(0.try_into()?) = true;
        *bitfield.bit_mut(1.try_into()?) = false;

        assert_eq!(*bitfield.bit_ref(0.try_into()?), true);
        assert_eq!(*bitfield.bit_ref(1.try_into()?), false);
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

        assert_eq!(bitfield.count_zeros(), 61);
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

        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(true));

        for _ in 8..64 {
            assert_eq!(iter.next(), Some(false));
        }

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn bits_ref() {
        let bitfield: Tested = 0b11110000.into();
        let mut iter = bitfield.bits_ref();

        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));

        for _ in 8..64 {
            assert_eq!(iter.next().as_deref(), Some(&false));
        }

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn bits_mut() {
        let mut bitfield: Tested = 0b11110000.into();

        let mut iter = bitfield.bits_ref();

        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));

        for _ in 8..64 {
            assert_eq!(iter.next().as_deref(), Some(&false));
        }

        assert_eq!(iter.next(), None);
        drop(iter);

        for mut bit in bitfield.bits_mut() {
            *bit = !*bit;
        }

        let mut iter = bitfield.bits_ref();

        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));

        for _ in 8..64 {
            assert_eq!(iter.next().as_deref(), Some(&true));
        }

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn collect_from_bits() {
        let a: Tested = 0b11110000.into();
        let iter = a.bits();
        let b: Tested = iter.collect();

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

        for i in 8..64 {
            assert_eq!(iter.next(), Some(i.try_into()?));
        }

        assert_eq!(iter.next(), None);
        Ok(())
    }

    #[test]
    fn from_slice_bool() {
        // Same index order
        let slice: &[bool] = &[true, false, true, false, true, false, true, false];
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
        let bitfield1 = Bitfield64::from(0b00011011);
        let bitfield2: Bitfield128 = bitfield1.expand()?;

        assert_eq!(bitfield2, Bitfield128::from(0b00011011));

        Ok(())
    }

    #[test]
    fn fast_expand() -> TestResult {
        let bitfield1 = Bitfield64::from(0b00011011);
        let bitfield2: Bitfield128 = bitfield1.fast_expand()?;

        assert_eq!(bitfield2, Bitfield128::from(0b00011011));

        Ok(())
    }

    #[test]
    fn combine() -> TestResult {
        let bitfield1 = Bitfield64::NONE.clone().set_bit(1.try_into()?, true).build();
        let bitfield2 = Bitfield64::NONE.clone().set_bit(1.try_into()?, true).build();

        let bitfield3: Bitfield128 = bitfield1.combine(bitfield2)?;

        assert_eq!(
            bitfield3,
            Bitfield128::NONE.clone()
                .set_bit(1.try_into()?, true)
                .set_bit((64 + 1).try_into()?, true)
                .build()
        );
        Ok(())
    }

    #[test]
    fn split() -> TestResult {
        let bitfield1 = Bitfield128::NONE.clone()
            .set_bit(1.try_into()?, true)
            .set_bit((64 + 1).try_into()?, true)
            .build();
        let (bitfield2, bitfield3): (Bitfield64, Bitfield64) = bitfield1.split()?;

        assert_eq!(
            bitfield2,
            Bitfield64::NONE.clone().set_bit(1.try_into()?, true).build()
        );
        assert_eq!(
            bitfield3,
            Bitfield64::NONE.clone().set_bit(1.try_into()?, true).build()
        );
        Ok(())
    }

    #[test]
    fn fast_combine() -> TestResult {
        let bitfield1 = Bitfield64::NONE.clone().set_bit(1.try_into()?, true).build();
        let bitfield2 = Bitfield64::NONE.clone().set_bit(1.try_into()?, true).build();

        let bitfield3: Bitfield128 = bitfield1.fast_combine(bitfield2)?;

        assert_eq!(
            bitfield3,
            Bitfield128::NONE.clone()
                .set_bit(1.try_into()?, true)
                .set_bit((64 + 1).try_into()?, true)
                .build()
        );
        Ok(())
    }

    #[test]
    fn fast_split() -> TestResult {
        let bitfield1 = Bitfield128::NONE.clone()
            .set_bit(1.try_into()?, true)
            .set_bit((64 + 1).try_into()?, true)
            .build();
        let (bitfield2, bitfield3): (Bitfield64, Bitfield64) = bitfield1.fast_split()?;

        assert_eq!(
            bitfield2,
            Bitfield64::NONE.clone().set_bit(1.try_into()?, true).build()
        );
        assert_eq!(
            bitfield3,
            Bitfield64::NONE.clone().set_bit(1.try_into()?, true).build()
        );
        Ok(())
    }
}
