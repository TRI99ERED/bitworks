//! Module containing [`Bitset16`].

use crate::{
    bit::Bit,
    bitset::{Bitset, LeftAligned},
    error::{ConvError, ConvTarget},
    prelude::{Bitset128, Bitset32, Bitset64, Bitset8, Byteset, Index},
    safety_markers::Size,
};
use std::{
    fmt::{Binary, Debug, Display, LowerHex, Octal, UpperHex},
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
        ShrAssign,
    },
};

type Inner = u16;
type BIndex = Index<Bitset16>;
const BITS: usize = 16;

/// [`Bitset`] of bit size 16.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
pub struct Bitset16(pub(crate) Inner);

impl Bitset16 {
    /// Constructs a new value of `Bitset16`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::{Bitset, Bitset16};
    ///
    /// let bitset = Bitset16::new(19);
    ///
    /// assert_eq!(bitset, Bitset16::from_repr(19));
    /// #   Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub const fn new(inner: Inner) -> Self {
        Self(inner)
    }

    /// Returns the inner [`u16`] representation of `Bitset16`.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use bitworks::prelude::Bitset16;
    ///
    /// let bitset = Bitset16::new(19);
    /// let inner: u16 = bitset.into_inner();
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

unsafe impl LeftAligned for Bitset16 {
    type _Repr = Inner;
    type _Size = Size<2>;
    const _BYTE_SIZE: usize = 2;
    const _ALL: Self = Self(Inner::MAX);
    const _NONE: Self = Self(Inner::MIN);

    #[inline(always)]
    fn _from_repr(value: Self::Repr) -> Self {
        Self(value)
    }
}

impl From<Inner> for Bitset16 {
    #[inline(always)]
    fn from(value: Inner) -> Self {
        Self(value)
    }
}

impl From<Bitset16> for Inner {
    #[inline(always)]
    fn from(value: Bitset16) -> Self {
        value.0
    }
}

impl From<BIndex> for Bitset16 {
    #[inline(always)]
    fn from(value: BIndex) -> Self {
        Self(1) << value
    }
}

impl From<Byteset<2>> for Bitset16 {
    #[inline(always)]
    fn from(value: Byteset<2>) -> Self {
        unsafe { std::mem::transmute_copy(&value) }
    }
}

impl From<Bitset8> for Bitset16 {
    #[inline(always)]
    fn from(value: Bitset8) -> Self {
        Self(value.into_inner() as Inner)
    }
}

impl TryFrom<Bitset32> for Bitset16 {
    type Error = ConvError;

    #[inline(always)]
    fn try_from(value: Bitset32) -> Result<Self, Self::Error> {
        Inner::try_from(value.into_inner())
            .map(Self::from)
            .map_err(|_| ConvError::new(ConvTarget::Set(32), ConvTarget::Set(16)))
    }
}

impl TryFrom<Bitset64> for Bitset16 {
    type Error = ConvError;

    #[inline(always)]
    fn try_from(value: Bitset64) -> Result<Self, Self::Error> {
        Inner::try_from(value.into_inner())
            .map(Self::from)
            .map_err(|_| ConvError::new(ConvTarget::Set(64), ConvTarget::Set(16)))
    }
}

impl TryFrom<Bitset128> for Bitset16 {
    type Error = ConvError;

    #[inline(always)]
    fn try_from(value: Bitset128) -> Result<Self, Self::Error> {
        Inner::try_from(value.into_inner())
            .map(Self::from)
            .map_err(|_| ConvError::new(ConvTarget::Set(128), ConvTarget::Set(16)))
    }
}

impl Not for Bitset16 {
    type Output = Self;

    #[inline(always)]
    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

impl BitAnd for Bitset16 {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl BitAndAssign for Bitset16 {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}

impl BitOr for Bitset16 {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for Bitset16 {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl BitXor for Bitset16 {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self::Output {
        Self(self.0 ^ rhs.0)
    }
}

impl BitXorAssign for Bitset16 {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0;
    }
}

impl Shl<BIndex> for Bitset16 {
    type Output = Self;

    #[inline(always)]
    fn shl(self, rhs: BIndex) -> Self::Output {
        Self::from(self.0.shl(rhs.into_inner()))
    }
}

impl ShlAssign<BIndex> for Bitset16 {
    #[inline(always)]
    fn shl_assign(&mut self, rhs: BIndex) {
        *self = self.shl(rhs);
    }
}

impl Shr<BIndex> for Bitset16 {
    type Output = Self;

    #[inline(always)]
    fn shr(self, rhs: BIndex) -> Self::Output {
        Self::from(self.0.shr(rhs.into_inner()))
    }
}

impl ShrAssign<BIndex> for Bitset16 {
    #[inline(always)]
    fn shr_assign(&mut self, rhs: BIndex) {
        *self = self.shr(rhs);
    }
}

impl BitAnd<BIndex> for Bitset16 {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: BIndex) -> Self::Output {
        Self(self.0 & Self::from(rhs).0)
    }
}

impl BitAndAssign<BIndex> for Bitset16 {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: BIndex) {
        self.0 &= Self::from(rhs).0;
    }
}

impl BitOr<BIndex> for Bitset16 {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: BIndex) -> Self::Output {
        Self(self.0 | Self::from(rhs).0)
    }
}

impl BitOrAssign<BIndex> for Bitset16 {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: BIndex) {
        self.0 |= Self::from(rhs).0;
    }
}

impl BitXor<BIndex> for Bitset16 {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: BIndex) -> Self::Output {
        Self(self.0 ^ Self::from(rhs).0)
    }
}

impl BitXorAssign<BIndex> for Bitset16 {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: BIndex) {
        self.0 ^= Self::from(rhs).0;
    }
}

impl FromIterator<Bit> for Bitset16 {
    fn from_iter<T: IntoIterator<Item = Bit>>(iter: T) -> Self {
        iter.into_iter()
            .take(BITS)
            .enumerate()
            .filter_map(|(i, bit)| if bool::from(bit) { Some(i) } else { None })
            .filter_map(|i| BIndex::try_from(i).ok())
            .fold(Self::NONE, |acc, i| acc | Self(1) << i)
    }
}

impl Debug for Bitset16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bitset16({:#018b})", self.0)
    }
}

impl Display for Bitset16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:016b}", self.0)
    }
}

impl Binary for Bitset16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#018b}", self.0)
    }
}

impl Octal for Bitset16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#08o}", self.0)
    }
}

impl UpperHex for Bitset16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#06X}", self.0)
    }
}

impl LowerHex for Bitset16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#06x}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use crate::{bit::Bit::*, prelude::Bitset};

    use super::*;
    type Tested = Bitset16;
    type TestResult = Result<(), Box<dyn Error>>;

    #[test]
    fn construction() -> TestResult {
        let bitset = Tested::NONE
            .clone()
            .replace(0.try_into()?, One)
            .set(1.try_into()?)
            .unset(0.try_into()?)
            .build();

        assert_eq!(bitset, 0b00000010.into());
        Ok(())
    }

    #[test]
    fn conversion_from_integer() {
        let bitset: Tested = 0b10101010.into();

        assert_eq!(bitset.0, 0b10101010);
    }

    #[test]
    fn conversion_from_index() {
        let bitset = Tested::from(Index::<Tested>::MIN);

        assert_eq!(bitset.0, 1);
    }

    #[test]
    fn into_inner() {
        let bitset: Tested = 0b10101010.into();

        assert_eq!(bitset.0, bitset.into_inner());
    }

    #[test]
    fn bit_set_to_true() -> TestResult {
        let mut bitset: Tested = 0b10101010.into();

        bitset.replace(6.try_into()?, One);

        assert_eq!(bitset.0, 0b11101010);
        Ok(())
    }

    #[test]
    fn bit_set_to_false() -> TestResult {
        let mut bitset: Tested = 0b10101010.into();

        bitset.replace(7.try_into()?, Zero);

        assert_eq!(bitset.0, 0b00101010);
        Ok(())
    }

    #[test]
    fn bit() -> TestResult {
        let bitset: Tested = 0b10101010.into();

        assert_eq!(bitset.bit(0.try_into()?), Zero);
        assert_eq!(bitset.bit(1.try_into()?), One);
        Ok(())
    }

    #[test]
    fn bit_check() -> TestResult {
        let mut bitset: Tested = 0b10101010.into();

        bitset.set(6.try_into()?);

        assert_eq!(bitset.0, 0b11101010);
        Ok(())
    }

    #[test]
    fn bit_uncheck() -> TestResult {
        let mut bitset: Tested = 0b10101010.into();

        bitset.unset(7.try_into()?);

        assert_eq!(bitset.0, 0b00101010);
        Ok(())
    }

    #[test]
    fn bit_ref() -> TestResult {
        let bitset: Tested = 0b10101010.into();

        assert_eq!(*bitset.bit_ref(0.try_into()?), Zero);
        assert_eq!(*bitset.bit_ref(1.try_into()?), One);
        Ok(())
    }

    #[test]
    fn bit_mut() -> TestResult {
        let mut bitset: Tested = 0b10101010.into();

        assert_eq!(*bitset.bit_ref(0.try_into()?), Zero);
        assert_eq!(*bitset.bit_ref(1.try_into()?), One);

        *bitset.bit_mut(0.try_into()?) = One;
        *bitset.bit_mut(1.try_into()?) = Zero;

        assert_eq!(*bitset.bit_ref(0.try_into()?), One);
        assert_eq!(*bitset.bit_ref(1.try_into()?), Zero);
        Ok(())
    }

    #[test]
    fn count_ones() {
        let bitset: Tested = 0b11100000.into();

        assert_eq!(bitset.count_ones(), 3);
    }

    #[test]
    fn count_zeros() {
        let bitset: Tested = 0b11100000.into();

        assert_eq!(bitset.count_zeros(), 13);
    }

    #[test]
    fn shl() -> TestResult {
        let bitset: Tested = 0b00000001.into();

        assert_eq!(bitset << 1.try_into()?, 0b00000010.into());

        let mut bitset: Tested = 0b00000001.into();
        bitset <<= 1.try_into()?;

        assert_eq!(bitset, 0b00000010.into());
        Ok(())
    }

    #[test]
    fn shr() -> TestResult {
        let bitset: Tested = 0b00000010.into();

        assert_eq!(bitset >> 1.try_into()?, 0b00000001.into());

        let mut bitset: Tested = 0b00000010.into();
        bitset >>= 1.try_into()?;

        assert_eq!(bitset, 0b00000001.into());
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
        let bitset: Tested = 0b11110000.into();
        let mut iter = bitset.bits();

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
        let bitset: Tested = 0b11110000.into();
        let mut iter = bitset.bits_ref();

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
        let mut bitset: Tested = 0b11110000.into();

        let mut iter = bitset.bits_ref();

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

        for mut bit in bitset.bits_mut() {
            *bit = !*bit;
        }

        let mut iter = bitset.bits_ref();

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
        let bitset: Tested = arr
            .into_iter()
            // Need to reverse to get the same visual representation, because
            // array's .into_iter() makes iterator from left to right,
            // but .collect() will collect from right to left here.
            .rev()
            .collect();

        assert_eq!(bitset, 0b10101010.into());
    }

    #[test]
    fn ones() -> TestResult {
        let bitset: Tested = 0b11110000.into();
        let mut iter = bitset.ones();

        assert_eq!(iter.next(), Some(4.try_into()?));
        assert_eq!(iter.next(), Some(5.try_into()?));
        assert_eq!(iter.next(), Some(6.try_into()?));
        assert_eq!(iter.next(), Some(7.try_into()?));
        assert_eq!(iter.next(), None);
        Ok(())
    }

    #[test]
    fn zeros() -> TestResult {
        let bitset: Tested = 0b11110000.into();
        let mut iter = bitset.zeros();

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
        let bitset: Tested = Tested::from_bits_col(slice);

        assert_eq!(bitset, 0b01010101.into());
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
        let bitset1 = Bitset16::from(0b00011011);
        let bitset2: Bitset32 = bitset1.expand();

        assert_eq!(bitset2, Bitset32::from(0b00011011));

        let bitset1 = Bitset16::from(0b00011011);
        let bitset2: Bitset64 = bitset1.expand();

        assert_eq!(bitset2, Bitset64::from(0b00011011));

        let bitset1 = Bitset16::from(0b00011011);
        let bitset2: Bitset128 = bitset1.expand();

        assert_eq!(bitset2, Bitset128::from(0b00011011));

        Ok(())
    }

    #[test]
    fn fast_expand() -> TestResult {
        let bitset1 = Bitset16::from(0b00011011);
        let bitset2: Bitset32 = bitset1.expand_optimized();

        assert_eq!(bitset2, Bitset32::from(0b00011011));

        let bitset1 = Bitset16::from(0b00011011);
        let bitset2: Bitset64 = bitset1.expand_optimized();

        assert_eq!(bitset2, Bitset64::from(0b00011011));

        let bitset1 = Bitset16::from(0b00011011);
        let bitset2: Bitset128 = bitset1.expand_optimized();

        assert_eq!(bitset2, Bitset128::from(0b00011011));

        Ok(())
    }

    #[test]
    fn combine() -> TestResult {
        let bitset1 = Bitset16::NONE.clone().set(1.try_into()?).build();
        let bitset2 = Bitset16::NONE.clone().set(1.try_into()?).build();

        let bitset3: Bitset32 = bitset1.combine(bitset2);

        assert_eq!(
            bitset3,
            Bitset32::NONE
                .clone()
                .set(1.try_into()?)
                .set(17.try_into()?)
                .build()
        );
        Ok(())
    }

    #[test]
    fn split() -> TestResult {
        let bitset1 = Bitset32::NONE
            .clone()
            .replace(1.try_into()?, One)
            .replace((16 + 1).try_into()?, One)
            .build();
        let (bitset2, bitset3): (Bitset16, Bitset16) = bitset1.split();

        assert_eq!(
            bitset2,
            Bitset16::NONE.clone().replace(1.try_into()?, One).build()
        );
        assert_eq!(
            bitset3,
            Bitset16::NONE.clone().replace(1.try_into()?, One).build()
        );
        Ok(())
    }

    #[test]
    fn fast_combine() -> TestResult {
        let bitset1 = Bitset16::NONE.clone().replace(1.try_into()?, One).build();
        let bitset2 = Bitset16::NONE.clone().replace(1.try_into()?, One).build();

        let bitset3: Bitset32 = bitset1.combine_optimized(bitset2);

        assert_eq!(
            bitset3,
            Bitset32::NONE
                .clone()
                .replace(1.try_into()?, One)
                .replace((16 + 1).try_into()?, One)
                .build()
        );
        Ok(())
    }

    #[test]
    fn fast_split() -> TestResult {
        let bitset1 = Bitset32::NONE
            .clone()
            .replace(1.try_into()?, One)
            .replace((16 + 1).try_into()?, One)
            .build();
        let (bitset2, bitset3): (Bitset16, Bitset16) = bitset1.split_optimized();

        assert_eq!(
            bitset2,
            Bitset16::NONE.clone().replace(1.try_into()?, One).build()
        );
        assert_eq!(
            bitset3,
            Bitset16::NONE.clone().replace(1.try_into()?, One).build()
        );
        Ok(())
    }
}
