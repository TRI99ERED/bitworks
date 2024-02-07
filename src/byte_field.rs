//! Module containing [`ByteField`].

use crate::{
    bit_ref::{BitMut, BitRef},
    bitfield::Simple,
    prelude::{Bitfield, FlagsEnum, Index},
};
use std::{
    collections::BTreeSet,
    fmt::{Binary, Display, LowerHex, Octal, UpperHex},
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
        ShrAssign,
    },
};

type Inner<const N: usize> = [u8; N];
type BIndex<const N: usize> = Index<ByteField<N>>;

const fn byte_index(index: usize) -> usize {
    index / 8
}

const fn bit_index(index: usize) -> usize {
    index % 8
}

const fn bitmask(index: usize) -> u8 {
    1 << bit_index(index)
}

/// [`Bitfield`] of variable `size`.
/// `N` is size in bytes of the `ByteField`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ByteField<const N: usize>(pub(crate) Inner<N>);

impl<const N: usize> ByteField<N> {
    #[inline(always)]
    pub const fn new(arr: Inner<N>) -> Self {
        Self(arr)
    }

    #[inline(always)]
    pub fn into_inner(&self) -> Inner<N> {
        self.0
    }

    const fn __one() -> Self {
        let mut inner: Inner<N> = [0; N];
        inner[0] = 1;
        Self(inner)
    }
}

impl<const N: usize> Bitfield for ByteField<N> {
    const BIT_SIZE: usize = N * 8;

    const ONE: Self = Self::__one();

    const NONE: Self = Self([0; N]);

    const ALL: Self = Self([255; N]);

    #[inline(always)]
    fn from_index(index: &BIndex<N>) -> Self {
        Self::from(*index)
    }

    #[inline(always)]
    fn from_flag<T>(flag: &T) -> Self
    where
        T: FlagsEnum<Bitfield = Self> + Copy,
        BIndex<N>: From<T>,
    {
        Self::from(BIndex::<N>::from(*flag))
    }

    #[inline(always)]
    fn count_ones(&self) -> usize {
        self.0
            .iter()
            .fold(0usize, |acc, &e| acc + e.count_ones() as usize)
    }

    #[inline(always)]
    fn count_zeros(&self) -> usize {
        self.0
            .iter()
            .fold(0usize, |acc, &e| acc + e.count_zeros() as usize)
    }

    #[inline(always)]
    fn set_bit(&mut self, Index::<Self>(index, ..): BIndex<N>, value: bool) -> &mut Self {
        if value {
            self.0[byte_index(index)] |= bitmask(index);
        } else {
            self.0[byte_index(index)] &= !(bitmask(index));
        }
        self
    }

    #[inline(always)]
    fn check_bit(&mut self, Index::<Self>(index, ..): BIndex<N>) -> &mut Self {
        self.0[byte_index(index)] |= bitmask(index);
        self
    }

    #[inline(always)]
    fn uncheck_bit(&mut self, Index::<Self>(index, ..): BIndex<N>) -> &mut Self {
        self.0[byte_index(index)] &= !(bitmask(index));
        self
    }

    #[inline(always)]
    fn bit(self, Index::<Self>(index, ..): BIndex<N>) -> bool {
        (self.0[byte_index(index)] & bitmask(index)) != 0
    }

    #[inline(always)]
    fn bit_ref(&self, index: BIndex<N>) -> BitRef<'_, Self> {
        BitRef(
            (self.0[byte_index(index.into_inner())] & bitmask(index.into_inner())) != 0,
            index,
            self,
        )
    }

    #[inline(always)]
    fn bit_mut(&mut self, index: BIndex<N>) -> BitMut<'_, Self> {
        BitMut(
            (self.0[byte_index(index.into_inner())] & bitmask(index.into_inner())) != 0,
            index,
            self,
        )
    }
}

unsafe impl<const N: usize> Simple for ByteField<N> {}

impl<const N: usize> From<Inner<N>> for ByteField<N> {
    #[inline(always)]
    fn from(value: Inner<N>) -> Self {
        Self(value)
    }
}

impl<const N: usize> From<ByteField<N>> for Inner<N> {
    #[inline(always)]
    fn from(value: ByteField<N>) -> Self {
        value.0
    }
}

impl<const N: usize> From<BIndex<N>> for ByteField<N> {
    fn from(Index::<Self>(index, ..): BIndex<N>) -> Self {
        let mut inner = [0; N];
        inner[byte_index(index)] = bitmask(index);
        Self(inner)
    }
}

impl<const N: usize, T> From<T> for ByteField<N>
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex<N>: From<T>,
{
    #[inline(always)]
    fn from(value: T) -> Self {
        Self::from(BIndex::from(value))
    }
}

impl<const N: usize> Not for ByteField<N> {
    type Output = Self;

    fn not(mut self) -> Self::Output {
        for chunk in &mut self.0 {
            *chunk = !*chunk;
        }
        self
    }
}

impl<const N: usize> BitAnd for ByteField<N> {
    type Output = Self;

    fn bitand(mut self, rhs: Self) -> Self::Output {
        for (i, chunk) in self.0.iter_mut().enumerate() {
            *chunk &= rhs.0[i];
        }
        self
    }
}

impl<const N: usize> BitAndAssign for ByteField<N> {
    fn bitand_assign(&mut self, rhs: Self) {
        for (i, chunk) in self.0.iter_mut().enumerate() {
            *chunk &= rhs.0[i];
        }
    }
}

impl<const N: usize> BitOr for ByteField<N> {
    type Output = Self;

    fn bitor(mut self, rhs: Self) -> Self::Output {
        for (i, chunk) in self.0.iter_mut().enumerate() {
            *chunk |= rhs.0[i];
        }
        self
    }
}

impl<const N: usize> BitOrAssign for ByteField<N> {
    fn bitor_assign(&mut self, rhs: Self) {
        for (i, chunk) in self.0.iter_mut().enumerate() {
            *chunk |= rhs.0[i];
        }
    }
}

impl<const N: usize> BitXor for ByteField<N> {
    type Output = Self;

    fn bitxor(mut self, rhs: Self) -> Self::Output {
        for (i, chunk) in self.0.iter_mut().enumerate() {
            *chunk ^= rhs.0[i];
        }
        self
    }
}

impl<const N: usize> BitXorAssign for ByteField<N> {
    fn bitxor_assign(&mut self, rhs: Self) {
        for (i, chunk) in self.0.iter_mut().enumerate() {
            *chunk ^= rhs.0[i];
        }
    }
}

impl<const N: usize> Shl<BIndex<N>> for ByteField<N> {
    type Output = Self;

    fn shl(self, Index::<Self>(index, ..): BIndex<N>) -> Self::Output {
        let mut inner = self.0;

        let byte_shift = byte_index(index);
        let bit_shift = bit_index(index);

        if byte_shift > 0 {
            unsafe {
                std::ptr::copy(
                    inner.as_ptr().add(byte_shift),
                    inner.as_mut_ptr(),
                    N - byte_shift,
                );
                std::ptr::write_bytes(inner.as_mut_ptr().add(N - byte_shift), 0, byte_shift);
            }
        }

        if bit_shift > 0 {
            let mut carry = 0;
            for chunk in inner.iter_mut().rev() {
                let shifted = *chunk << bit_shift | carry;
                carry = *chunk >> (8 - bit_shift);
                *chunk = shifted;
            }
        }
        Self(inner)
    }
}

impl<const N: usize> ShlAssign<BIndex<N>> for ByteField<N> {
    fn shl_assign(&mut self, rhs: BIndex<N>) {
        *self = self.shl(rhs);
    }
}

impl<const N: usize> Shr<BIndex<N>> for ByteField<N> {
    type Output = Self;

    fn shr(self, Index::<Self>(index, ..): BIndex<N>) -> Self::Output {
        let mut inner = self.0;

        let byte_shift = byte_index(index);
        let bit_shift = bit_index(index);

        if byte_shift > 0 {
            unsafe {
                std::ptr::copy(
                    inner.as_ptr(),
                    inner.as_mut_ptr().add(byte_shift),
                    N - byte_shift,
                );
                std::ptr::write_bytes(inner.as_mut_ptr(), 0, byte_shift);
            }
        }

        if bit_shift > 0 {
            let mut carry = 0;
            for chunk in inner.iter_mut() {
                let shifted = *chunk >> bit_shift | carry;
                carry = *chunk << (8 - bit_shift);
                *chunk = shifted;
            }
        }
        Self(inner)
    }
}

impl<const N: usize> ShrAssign<BIndex<N>> for ByteField<N> {
    fn shr_assign(&mut self, rhs: BIndex<N>) {
        *self = self.shr(rhs);
    }
}

impl<const N: usize> BitAnd<BIndex<N>> for ByteField<N> {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: BIndex<N>) -> Self::Output {
        self & Self::from(rhs)
    }
}

impl<const N: usize> BitAndAssign<BIndex<N>> for ByteField<N> {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: BIndex<N>) {
        *self &= Self::from(rhs);
    }
}

impl<const N: usize> BitOr<BIndex<N>> for ByteField<N> {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: BIndex<N>) -> Self::Output {
        self | Self::from(rhs)
    }
}

impl<const N: usize> BitOrAssign<BIndex<N>> for ByteField<N> {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: BIndex<N>) {
        *self |= Self::from(rhs);
    }
}

impl<const N: usize> BitXor<BIndex<N>> for ByteField<N> {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: BIndex<N>) -> Self::Output {
        self ^ Self::from(rhs)
    }
}

impl<const N: usize> BitXorAssign<BIndex<N>> for ByteField<N> {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: BIndex<N>) {
        *self ^= Self::from(rhs);
    }
}

impl<const N: usize, T> BitAnd<T> for ByteField<N>
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex<N>: From<T>,
{
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: T) -> Self::Output {
        self & Self::from(rhs)
    }
}

impl<const N: usize, T> BitAndAssign<T> for ByteField<N>
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex<N>: From<T>,
{
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: T) {
        *self &= Self::from(rhs);
    }
}

impl<const N: usize, T> BitOr<T> for ByteField<N>
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex<N>: From<T>,
{
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: T) -> Self::Output {
        self | Self::from(rhs)
    }
}

impl<const N: usize, T> BitOrAssign<T> for ByteField<N>
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex<N>: From<T>,
{
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: T) {
        *self |= Self::from(rhs);
    }
}

impl<const N: usize, T> BitXor<T> for ByteField<N>
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex<N>: From<T>,
{
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: T) -> Self::Output {
        self ^ Self::from(rhs)
    }
}

impl<const N: usize, T> BitXorAssign<T> for ByteField<N>
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex<N>: From<T>,
{
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: T) {
        *self ^= Self::from(rhs);
    }
}

impl<const N: usize> FromIterator<bool> for ByteField<N> {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        iter.into_iter()
            .take(N * 8)
            .enumerate()
            .filter_map(|(i, bit)| if bit { Some(i) } else { None })
            .filter_map(|i| BIndex::try_from(i).ok())
            .fold(Self::NONE, |acc, i| acc | Self::__one() << i)
    }
}

impl<const N: usize, A> FromIterator<A> for ByteField<N>
where
    A: FlagsEnum<Bitfield = Self>,
    BIndex<N>: From<A>,
{
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        let mut bitfield = Self::NONE;
        let mut seen_indices = BTreeSet::new();

        for e in iter {
            let index = BIndex::from(e);
            if !seen_indices.contains(&index) {
                seen_indices.insert(index);
                bitfield |= Self::from(index);
            }
        }
        bitfield
    }
}

impl<const N: usize> Display for ByteField<N> {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = self
            .0
            .iter()
            .enumerate()
            .fold("\n[".to_owned(), |mut acc, (i, &chunk)| {
                acc.push_str(&format!(" {:08b} ", chunk));
                if (i + 1) % 4 == 0 && i != N - 1 {
                    acc.push_str(" \n ")
                }
                acc
            });
        if N > 4 && N % 4 > 0 {
            let padding = (4 - N % 4) * 10 + 1;
            s.push_str(&format!("{:>padding$}", "]"));
        } else {
            s.push(']');
        }
        write!(f, "{s}")
    }
}

impl<const N: usize> Binary for ByteField<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.0.iter().fold("".to_owned(), |mut acc, &chunk| {
            acc.push_str(&format!("{:08b}", chunk));
            acc
        });
        write!(f, "{s}")
    }
}

impl<const N: usize> Octal for ByteField<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.0.iter().fold("".to_owned(), |mut acc, &chunk| {
            acc.push_str(&format!("{:03o}", chunk));
            acc
        });
        write!(f, "{s}")
    }
}

impl<const N: usize> UpperHex for ByteField<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.0.iter().fold("".to_owned(), |mut acc, &chunk| {
            acc.push_str(&format!("{:02X}", chunk));
            acc
        });
        write!(f, "{s}")
    }
}

impl<const N: usize> LowerHex for ByteField<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.0.iter().fold("".to_owned(), |mut acc, &chunk| {
            acc.push_str(&format!("{:02x}", chunk));
            acc
        });
        write!(f, "{s}")
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use super::*;
    type Tested1 = ByteField<1>;
    type Tested2 = ByteField<2>;
    type Tested4 = ByteField<4>;
    type Tested8 = ByteField<8>;
    type Tested16 = ByteField<16>;

    type TestedOdd = ByteField<3>;

    type TestResult = Result<(), Box<dyn Error>>;

    #[test]
    fn construction() -> TestResult {
        let bitfield = Tested1::NONE
            .clone()
            .set_bit(0.try_into()?, true)
            .check_bit(1.try_into()?)
            .uncheck_bit(0.try_into()?)
            .build();

        assert_eq!(bitfield, [0b00000010].into());
        Ok(())
    }

    #[test]
    fn conversion_from_arr() {
        let bitfield: Tested1 = [0b10101010].into();

        assert_eq!(bitfield.0, [0b10101010]);
    }

    #[test]
    fn conversion_from_index() {
        let bitfield = Tested1::from(Index::<Tested1>::MIN);

        assert_eq!(bitfield.0, [1]);
    }

    #[test]
    fn into_inner() {
        let bitfield: Tested1 = [0b10101010].into();

        assert_eq!(bitfield.0, bitfield.into_inner());
    }

    #[test]
    fn bit_set_to_true() -> TestResult {
        let mut bitfield: Tested1 = [0b10101010].into();

        bitfield.set_bit(6.try_into()?, true);

        assert_eq!(bitfield.0, [0b11101010]);
        Ok(())
    }

    #[test]
    fn bit_set_to_false() -> TestResult {
        let mut bitfield: Tested1 = [0b10101010].into();

        bitfield.set_bit(7.try_into()?, false);

        assert_eq!(bitfield.0, [0b00101010]);
        Ok(())
    }

    #[test]
    fn bit() -> TestResult {
        let bitfield: Tested1 = [0b10101010].into();

        assert_eq!(bitfield.bit(0.try_into()?), false);
        assert_eq!(bitfield.bit(1.try_into()?), true);
        Ok(())
    }

    #[test]
    fn bit_check() -> TestResult {
        let mut bitfield: Tested1 = [0b10101010].into();

        bitfield.check_bit(6.try_into()?);

        assert_eq!(bitfield.0, [0b11101010]);
        Ok(())
    }

    #[test]
    fn bit_uncheck() -> TestResult {
        let mut bitfield: Tested1 = [0b10101010].into();

        bitfield.uncheck_bit(7.try_into()?);

        assert_eq!(bitfield.0, [0b00101010]);
        Ok(())
    }

    #[test]
    fn bit_ref() -> TestResult {
        let bitfield: Tested1 = [0b10101010].into();

        assert_eq!(*bitfield.bit_ref(0.try_into()?), false);
        assert_eq!(*bitfield.bit_ref(1.try_into()?), true);
        Ok(())
    }

    #[test]
    fn bit_mut() -> TestResult {
        let mut bitfield: Tested1 = [0b10101010].into();

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
        let bitfield: Tested1 = [0b11100000].into();

        assert_eq!(bitfield.count_ones(), 3);
    }

    #[test]
    fn count_zeros() {
        let bitfield: Tested1 = [0b11100000].into();

        assert_eq!(bitfield.count_zeros(), 5);
    }

    #[test]
    fn shl() -> TestResult {
        // 1 bit shift, easy case
        let bitfield: Tested1 = [0b00000001].into();

        assert_eq!(bitfield << 1.try_into()?, [0b00000010].into());

        let mut bitfield: Tested1 = [0b00000001].into();
        bitfield <<= 1.try_into()?;

        assert_eq!(bitfield, [0b00000010].into());

        // 7 bit shift, crossing the boundary case
        let bitfield: Tested2 = [0b00011011, 0b11101000].into();

        assert_eq!(bitfield << 7.try_into()?, [0b11110100, 0b00000000].into());

        let mut bitfield: Tested2 = [0b00011011, 0b11101000].into();
        bitfield <<= 7.try_into()?;

        assert_eq!(bitfield, [0b11110100, 0b00000000].into());

        // 9 bit shift, bigger, than chunk length
        let bitfield: Tested2 = [0b00011011, 0b11101000].into();

        assert_eq!(bitfield << 9.try_into()?, [0b11010000, 0b00000000].into());

        let mut bitfield: Tested2 = [0b00011011, 0b11101000].into();
        bitfield <<= 9.try_into()?;

        assert_eq!(bitfield, [0b11010000, 0b00000000].into());
        Ok(())
    }

    #[test]
    fn shr() -> TestResult {
        // 1 bit shift, easy case
        let bitfield: Tested1 = [0b00000010].into();

        assert_eq!(bitfield >> 1.try_into()?, [0b00000001].into());

        let mut bitfield: Tested1 = [0b00000010].into();
        bitfield >>= 1.try_into()?;

        assert_eq!(bitfield, [0b00000001].into());

        // 7 bit shift, crossing the boundary case
        let bitfield: Tested2 = [0b11110100, 0b00000000].into();

        assert_eq!(bitfield >> 7.try_into()?, [0b00000001, 0b11101000].into());

        let mut bitfield: Tested2 = [0b11110100, 0b00000000].into();
        bitfield >>= 7.try_into()?;

        assert_eq!(bitfield, [0b00000001, 0b11101000].into());

        // 9 bit shift, bigger, than chunk length
        let bitfield: Tested2 = [0b11010000, 0b00000000].into();

        assert_eq!(bitfield >> 9.try_into()?, [0b00000000, 0b01101000].into());

        let mut bitfield: Tested2 = [0b11010000, 0b00000000].into();
        bitfield >>= 9.try_into()?;

        assert_eq!(bitfield, [0b00000000, 0b01101000].into());
        Ok(())
    }

    #[test]
    fn not() {
        let a: Tested1 = [0b11110000].into();

        assert_eq!(!a, [0b00001111].into());
    }

    #[test]
    fn bit_and() {
        let a: Tested1 = [0b11110000].into();
        let b: Tested1 = [0b11001100].into();

        assert_eq!(a & b, [0b11000000].into());

        let mut a: Tested1 = [0b11110000].into();
        let b: Tested1 = [0b11001100].into();
        a &= b;

        assert_eq!(a, [0b11000000].into());
    }

    #[test]
    fn bit_or() {
        let a: Tested1 = [0b11110000].into();
        let b: Tested1 = [0b11001100].into();

        assert_eq!(a | b, [0b11111100].into());

        let mut a: Tested1 = [0b11110000].into();
        let b: Tested1 = [0b11001100].into();
        a |= b;

        assert_eq!(a, [0b11111100].into());
    }

    #[test]
    fn bit_xor() {
        let a: Tested1 = [0b11110000].into();
        let b: Tested1 = [0b11001100].into();

        assert_eq!(a ^ b, [0b00111100].into());

        let mut a: Tested1 = [0b11110000].into();
        let b: Tested1 = [0b11001100].into();
        a ^= b;

        assert_eq!(a, [0b00111100].into());
    }

    #[test]
    fn complement() {
        let a: Tested1 = [0b11110000].into();

        assert_eq!(a.complement(), [0b00001111].into());
    }

    #[test]
    fn intersection() {
        let a: Tested1 = [0b11110000].into();
        let b: Tested1 = [0b11001100].into();

        assert_eq!(a.intersection(b), [0b11000000].into());
    }

    #[test]
    fn union() {
        let a: Tested1 = [0b11110000].into();
        let b: Tested1 = [0b11001100].into();

        assert_eq!(a.union(b), [0b11111100].into());
    }

    #[test]
    fn difference() {
        let a: Tested1 = [0b11110000].into();
        let b: Tested1 = [0b11001100].into();

        assert_eq!(a.difference(b), [0b00110000].into());
    }

    #[test]
    fn sym_difference() {
        let a: Tested1 = [0b11110000].into();
        let b: Tested1 = [0b11001100].into();

        assert_eq!(a.sym_difference(b), [0b00111100].into());
    }

    #[test]
    fn bits() {
        let bitfield: Tested1 = [0b11110000].into();
        let mut iter = bitfield.bits();

        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn bits_ref() {
        let bitfield: Tested1 = [0b11110000].into();
        let mut iter = bitfield.bits_ref();

        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn bits_mut() {
        let mut bitfield: Tested1 = [0b11110000].into();

        let mut iter = bitfield.bits_ref();

        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&false));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));
        assert_eq!(iter.next().as_deref(), Some(&true));
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
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn collect_from_bits() {
        let a: Tested1 = [0b11110000].into();
        let iter = a.bits();
        let b: Tested1 = iter.collect();

        assert_eq!(b, [0b11110000].into());

        let arr = [true, false, true, false, true, false, true, false];
        let bitfield: Tested1 = arr
            .into_iter()
            // Need to reverse to get the same visual representation, because
            // array's .into_iter() makes iterator from left to right,
            // but .collect() will collect from right to left here.
            .rev()
            .collect();

        assert_eq!(bitfield, [0b10101010].into());
    }

    #[test]
    fn ones() -> TestResult {
        let bitfield: Tested1 = [0b11110000].into();
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
        let bitfield: Tested1 = [0b11110000].into();
        let mut iter = bitfield.zeros();

        assert_eq!(iter.next(), Some(0.try_into()?));
        assert_eq!(iter.next(), Some(1.try_into()?));
        assert_eq!(iter.next(), Some(2.try_into()?));
        assert_eq!(iter.next(), Some(3.try_into()?));
        assert_eq!(iter.next(), None);
        Ok(())
    }

    #[test]
    fn from_slice_bool() {
        // Same index order
        let slice: &[bool] = &[true, false, true, false, true, false, true, false];
        let bitfield: Tested1 = Tested1::from_bits_ref(slice);

        assert_eq!(bitfield, [0b01010101].into());
    }

    #[test]
    fn test_send() {
        fn assert_send<T: Send>() {}
        assert_send::<Tested1>();
    }

    #[test]
    fn test_sync() {
        fn assert_sync<T: Sync>() {}
        assert_sync::<Tested1>();
    }

    #[test]
    fn expand() -> TestResult {
        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2: Tested2 = bitfield1.expand()?;

        let mut arr = [0; 2];
        arr[0] = 0b00011011;
        assert_eq!(bitfield2, Tested2::from(arr));

        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2: Tested4 = bitfield1.expand()?;

        let mut arr = [0; 4];
        arr[0] = 0b00011011;
        assert_eq!(bitfield2, Tested4::from(arr));

        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2: Tested8 = bitfield1.expand()?;

        let mut arr = [0; 8];
        arr[0] = 0b00011011;
        assert_eq!(bitfield2, Tested8::from(arr));

        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2: Tested16 = bitfield1.expand()?;

        let mut arr = [0; 16];
        arr[0] = 0b00011011;
        assert_eq!(bitfield2, Tested16::from(arr));

        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2: TestedOdd = bitfield1.expand()?;

        let mut arr = [0; 3];
        arr[0] = 0b00011011;
        assert_eq!(bitfield2, TestedOdd::from(arr));

        Ok(())
    }

    #[test]
    fn fast_expand() -> TestResult {
        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2: Tested2 = bitfield1.fast_expand()?;

        let mut arr = [0; 2];
        arr[0] = 0b00011011;
        assert_eq!(bitfield2, Tested2::from(arr));

        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2: Tested4 = bitfield1.fast_expand()?;

        let mut arr = [0; 4];
        arr[0] = 0b00011011;
        assert_eq!(bitfield2, Tested4::from(arr));

        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2: Tested8 = bitfield1.fast_expand()?;

        let mut arr = [0; 8];
        arr[0] = 0b00011011;
        assert_eq!(bitfield2, Tested8::from(arr));

        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2: Tested16 = bitfield1.fast_expand()?;

        let mut arr = [0; 16];
        arr[0] = 0b00011011;
        assert_eq!(bitfield2, Tested16::from(arr));

        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2: TestedOdd = bitfield1.fast_expand()?;

        let mut arr = [0; 3];
        arr[0] = 0b00011011;
        assert_eq!(bitfield2, TestedOdd::from(arr));

        Ok(())
    }

    #[test]
    fn combine() -> TestResult {
        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2 = Tested1::from([0b11101000]);

        let bitfield3: Tested2 = bitfield1.combine(bitfield2)?;

        assert_eq!(bitfield3, Tested2::from([0b00011011, 0b11101000]));

        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2 = Tested2::from([0b11011011, 0b11101000]);

        let bitfield3: TestedOdd = bitfield1.combine(bitfield2)?;

        assert_eq!(
            bitfield3,
            TestedOdd::from([0b00011011, 0b11011011, 0b11101000])
        );
        Ok(())
    }

    #[test]
    fn split() -> TestResult {
        let bitfield1 = Tested2::from([0b00011011, 0b11101000]);
        let (bitfield2, bitfield3): (Tested1, Tested1) = bitfield1.split()?;

        assert_eq!(bitfield2, Tested1::from([0b00011011]));
        assert_eq!(bitfield3, Tested1::from([0b11101000]));

        let bitfield1 = TestedOdd::from([0b00011011, 0b11011011, 0b11101000]);
        let (bitfield2, bitfield3): (Tested1, Tested2) = bitfield1.split()?;

        assert_eq!(bitfield2, Tested1::from([0b00011011]));
        assert_eq!(bitfield3, Tested2::from([0b11011011, 0b11101000]));
        Ok(())
    }

    #[test]
    fn fast_combine() -> TestResult {
        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2 = Tested1::from([0b11101000]);

        let bitfield3: Tested2 = bitfield1.fast_combine(bitfield2)?;

        assert_eq!(bitfield3, Tested2::from([0b00011011, 0b11101000]));

        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2 = Tested2::from([0b11011011, 0b11101000]);

        let bitfield3: TestedOdd = bitfield1.fast_combine(bitfield2)?;

        assert_eq!(
            bitfield3,
            TestedOdd::from([0b00011011, 0b11011011, 0b11101000])
        );
        Ok(())
    }

    #[test]
    fn fast_split() -> TestResult {
        let bitfield1 = Tested2::from([0b00011011, 0b11101000]);
        let (bitfield2, bitfield3): (Tested1, Tested1) = bitfield1.fast_split()?;

        assert_eq!(bitfield2, Tested1::from([0b00011011]));
        assert_eq!(bitfield3, Tested1::from([0b11101000]));

        let bitfield1 = TestedOdd::from([0b00011011, 0b11011011, 0b11101000]);
        let (bitfield2, bitfield3): (Tested1, Tested2) = bitfield1.fast_split()?;

        assert_eq!(bitfield2, Tested1::from([0b00011011]));
        assert_eq!(bitfield3, Tested2::from([0b11011011, 0b11101000]));
        Ok(())
    }

    #[test]
    fn display() {
        let bytefield = ByteField::<1>::from([170; 1]);
        println!("{bytefield}");

        println!("Binary representation: {:#0b}", bytefield);
        println!("Octal representation: {:#0o}", bytefield);
        println!("LowerHex representation: {:#0x}", bytefield);
        println!("UpperHex representation: {:#0X}", bytefield);

        let bytefield = ByteField::<2>::from([170; 2]);
        println!("{bytefield}");
        let bytefield = ByteField::<3>::from([170; 3]);
        println!("{bytefield}");
        let bytefield = ByteField::<4>::from([170; 4]);
        println!("{bytefield}");
        let bytefield = ByteField::<5>::from([170; 5]);
        println!("{bytefield}");
        let bytefield = ByteField::<6>::from([170; 6]);
        println!("{bytefield}");
        let bytefield = ByteField::<7>::from([170; 7]);
        println!("{bytefield}");
        let bytefield = ByteField::<8>::from([170; 8]);
        println!("{bytefield}");
    }
}
