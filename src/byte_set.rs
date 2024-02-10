//! Module containing [`Byteset`].

use crate::{
    bit::Bit,
    bitset::{Bitset, LeftAligned},
    prelude::Index,
};
use std::{
    fmt::{Binary, Debug, Display, LowerHex, Octal, UpperHex},
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
        ShrAssign,
    },
};

type Inner<const N: usize> = [u8; N];
type BIndex<const N: usize> = Index<Byteset<N>>;

const fn byte_index<const N: usize>(index: BIndex<N>) -> usize {
    index.into_inner() / 8
}

const fn bit_index<const N: usize>(index: BIndex<N>) -> usize {
    index.into_inner() % 8
}

const fn bitmask<const N: usize>(index: BIndex<N>) -> u8 {
    1 << bit_index(index)
}

/// [`Bitset`] of variable `size`.
/// `N` is size in bytes of the `Byteset`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Byteset<const N: usize>(pub(crate) Inner<N>);

impl<const N: usize> Byteset<N> {
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

unsafe impl<const N: usize> LeftAligned for Byteset<N> {
    type _Repr = Inner<N>;
    const _BYTE_SIZE: usize = N;
    const _ONE: Self = Self::__one();
    const _ALL: Self = Self([255; N]);
    const _NONE: Self = Self([0; N]);

    #[inline(always)]
    fn _new(value: Self::Repr) -> Self {
        Self(value)
    }
}

impl<const N: usize> From<Inner<N>> for Byteset<N> {
    #[inline(always)]
    fn from(value: Inner<N>) -> Self {
        Self(value)
    }
}

impl<const N: usize> From<Byteset<N>> for Inner<N> {
    #[inline(always)]
    fn from(value: Byteset<N>) -> Self {
        value.0
    }
}

impl<const N: usize> From<BIndex<N>> for Byteset<N> {
    fn from(index: BIndex<N>) -> Self {
        let mut inner = [0; N];
        inner[byte_index(index)] = bitmask(index);
        Self(inner)
    }
}

impl<const N: usize> Not for Byteset<N> {
    type Output = Self;

    fn not(mut self) -> Self::Output {
        for chunk in &mut self.0 {
            *chunk = !*chunk;
        }
        self
    }
}

impl<const N: usize> BitAnd for Byteset<N> {
    type Output = Self;

    fn bitand(mut self, rhs: Self) -> Self::Output {
        for (i, chunk) in self.0.iter_mut().enumerate() {
            *chunk &= rhs.0[i];
        }
        self
    }
}

impl<const N: usize> BitAndAssign for Byteset<N> {
    fn bitand_assign(&mut self, rhs: Self) {
        for (i, chunk) in self.0.iter_mut().enumerate() {
            *chunk &= rhs.0[i];
        }
    }
}

impl<const N: usize> BitOr for Byteset<N> {
    type Output = Self;

    fn bitor(mut self, rhs: Self) -> Self::Output {
        for (i, chunk) in self.0.iter_mut().enumerate() {
            *chunk |= rhs.0[i];
        }
        self
    }
}

impl<const N: usize> BitOrAssign for Byteset<N> {
    fn bitor_assign(&mut self, rhs: Self) {
        for (i, chunk) in self.0.iter_mut().enumerate() {
            *chunk |= rhs.0[i];
        }
    }
}

impl<const N: usize> BitXor for Byteset<N> {
    type Output = Self;

    fn bitxor(mut self, rhs: Self) -> Self::Output {
        for (i, chunk) in self.0.iter_mut().enumerate() {
            *chunk ^= rhs.0[i];
        }
        self
    }
}

impl<const N: usize> BitXorAssign for Byteset<N> {
    fn bitxor_assign(&mut self, rhs: Self) {
        for (i, chunk) in self.0.iter_mut().enumerate() {
            *chunk ^= rhs.0[i];
        }
    }
}

impl<const N: usize> Shl<BIndex<N>> for Byteset<N> {
    type Output = Self;

    fn shl(self, rhs: BIndex<N>) -> Self::Output {
        Self::shift_left(self, rhs)
    }
}

impl<const N: usize> ShlAssign<BIndex<N>> for Byteset<N> {
    fn shl_assign(&mut self, rhs: BIndex<N>) {
        let byte_shift = byte_index(rhs);
        let bit_shift = bit_index(rhs);

        let ptr = self as *mut _ as *mut u8;

        if byte_shift > 0 {
            unsafe {
                std::ptr::copy(ptr.add(byte_shift), ptr, Self::BYTE_SIZE - byte_shift);
                std::ptr::write_bytes(ptr.add(Self::BYTE_SIZE - byte_shift), 0, byte_shift);
            }
        }

        if bit_shift > 0 {
            let bytes: &mut [u8] = unsafe { std::slice::from_raw_parts_mut(ptr, Self::BYTE_SIZE) };
            let mut carry = 0;
            for byte in bytes.iter_mut().rev() {
                let shifted = *byte << bit_shift | carry;
                carry = *byte >> (8 - bit_shift);
                *byte = shifted;
            }
        }
    }
}

impl<const N: usize> Shr<BIndex<N>> for Byteset<N> {
    type Output = Self;

    fn shr(self, rhs: BIndex<N>) -> Self::Output {
        Self::shift_right(self, rhs)
    }
}

impl<const N: usize> ShrAssign<BIndex<N>> for Byteset<N> {
    fn shr_assign(&mut self, rhs: BIndex<N>) {
        let byte_shift = byte_index(rhs);
        let bit_shift = bit_index(rhs);

        let ptr = self as *mut _ as *mut u8;

        if byte_shift > 0 {
            unsafe {
                std::ptr::copy(ptr, ptr.add(byte_shift), Self::BYTE_SIZE - byte_shift);
                std::ptr::write_bytes(ptr, 0, byte_shift);
            }
        }

        if bit_shift > 0 {
            let bytes: &mut [u8] = unsafe { std::slice::from_raw_parts_mut(ptr, Self::BYTE_SIZE) };
            let mut carry = 0;
            for byte in bytes.iter_mut() {
                let shifted = *byte >> bit_shift | carry;
                carry = *byte << (8 - bit_shift);
                *byte = shifted;
            }
        }
    }
}

impl<const N: usize> BitAnd<BIndex<N>> for Byteset<N> {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: BIndex<N>) -> Self::Output {
        self & Self::from(rhs)
    }
}

impl<const N: usize> BitAndAssign<BIndex<N>> for Byteset<N> {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: BIndex<N>) {
        *self &= Self::from(rhs);
    }
}

impl<const N: usize> BitOr<BIndex<N>> for Byteset<N> {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: BIndex<N>) -> Self::Output {
        self | Self::from(rhs)
    }
}

impl<const N: usize> BitOrAssign<BIndex<N>> for Byteset<N> {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: BIndex<N>) {
        *self |= Self::from(rhs);
    }
}

impl<const N: usize> BitXor<BIndex<N>> for Byteset<N> {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: BIndex<N>) -> Self::Output {
        self ^ Self::from(rhs)
    }
}

impl<const N: usize> BitXorAssign<BIndex<N>> for Byteset<N> {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: BIndex<N>) {
        *self ^= Self::from(rhs);
    }
}

impl<const N: usize> FromIterator<Bit> for Byteset<N> {
    fn from_iter<T: IntoIterator<Item = Bit>>(iter: T) -> Self {
        iter.into_iter()
            .take(N * 8)
            .enumerate()
            .filter_map(|(i, bit)| if bool::from(bit) { Some(i) } else { None })
            .filter_map(|i| BIndex::try_from(i).ok())
            .fold(Self::NONE, |acc, i| acc | Self::__one() << i)
    }
}

impl<const N: usize> Debug for Byteset<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = self
            .0
            .iter()
            .fold("Byteset([".to_owned(), |mut acc, &chunk| {
                acc.push_str(&format!(" {:08b}", chunk));
                acc
            });
        s.push_str(" ])");
        write!(f, "{s}")
    }
}

impl<const N: usize> Display for Byteset<N> {
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

impl<const N: usize> Binary for Byteset<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.0.iter().fold("".to_owned(), |mut acc, &chunk| {
            acc.push_str(&format!("{:08b}", chunk));
            acc
        });
        write!(f, "{s}")
    }
}

impl<const N: usize> Octal for Byteset<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.0.iter().fold("".to_owned(), |mut acc, &chunk| {
            acc.push_str(&format!("{:03o}", chunk));
            acc
        });
        write!(f, "{s}")
    }
}

impl<const N: usize> UpperHex for Byteset<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.0.iter().fold("".to_owned(), |mut acc, &chunk| {
            acc.push_str(&format!("{:02X}", chunk));
            acc
        });
        write!(f, "{s}")
    }
}

impl<const N: usize> LowerHex for Byteset<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.0.iter().fold("".to_owned(), |mut acc, &chunk| {
            acc.push_str(&format!("{:02x}", chunk));
            acc
        });
        write!(f, "{s}")
    }
}

#[cfg(feature = "serde")]
impl<const N: usize> serde::Serialize for Byteset<N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_bytes(&self.0)
    }
}

#[cfg(feature = "serde")]
impl<'de, const N: usize> serde::Deserialize<'de> for Byteset<N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct BytesetVisitor<const M: usize>;

        impl<'de, const M: usize> serde::de::Visitor<'de> for BytesetVisitor<M> {
            type Value = Byteset<M>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("a byte array")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                if v.len() != M {
                    return Err(serde::de::Error::invalid_length(
                        v.len(),
                        &format!("array of length {}", M).as_str(),
                    ));
                }
                let mut bytes = [0; M];
                bytes.copy_from_slice(v);
                Ok(Byteset(bytes))
            }
        }

        deserializer.deserialize_bytes(BytesetVisitor::<N>)
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use crate::{bit::Bit::*, prelude::Bitset};

    use super::*;
    type Tested1 = Byteset<1>;
    type Tested2 = Byteset<2>;
    type Tested4 = Byteset<4>;
    type Tested8 = Byteset<8>;
    type Tested16 = Byteset<16>;

    type TestedOdd = Byteset<3>;

    type TestResult = Result<(), Box<dyn Error>>;

    #[test]
    fn construction() -> TestResult {
        let bitset = Tested1::NONE
            .clone()
            .set_bit(0.try_into()?, One)
            .check_bit(1.try_into()?)
            .uncheck_bit(0.try_into()?)
            .build();

        assert_eq!(bitset, [0b00000010].into());
        Ok(())
    }

    #[test]
    fn conversion_from_arr() {
        let bitset: Tested1 = [0b10101010].into();

        assert_eq!(bitset.0, [0b10101010]);
    }

    #[test]
    fn conversion_from_index() {
        let bitset = Tested1::from(Index::<Tested1>::MIN);

        assert_eq!(bitset.0, [1]);
    }

    #[test]
    fn into_inner() {
        let bitset: Tested1 = [0b10101010].into();

        assert_eq!(bitset.0, bitset.into_inner());
    }

    #[test]
    fn bit_set_to_true() -> TestResult {
        let mut bitset: Tested1 = [0b10101010].into();

        bitset.set_bit(6.try_into()?, One);

        assert_eq!(bitset.0, [0b11101010]);
        Ok(())
    }

    #[test]
    fn bit_set_to_false() -> TestResult {
        let mut bitset: Tested1 = [0b10101010].into();

        bitset.set_bit(7.try_into()?, Zero);

        assert_eq!(bitset.0, [0b00101010]);
        Ok(())
    }

    // #[test]
    // fn bit() -> TestResult {
    //     let bitset: Tested1 = [0b10101010].into();

    //     assert_eq!(bitset.bit(0.try_into()?), Zero);
    //     assert_eq!(bitset.bit(1.try_into()?), One);
    //     Ok(())
    // }

    #[test]
    fn bit_check() -> TestResult {
        let mut bitset: Tested1 = [0b10101010].into();

        bitset.check_bit(6.try_into()?);

        assert_eq!(bitset.0, [0b11101010]);
        Ok(())
    }

    #[test]
    fn bit_uncheck() -> TestResult {
        let mut bitset: Tested1 = [0b10101010].into();

        bitset.uncheck_bit(7.try_into()?);

        assert_eq!(bitset.0, [0b00101010]);
        Ok(())
    }

    #[test]
    fn bit_ref() -> TestResult {
        let bitset: Tested1 = [0b10101010].into();

        assert_eq!(*bitset.bit_ref(0.try_into()?), Zero);
        assert_eq!(*bitset.bit_ref(1.try_into()?), One);
        Ok(())
    }

    #[test]
    fn bit_mut() -> TestResult {
        let mut bitset: Tested1 = [0b10101010].into();

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
        let bitset: Tested1 = [0b11100000].into();

        assert_eq!(bitset.count_ones(), 3);
    }

    #[test]
    fn count_zeros() {
        let bitset: Tested1 = [0b11100000].into();

        assert_eq!(bitset.count_zeros(), 5);
    }

    #[test]
    fn shl() -> TestResult {
        // 1 bit shift, easy case
        let bitset: Tested1 = [0b00000001].into();

        assert_eq!(bitset << 1.try_into()?, [0b00000010].into());

        let mut bitset: Tested1 = [0b00000001].into();
        bitset <<= 1.try_into()?;

        assert_eq!(bitset, [0b00000010].into());

        // 7 bit shift, crossing the boundary case
        let bitset: Tested2 = [0b00011011, 0b11101000].into();

        assert_eq!(bitset << 7.try_into()?, [0b11110100, 0b00000000].into());

        let mut bitset: Tested2 = [0b00011011, 0b11101000].into();
        bitset <<= 7.try_into()?;

        assert_eq!(bitset, [0b11110100, 0b00000000].into());

        // 9 bit shift, bigger, than chunk length
        let bitset: Tested2 = [0b00011011, 0b11101000].into();

        assert_eq!(bitset << 9.try_into()?, [0b11010000, 0b00000000].into());

        let mut bitset: Tested2 = [0b00011011, 0b11101000].into();
        bitset <<= 9.try_into()?;

        assert_eq!(bitset, [0b11010000, 0b00000000].into());
        Ok(())
    }

    #[test]
    fn shr() -> TestResult {
        // 1 bit shift, easy case
        let bitset: Tested1 = [0b00000010].into();

        assert_eq!(bitset >> 1.try_into()?, [0b00000001].into());

        let mut bitset: Tested1 = [0b00000010].into();
        bitset >>= 1.try_into()?;

        assert_eq!(bitset, [0b00000001].into());

        // 7 bit shift, crossing the boundary case
        let bitset: Tested2 = [0b11110100, 0b00000000].into();

        assert_eq!(bitset >> 7.try_into()?, [0b00000001, 0b11101000].into());

        let mut bitset: Tested2 = [0b11110100, 0b00000000].into();
        bitset >>= 7.try_into()?;

        assert_eq!(bitset, [0b00000001, 0b11101000].into());

        // 9 bit shift, bigger, than chunk length
        let bitset: Tested2 = [0b11010000, 0b00000000].into();

        assert_eq!(bitset >> 9.try_into()?, [0b00000000, 0b01101000].into());

        let mut bitset: Tested2 = [0b11010000, 0b00000000].into();
        bitset >>= 9.try_into()?;

        assert_eq!(bitset, [0b00000000, 0b01101000].into());
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
    fn bits_ref() {
        let bitset: Tested1 = [0b11110000].into();
        let mut iter = bitset.bits_ref();

        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn bits_mut() {
        let mut bitset: Tested1 = [0b11110000].into();

        let mut iter = bitset.bits_ref();

        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&Zero));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));
        assert_eq!(iter.next().as_deref(), Some(&One));
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
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn collect_from_bits() {
        let a: Tested1 = [0b11110000].into();
        let iter = a.bits_ref();
        let b: Tested1 = iter.map(|b| *b).collect();

        assert_eq!(b, [0b11110000].into());

        let arr = [One, Zero, One, Zero, One, Zero, One, Zero];
        let bitset: Tested1 = arr
            .into_iter()
            // Need to reverse to get the same visual representation, because
            // array's .into_iter() makes iterator from left to right,
            // but .collect() will collect from right to left here.
            .rev()
            .collect();

        assert_eq!(bitset, [0b10101010].into());
    }

    #[test]
    fn ones() -> TestResult {
        let bitset: Tested1 = [0b11110000].into();
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
        let bitset: Tested1 = [0b11110000].into();
        let mut iter = bitset.zeros();

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
        let slice: &[Bit] = &[One, Zero, One, Zero, One, Zero, One, Zero];
        let bitset: Tested1 = Tested1::from_bits_col(slice);

        assert_eq!(bitset, [0b01010101].into());
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
        let bitset1 = Tested1::from([0b00011011]);
        let bitset2: Tested2 = bitset1.expand()?;

        let mut arr = [0; 2];
        arr[0] = 0b00011011;
        assert_eq!(bitset2, Tested2::from(arr));

        let bitset1 = Tested1::from([0b00011011]);
        let bitset2: Tested4 = bitset1.expand()?;

        let mut arr = [0; 4];
        arr[0] = 0b00011011;
        assert_eq!(bitset2, Tested4::from(arr));

        let bitset1 = Tested1::from([0b00011011]);
        let bitset2: Tested8 = bitset1.expand()?;

        let mut arr = [0; 8];
        arr[0] = 0b00011011;
        assert_eq!(bitset2, Tested8::from(arr));

        let bitset1 = Tested1::from([0b00011011]);
        let bitset2: Tested16 = bitset1.expand()?;

        let mut arr = [0; 16];
        arr[0] = 0b00011011;
        assert_eq!(bitset2, Tested16::from(arr));

        let bitset1 = Tested1::from([0b00011011]);
        let bitset2: TestedOdd = bitset1.expand()?;

        let mut arr = [0; 3];
        arr[0] = 0b00011011;
        assert_eq!(bitset2, TestedOdd::from(arr));

        Ok(())
    }

    #[test]
    fn fast_expand() -> TestResult {
        let bitset1 = Tested1::from([0b00011011]);
        let bitset2: Tested2 = bitset1.expand_optimized()?;

        let mut arr = [0; 2];
        arr[0] = 0b00011011;
        assert_eq!(bitset2, Tested2::from(arr));

        let bitset1 = Tested1::from([0b00011011]);
        let bitset2: Tested4 = bitset1.expand_optimized()?;

        let mut arr = [0; 4];
        arr[0] = 0b00011011;
        assert_eq!(bitset2, Tested4::from(arr));

        let bitset1 = Tested1::from([0b00011011]);
        let bitset2: Tested8 = bitset1.expand_optimized()?;

        let mut arr = [0; 8];
        arr[0] = 0b00011011;
        assert_eq!(bitset2, Tested8::from(arr));

        let bitset1 = Tested1::from([0b00011011]);
        let bitset2: Tested16 = bitset1.expand_optimized()?;

        let mut arr = [0; 16];
        arr[0] = 0b00011011;
        assert_eq!(bitset2, Tested16::from(arr));

        let bitset1 = Tested1::from([0b00011011]);
        let bitset2: TestedOdd = bitset1.expand_optimized()?;

        let mut arr = [0; 3];
        arr[0] = 0b00011011;
        assert_eq!(bitset2, TestedOdd::from(arr));

        Ok(())
    }

    #[test]
    fn combine() -> TestResult {
        let bitset1 = Tested1::from([0b00011011]);
        let bitset2 = Tested1::from([0b11101000]);

        let bitset3: Tested2 = bitset1.combine(bitset2)?;

        assert_eq!(bitset3, Tested2::from([0b00011011, 0b11101000]));

        let bitset1 = Tested1::from([0b00011011]);
        let bitset2 = Tested2::from([0b11011011, 0b11101000]);

        let bitset3: TestedOdd = bitset1.combine(bitset2)?;

        assert_eq!(
            bitset3,
            TestedOdd::from([0b00011011, 0b11011011, 0b11101000])
        );
        Ok(())
    }

    #[test]
    fn split() -> TestResult {
        let bitset1 = Tested2::from([0b00011011, 0b11101000]);
        let (bitset2, bitset3): (Tested1, Tested1) = bitset1.split()?;

        assert_eq!(bitset2, Tested1::from([0b00011011]));
        assert_eq!(bitset3, Tested1::from([0b11101000]));

        let bitset1 = TestedOdd::from([0b00011011, 0b11011011, 0b11101000]);
        let (bitset2, bitset3): (Tested1, Tested2) = bitset1.split()?;

        assert_eq!(bitset2, Tested1::from([0b00011011]));
        assert_eq!(bitset3, Tested2::from([0b11011011, 0b11101000]));
        Ok(())
    }

    #[test]
    fn fast_combine() -> TestResult {
        let bitset1 = Tested1::from([0b00011011]);
        let bitset2 = Tested1::from([0b11101000]);

        let bitset3: Tested2 = bitset1.combine_optimized(bitset2)?;

        assert_eq!(bitset3, Tested2::from([0b00011011, 0b11101000]));

        let bitset1 = Tested1::from([0b00011011]);
        let bitset2 = Tested2::from([0b11011011, 0b11101000]);

        let bitset3: TestedOdd = bitset1.combine_optimized(bitset2)?;

        assert_eq!(
            bitset3,
            TestedOdd::from([0b00011011, 0b11011011, 0b11101000])
        );
        Ok(())
    }

    #[test]
    fn fast_split() -> TestResult {
        let bitset1 = Tested2::from([0b00011011, 0b11101000]);
        let (bitset2, bitset3): (Tested1, Tested1) = bitset1.split_optimized()?;

        assert_eq!(bitset2, Tested1::from([0b00011011]));
        assert_eq!(bitset3, Tested1::from([0b11101000]));

        let bitset1 = TestedOdd::from([0b00011011, 0b11011011, 0b11101000]);
        let (bitset2, bitset3): (Tested1, Tested2) = bitset1.split_optimized()?;

        assert_eq!(bitset2, Tested1::from([0b00011011]));
        assert_eq!(bitset3, Tested2::from([0b11011011, 0b11101000]));
        Ok(())
    }

    #[test]
    fn display() {
        let byteset = Byteset::<1>::from([170; 1]);
        println!("{byteset}");

        println!("Binary representation: {:#0b}", byteset);
        println!("Octal representation: {:#0o}", byteset);
        println!("LowerHex representation: {:#0x}", byteset);
        println!("UpperHex representation: {:#0X}", byteset);

        let byteset = Byteset::<2>::from([170; 2]);
        println!("{byteset}");
        let byteset = Byteset::<3>::from([170; 3]);
        println!("{byteset}");
        let byteset = Byteset::<4>::from([170; 4]);
        println!("{byteset}");
        let byteset = Byteset::<5>::from([170; 5]);
        println!("{byteset}");
        let byteset = Byteset::<6>::from([170; 6]);
        println!("{byteset}");
        let byteset = Byteset::<7>::from([170; 7]);
        println!("{byteset}");
        let byteset = Byteset::<8>::from([170; 8]);
        println!("{byteset}");
    }
}
