use crate::{
    bitfield::Simple,
    prelude::{Bitfield, FlagsEnum, Index},
};
use std::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
    ShrAssign,
};

type Inner<const N: usize> = [u8; N];
type BIndex<const N: usize> = Index<BitfieldBytes<N>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BitfieldBytes<const N: usize>(pub(crate) Inner<N>);

impl<const N: usize> BitfieldBytes<N> {
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

impl<const N: usize> Bitfield for BitfieldBytes<N> {
    const BIT_SIZE: usize = N * 8;

    const ONE: Self = Self::__one();

    const NONE: Self = Self([0; N]);

    const ALL: Self = Self([255; N]);

    fn from_index(index: &BIndex<N>) -> Self {
        Self::from(*index)
    }

    fn from_flag<T>(flag: &T) -> Self
    where
        T: FlagsEnum<Bitfield = Self> + Copy,
        BIndex<N>: From<T>,
    {
        Self::from(BIndex::<N>::from(*flag))
    }

    fn count_ones(&self) -> usize {
        self.0
            .iter()
            .fold(0usize, |acc, &e| acc + e.count_ones() as usize)
    }

    fn count_zeros(&self) -> usize {
        self.0
            .iter()
            .fold(0usize, |acc, &e| acc + e.count_zeros() as usize)
    }

    fn set_bit(&mut self, Index::<Self>(index, ..): BIndex<N>, value: bool) -> &mut Self {
        let byte_index = index / 8;
        let bit_index = index % 8;
        if value {
            self.0[byte_index] |= 1 << bit_index;
        } else {
            self.0[byte_index] &= !(1 << bit_index);
        }
        self
    }

    fn check_bit(&mut self, Index::<Self>(index, ..): BIndex<N>) -> &mut Self {
        let byte_index = index / 8;
        let bit_index = index % 8;
        self.0[byte_index] |= 1 << bit_index;
        self
    }

    fn uncheck_bit(&mut self, Index::<Self>(index, ..): BIndex<N>) -> &mut Self {
        let byte_index = index / 8;
        let bit_index = index % 8;
        self.0[byte_index] &= !(1 << bit_index);
        self
    }

    fn bit(&self, Index::<Self>(index, ..): BIndex<N>) -> bool {
        let byte_index = index / 8;
        let bit_index = index % 8;
        let bit = 1 << bit_index;
        (self.0[byte_index] & bit) != 0
    }
}

unsafe impl<const N: usize> Simple for BitfieldBytes<N> {}

impl<const N: usize> From<Inner<N>> for BitfieldBytes<N> {
    #[inline(always)]
    fn from(value: Inner<N>) -> Self {
        Self(value)
    }
}

impl<const N: usize> From<BitfieldBytes<N>> for Inner<N> {
    #[inline(always)]
    fn from(value: BitfieldBytes<N>) -> Self {
        value.0
    }
}

impl<const N: usize> From<BIndex<N>> for BitfieldBytes<N> {
    fn from(Index::<Self>(index, ..): BIndex<N>) -> Self {
        let byte_index = index / 8;
        let bit_index = index % 8;
        let mut inner = [0; N];
        inner[byte_index] = 1 << bit_index;
        Self(inner)
    }
}

impl<const N: usize, T> From<T> for BitfieldBytes<N>
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex<N>: From<T>,
{
    #[inline(always)]
    fn from(value: T) -> Self {
        Self::from(BIndex::from(value))
    }
}

impl<const N: usize> Not for BitfieldBytes<N> {
    type Output = Self;

    fn not(mut self) -> Self::Output {
        for num in &mut self.0 {
            *num = !*num;
        }
        self
    }
}

impl<const N: usize> BitAnd for BitfieldBytes<N> {
    type Output = Self;

    fn bitand(mut self, rhs: Self) -> Self::Output {
        for (i, num) in self.0.iter_mut().enumerate() {
            *num &= rhs.0[i];
        }
        self
    }
}

impl<const N: usize> BitAndAssign for BitfieldBytes<N> {
    fn bitand_assign(&mut self, rhs: Self) {
        for (i, num) in self.0.iter_mut().enumerate() {
            *num &= rhs.0[i];
        }
    }
}

impl<const N: usize> BitOr for BitfieldBytes<N> {
    type Output = Self;

    fn bitor(mut self, rhs: Self) -> Self::Output {
        for (i, num) in self.0.iter_mut().enumerate() {
            *num |= rhs.0[i];
        }
        self
    }
}

impl<const N: usize> BitOrAssign for BitfieldBytes<N> {
    fn bitor_assign(&mut self, rhs: Self) {
        for (i, num) in self.0.iter_mut().enumerate() {
            *num |= rhs.0[i];
        }
    }
}

impl<const N: usize> BitXor for BitfieldBytes<N> {
    type Output = Self;

    fn bitxor(mut self, rhs: Self) -> Self::Output {
        for (i, num) in self.0.iter_mut().enumerate() {
            *num ^= rhs.0[i];
        }
        self
    }
}

impl<const N: usize> BitXorAssign for BitfieldBytes<N> {
    fn bitxor_assign(&mut self, rhs: Self) {
        for (i, num) in self.0.iter_mut().enumerate() {
            *num ^= rhs.0[i];
        }
    }
}

impl<const N: usize> Shl<BIndex<N>> for BitfieldBytes<N> {
    type Output = Self;

    fn shl(self, Index::<Self>(index, ..): BIndex<N>) -> Self::Output {
        let mut inner = self.0.clone();

        let byte_shift = index / 8;
        let bit_shift = index % 8;

        if byte_shift > 0 {
            for i in 0..N - byte_shift {
                inner[i] = self.0[i + byte_shift];
            }
            for i in N - byte_shift..N {
                inner[i] = 0;
            }
        }

        if bit_shift > 0 {
            let mut carry = 0;
            for i in 0..N {
                let shifted = self.0[i] << bit_shift | carry;
                carry = self.0[i] >> (8 - bit_shift);
                inner[i] = shifted;
            }
        }
        Self(inner)
    }
}

impl<const N: usize> ShlAssign<BIndex<N>> for BitfieldBytes<N> {
    fn shl_assign(&mut self, rhs: BIndex<N>) {
        *self = self.clone().shl(rhs);
    }
}

impl<const N: usize> Shr<BIndex<N>> for BitfieldBytes<N> {
    type Output = Self;

    fn shr(self, Index::<Self>(index, ..): BIndex<N>) -> Self::Output {
        let mut inner = self.0.clone();

        let byte_shift = index / 8;
        let bit_shift = index % 8;

        if byte_shift > 0 {
            for i in 0..N - byte_shift {
                inner[i + byte_shift] = self.0[i];
            }
            for i in 0..byte_shift {
                inner[i] = 0;
            }
        }

        if bit_shift > 0 {
            let mut carry = 0;
            for i in (0..N).rev() {
                let shifted = self.0[i] >> bit_shift | carry;
                carry = self.0[i] << (8 - bit_shift);
                inner[i] = shifted;
            }
        }
        Self(inner)
    }
}

impl<const N: usize> ShrAssign<BIndex<N>> for BitfieldBytes<N> {
    fn shr_assign(&mut self, rhs: BIndex<N>) {
        *self = self.clone().shr(rhs);
    }
}

impl<const N: usize> BitAnd<BIndex<N>> for BitfieldBytes<N> {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: BIndex<N>) -> Self::Output {
        self & Self::from(rhs)
    }
}

impl<const N: usize> BitAndAssign<BIndex<N>> for BitfieldBytes<N> {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: BIndex<N>) {
        *self &= Self::from(rhs);
    }
}

impl<const N: usize> BitOr<BIndex<N>> for BitfieldBytes<N> {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: BIndex<N>) -> Self::Output {
        self | Self::from(rhs)
    }
}

impl<const N: usize> BitOrAssign<BIndex<N>> for BitfieldBytes<N> {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: BIndex<N>) {
        *self |= Self::from(rhs);
    }
}

impl<const N: usize> BitXor<BIndex<N>> for BitfieldBytes<N> {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: BIndex<N>) -> Self::Output {
        self ^ Self::from(rhs)
    }
}

impl<const N: usize> BitXorAssign<BIndex<N>> for BitfieldBytes<N> {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: BIndex<N>) {
        *self ^= Self::from(rhs);
    }
}

impl<const N: usize, T> BitAnd<T> for BitfieldBytes<N>
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

impl<const N: usize, T> BitAndAssign<T> for BitfieldBytes<N>
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex<N>: From<T>,
{
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: T) {
        *self &= Self::from(rhs);
    }
}

impl<const N: usize, T> BitOr<T> for BitfieldBytes<N>
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

impl<const N: usize, T> BitOrAssign<T> for BitfieldBytes<N>
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex<N>: From<T>,
{
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: T) {
        *self |= Self::from(rhs);
    }
}

impl<const N: usize, T> BitXor<T> for BitfieldBytes<N>
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

impl<const N: usize, T> BitXorAssign<T> for BitfieldBytes<N>
where
    T: FlagsEnum<Bitfield = Self>,
    BIndex<N>: From<T>,
{
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: T) {
        *self ^= Self::from(rhs);
    }
}


impl<const N: usize> FromIterator<bool> for BitfieldBytes<N> {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        iter.into_iter()
            .take(N * 8)
            .enumerate()
            .filter_map(|(i, bit)| if bit { Some(i) } else { None })
            .filter_map(|i| BIndex::try_from(i).ok())
            .fold(Self::NONE, |acc, i| acc | Self::__one() << i)
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use super::*;
    type Tested1 = BitfieldBytes<1>;
    type Tested2 = BitfieldBytes<2>;
    type Tested4 = BitfieldBytes<4>;
    type Tested8 = BitfieldBytes<8>;
    type Tested16 = BitfieldBytes<16>;

    type TestedOdd = BitfieldBytes<3>;

    type TestResult = Result<(), Box<dyn Error>>;

    #[test]
    fn construction() -> TestResult {
        let bitfield = Tested1::new()
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
        let bitfield: Tested1 = [0b00000001].into();

        assert_eq!(bitfield << 1.try_into()?, [0b00000010].into());

        let mut bitfield: Tested1 = [0b00000001].into();
        bitfield <<= 1.try_into()?;

        assert_eq!(bitfield, [0b00000010].into());
        Ok(())
    }

    #[test]
    fn shr() -> TestResult {
        let bitfield: Tested1 = [0b00000010].into();

        assert_eq!(bitfield >> 1.try_into()?, [0b00000001].into());

        let mut bitfield: Tested1 = [0b00000010].into();
        bitfield >>= 1.try_into()?;

        assert_eq!(bitfield, [0b00000001].into());
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

        let bitfield3: Tested2 = bitfield1.combine(&bitfield2)?;

        assert_eq!(bitfield3, Tested2::from([0b00011011, 0b11101000]));

        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2 = Tested2::from([0b11011011, 0b11101000]);

        let bitfield3: TestedOdd = bitfield1.combine(&bitfield2)?;

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

        let bitfield3: Tested2 = bitfield1.fast_combine(&bitfield2)?;

        assert_eq!(bitfield3, Tested2::from([0b00011011, 0b11101000]));

        let bitfield1 = Tested1::from([0b00011011]);
        let bitfield2 = Tested2::from([0b11011011, 0b11101000]);

        let bitfield3: TestedOdd = bitfield1.fast_combine(&bitfield2)?;

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
}
