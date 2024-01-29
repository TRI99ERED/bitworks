use crate::{
    bitfield::Bitfield,
    iter::BitIter,
    private::{BitfieldHelper, BitfieldMarker},
};
use std::{
    fmt::Display,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not},
};

type Inner = u128;
const BITS: usize = 128;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub struct Bitfield128(Inner);

impl Bitfield128 {
    pub fn value(&self) -> Inner {
        self.0
    }
}

impl Bitfield<Inner> for Bitfield128 {
    fn count_set(&self) -> usize {
        self.0.count_ones() as usize
    }

    fn count_unset(&self) -> usize {
        self.0.count_zeros() as usize
    }

    fn first_set(&self) -> Option<usize> {
        if self.0.count_ones() == 0 {
            None
        } else {
            Some((self.0.trailing_zeros() + 1) as usize)
        }
    }

    fn last_set(&self) -> Option<usize> {
        if self.0.count_ones() == 0 {
            None
        } else {
            Some((BITS as u32 - self.0.leading_ones()) as usize)
        }
    }

    fn bit_iter(&self) -> impl Iterator<Item = bool> {
        self.into_iter()
    }
}

impl BitfieldMarker for Bitfield128 {}

impl BitfieldHelper<Inner> for Bitfield128 {
    const BIT: Inner = 1;
    const EMPTY: Inner = Inner::MIN;
    const ALL: Inner = Inner::MAX;
}

impl From<Inner> for Bitfield128 {
    fn from(value: Inner) -> Self {
        Self(value)
    }
}

impl Into<Inner> for Bitfield128 {
    fn into(self) -> Inner {
        self.0
    }
}

impl BitAnd for Bitfield128 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl BitAndAssign for Bitfield128 {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0
    }
}

impl BitOr for Bitfield128 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for Bitfield128 {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0
    }
}

impl BitXor for Bitfield128 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self(self.0 ^ rhs.0)
    }
}

impl BitXorAssign for Bitfield128 {
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0
    }
}

impl Not for Bitfield128 {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

impl Display for Bitfield128 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#0130b}", self.0)
    }
}

impl IntoIterator for Bitfield128 {
    type Item = bool;

    type IntoIter = BitIter<Inner>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            bitfield: self.0,
            index: 0,
        }
    }
}

impl FromIterator<bool> for Bitfield128 {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut bitfield: Self = Self::from(0);
        for (i, bit) in iter.into_iter().take(BITS).enumerate() {
            bitfield.0 |= (if bit { 1 } else { 0 }) << (i as Inner);
        }
        bitfield
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     fn a() -> [Option<Inner>; BITS] {
//         let mut a = [None; BITS];
//         a[1] = Some(1);
//         a[3] = Some(3);
//         a[5] = Some(5);
//         a[7] = Some(7);
//         a
//     }

//     fn b() -> [Option<Inner>; BITS] {
//         let mut b = [None; BITS];
//         b[0] = Some(0);
//         b[2] = Some(2);
//         b[4] = Some(4);
//         b[6] = Some(6);
//         b
//     }

//     fn c() -> [Option<Inner>; BITS] {
//         let mut c = [None; BITS];
//         c[2] = Some(2);
//         c[3] = Some(3);
//         c[7] = Some(7);
//         c
//     }

//     fn d() -> [Option<Inner>; BITS] {
//         let mut d = [None; BITS];
//         d[0] = Some(0);
//         d[2] = Some(2);
//         d[6] = Some(6);
//         d[7] = Some(7);
//         d
//     }

//     #[test]
//     fn conversion_from_array() {
//         let arr = a();
//         let bitfield = Bitfield128::from_flag_arr(&arr);

//         assert_eq!(
//             bitfield.0,
//             2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 * 2
//         );
//     }

//     #[test]
//     fn conversion_into_array() {
//         let bitfield = Bitfield128(1 + 2 * 2 + 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2);
//         let arr = bitfield.into_flag_arr();

//         assert_eq!(arr, b());
//     }

//     #[test]
//     fn conversion_from_integer() {
//         let bitfield: Bitfield128 = 170.into();

//         assert_eq!(bitfield.0, 170);
//     }

//     #[test]
//     fn flag_set_to_true() {
//         let arr = a();
//         let mut bitfield = Bitfield128::from_flag_arr(&arr);

//         bitfield.set_flag(6, true);

//         assert_eq!(
//             bitfield.0,
//             2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 * 2
//         );
//     }

//     #[test]
//     fn flag_set_to_false() {
//         let arr = a();
//         let mut bitfield = Bitfield128::from_flag_arr(&arr);

//         bitfield.set_flag(7, false);

//         assert_eq!(bitfield.0, 2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2);
//     }

//     #[test]
//     fn flag_check() {
//         let arr = a();
//         let mut bitfield = Bitfield128::from_flag_arr(&arr);

//         bitfield.check_flag(6);

//         assert_eq!(
//             bitfield.0,
//             2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 * 2
//         );
//     }

//     #[test]
//     fn flag_uncheck() {
//         let arr = a();
//         let mut bitfield = Bitfield128::from_flag_arr(&arr);

//         bitfield.uncheck_flag(7);

//         assert_eq!(bitfield.0, 2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2);
//     }

//     #[test]
//     fn bit_and() {
//         let a = Bitfield128::from_flag_arr(&a());
//         let b = Bitfield128::from_flag_arr(&b());

//         assert_eq!(a & b, 0.into());
//     }

//     #[test]
//     fn bit_or() {
//         let a = Bitfield128::from_flag_arr(&a());
//         let b = Bitfield128::from_flag_arr(&b());

//         assert_eq!(a | b, 255.into());
//     }

//     #[test]
//     fn bit_xor() {
//         let c = Bitfield128::from_flag_arr(&c());
//         let d = Bitfield128::from_flag_arr(&d());

//         assert_eq!(c ^ d, (1 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2).into());
//     }
// }
