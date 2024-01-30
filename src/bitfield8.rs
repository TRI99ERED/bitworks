use crate::{
    bitfield::Bitfield,
    iter::BitIter,
    private::{BitfieldHelper, BitfieldMarker},
};
use std::{
    fmt::Display,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not},
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

impl Bitfield<Inner> for Bitfield8 {
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

impl BitfieldMarker for Bitfield8 {}

impl BitfieldHelper<Inner> for Bitfield8 {
    const BIT: Inner = 1;

    const EMPTY: Inner = Inner::MIN;

    const ALL: Inner = Inner::MAX;
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

//     const A: [Option<Inner>; BITS] = [None, Some(1), None, Some(3), None, Some(5), None, Some(7)];
//     const B: [Option<Inner>; BITS] = [Some(0), None, Some(2), None, Some(4), None, Some(6), None];
//     const C: [Option<Inner>; BITS] = [None, None, Some(2), Some(3), None, None, None, Some(7)];
//     const D: [Option<Inner>; BITS] = [Some(0), None, Some(2), None, None, None, Some(6), Some(7)];

//     #[test]
//     fn conversion_from_array() {
//         let arr = A;
//         let bitfield = Bitfield8::from_flag_arr(&arr);

//         assert_eq!(
//             bitfield.0,
//             2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 * 2
//         );
//     }

//     #[test]
//     fn conversion_into_array() {
//         let bitfield = Bitfield8(1 + 2 * 2 + 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2);
//         let arr = bitfield.into_flag_arr();

//         assert_eq!(arr, B);
//     }

//     #[test]
//     fn conversion_from_integer() {
//         let bitfield: Bitfield8 = 170.into();

//         assert_eq!(bitfield.0, 170);
//     }

//     #[test]
//     fn flag_set_to_true() {
//         let arr = A;
//         let mut bitfield = Bitfield8::from_flag_arr(&arr);

//         bitfield.set_flag(6, true);

//         assert_eq!(
//             bitfield.0,
//             2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 * 2
//         );
//     }

//     #[test]
//     fn flag_set_to_false() {
//         let arr = A;
//         let mut bitfield = Bitfield8::from_flag_arr(&arr);

//         bitfield.set_flag(7, false);

//         assert_eq!(bitfield.0, 2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2);
//     }

//     #[test]
//     fn flag_check() {
//         let arr = A;
//         let mut bitfield = Bitfield8::from_flag_arr(&arr);

//         bitfield.check_flag(6);

//         assert_eq!(
//             bitfield.0,
//             2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 * 2
//         );
//     }

//     #[test]
//     fn flag_uncheck() {
//         let arr = A;
//         let mut bitfield = Bitfield8::from_flag_arr(&arr);

//         bitfield.uncheck_flag(7);

//         assert_eq!(bitfield.0, 2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2);
//     }

//     #[test]
//     fn bit_and() {
//         let a = Bitfield8::from_flag_arr(&A);
//         let b = Bitfield8::from_flag_arr(&B);

//         assert_eq!(a & b, 0.into());
//     }

//     #[test]
//     fn bit_or() {
//         let a = Bitfield8::from_flag_arr(&A);
//         let b = Bitfield8::from_flag_arr(&B);

//         assert_eq!(a | b, 255.into());
//     }

//     #[test]
//     fn bit_xor() {
//         let c = Bitfield8::from_flag_arr(&C);
//         let d = Bitfield8::from_flag_arr(&D);

//         assert_eq!(c ^ d, (1 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2).into());
//     }
// }
