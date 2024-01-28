use crate::{
    bitfield::Bitfield,
    iter::BitIter,
    private::{BitfieldHelper, BitfieldMarker},
};
use std::{
    fmt::Display,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not},
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub struct Bitfield8(u8);

impl Bitfield8 {
    pub fn value(&self) -> u8 {
        self.0
    }
}

impl Bitfield<u8> for Bitfield8 {}

impl BitfieldMarker for Bitfield8 {}

impl BitfieldHelper<u8> for Bitfield8 {
    const BIT: u8 = 1;

    const EMPTY: u8 = u8::MIN;

    const ALL: u8 = u8::MAX;
}

impl From<u8> for Bitfield8 {
    fn from(value: u8) -> Self {
        Self(value)
    }
}

impl Into<u8> for Bitfield8 {
    fn into(self) -> u8 {
        self.0
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

    type IntoIter = BitIter<u8>;

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
        for (i, bit) in iter.into_iter().take(8).enumerate() {
            bitfield.0 |=  (if bit {1} else {0}) << (i as u8);
        }
        bitfield
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     const A: [Option<u8>; 8] = [None, Some(1), None, Some(3), None, Some(5), None, Some(7)];
//     const B: [Option<u8>; 8] = [Some(0), None, Some(2), None, Some(4), None, Some(6), None];
//     const C: [Option<u8>; 8] = [None, None, Some(2), Some(3), None, None, None, Some(7)];
//     const D: [Option<u8>; 8] = [Some(0), None, Some(2), None, None, None, Some(6), Some(7)];

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
