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
pub struct Bitfield64(u64);

impl Bitfield64 {
    pub fn value(&self) -> u64 {
        self.0
    }
}

impl Bitfield<u64> for Bitfield64 {}

impl BitfieldMarker for Bitfield64 {}

impl BitfieldHelper<u64> for Bitfield64 {
    const BIT: u64 = 1;
    const EMPTY: u64 = u64::MIN;
    const ALL: u64 = u64::MAX;
}

impl From<u64> for Bitfield64 {
    fn from(value: u64) -> Self {
        Self(value)
    }
}

impl Into<u64> for Bitfield64 {
    fn into(self) -> u64 {
        self.0
    }
}

impl BitAnd for Bitfield64 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl BitAndAssign for Bitfield64 {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0
    }
}

impl BitOr for Bitfield64 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for Bitfield64 {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0
    }
}

impl BitXor for Bitfield64 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self(self.0 ^ rhs.0)
    }
}

impl BitXorAssign for Bitfield64 {
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0
    }
}

impl Not for Bitfield64 {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

impl Display for Bitfield64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#066b}", self.0)
    }
}

impl IntoIterator for Bitfield64 {
    type Item = bool;

    type IntoIter = BitIter<u64>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            bitfield: self.0,
            index: 0,
        }
    }
}

impl FromIterator<bool> for Bitfield64 {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut bitfield: Self = Self::from(0);
        for (i, bit) in iter.into_iter().take(64).enumerate() {
            bitfield.0 |=  (if bit {1} else {0}) << (i as u64);
        }
        bitfield
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     fn a() -> [Option<u64>; 64] {
//         let mut a = [None; 64];
//         a[1] = Some(1);
//         a[3] = Some(3);
//         a[5] = Some(5);
//         a[7] = Some(7);
//         a
//     }

//     fn b() -> [Option<u64>; 64] {
//         let mut b = [None; 64];
//         b[0] = Some(0);
//         b[2] = Some(2);
//         b[4] = Some(4);
//         b[6] = Some(6);
//         b
//     }

//     fn c() -> [Option<u64>; 64] {
//         let mut c = [None; 64];
//         c[2] = Some(2);
//         c[3] = Some(3);
//         c[7] = Some(7);
//         c
//     }

//     fn d() -> [Option<u64>; 64] {
//         let mut d = [None; 64];
//         d[0] = Some(0);
//         d[2] = Some(2);
//         d[6] = Some(6);
//         d[7] = Some(7);
//         d
//     }

//     #[test]
//     fn conversion_from_array() {
//         let arr = a();
//         let bitfield = Bitfield64::from_flag_arr(&arr);

//         assert_eq!(
//             bitfield.0,
//             2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 * 2
//         );
//     }

//     #[test]
//     fn conversion_into_array() {
//         let bitfield = Bitfield64(1 + 2 * 2 + 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2);
//         let arr = bitfield.into_flag_arr();

//         assert_eq!(arr, b());
//     }

//     #[test]
//     fn conversion_from_integer() {
//         let bitfield: Bitfield64 = 170.into();

//         assert_eq!(bitfield.0, 170);
//     }

//     #[test]
//     fn flag_set_to_true() {
//         let arr = a();
//         let mut bitfield = Bitfield64::from_flag_arr(&arr);

//         bitfield.set_flag(6, true);

//         assert_eq!(
//             bitfield.0,
//             2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 * 2
//         );
//     }

//     #[test]
//     fn flag_set_to_false() {
//         let arr = a();
//         let mut bitfield = Bitfield64::from_flag_arr(&arr);

//         bitfield.set_flag(7, false);

//         assert_eq!(bitfield.0, 2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2);
//     }

//     #[test]
//     fn flag_check() {
//         let arr = a();
//         let mut bitfield = Bitfield64::from_flag_arr(&arr);

//         bitfield.check_flag(6);

//         assert_eq!(
//             bitfield.0,
//             2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2 * 2
//         );
//     }

//     #[test]
//     fn flag_uncheck() {
//         let arr = a();
//         let mut bitfield = Bitfield64::from_flag_arr(&arr);

//         bitfield.uncheck_flag(7);

//         assert_eq!(bitfield.0, 2 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2);
//     }

//     #[test]
//     fn bit_and() {
//         let a = Bitfield64::from_flag_arr(&a());
//         let b = Bitfield64::from_flag_arr(&b());

//         assert_eq!(a & b, 0.into());
//     }

//     #[test]
//     fn bit_or() {
//         let a = Bitfield64::from_flag_arr(&a());
//         let b = Bitfield64::from_flag_arr(&b());

//         assert_eq!(a | b, 255.into());
//     }

//     #[test]
//     fn bit_xor() {
//         let c = Bitfield64::from_flag_arr(&c());
//         let d = Bitfield64::from_flag_arr(&d());

//         assert_eq!(c ^ d, (1 + 2 * 2 * 2 + 2 * 2 * 2 * 2 * 2 * 2).into());
//     }
// }
