use crate::bitfield::Bitfield;

pub trait Flagenum: Sized + TryFrom<<Self::Bitfield as Bitfield>::Repr>
where
    Self::Bitfield: Sized + Bitfield + From<Self>,
    <Self::Bitfield as Bitfield>::Repr:
        Sized + From<Self> + PartialOrd + Ord + PartialEq + Eq + TryFrom<usize>,
{
    type Bitfield;
    const COUNT: usize;

    fn from_bit(bit: <Self::Bitfield as Bitfield>::Repr) -> Option<Self> {
        Self::try_from(bit).ok()
    }

    fn from_pos(pos: usize) -> Option<Self> {
        if pos >= Self::COUNT {
            None
        } else {
            let bit: <Self::Bitfield as Bitfield>::Repr =
                <u8 as Into<<Self::Bitfield as Bitfield>::Repr>>::into(1) << pos;
            Self::from_bit(bit)
        }
    }
}

// #[macro_export]
// macro_rules! count_variants {
//     () => { 0 };
//     ($head:ident $(, $tail:ident)*) => { 1 + count_variants!($($tail),*) };
// }

// #[macro_export]
// macro_rules! benum {
//     {enum $name: ident {
//         $($variant: ident $(= $repr: expr)?),+ $(,)?
//     }} => {
//         #[repr(u8)]
//         #[derive(Clone, Copy, Debug, Eq, PartialEq)]
//         enum $name {
//             $(
//                 $variant $(= $repr)?
//             ),+
//         }

//         impl std::convert::TryFrom<u8> for $name {
//             type Error = String;

//             fn try_from(value: u8) -> Result<Self, Self::Error> {
//                 match value {
//                     $(n if n == $name::$variant as u8 => Ok($name::$variant),)+
//                     _ => Err(format!("Invalid value for {}", stringify!($name))),
//                 }
//             }
//         }

//         impl $crate::prelude::Bitenum for $name {
//             const COUNT: usize = count_variants!($($variant),+);
//         }
//     };
// }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitfield8::Bitfield8;

    // benum! {
    //     enum Letters {
    //         A = 0b00000001,
    //         B = 0b00000010,
    //         C = 0b00000100,
    //         D = 0b00001000,
    //         E = 0b00010000,
    //         F = 0b00100000,
    //         G = 0b01000000,
    //         H = 0b10000000,
    //     }
    // }

    #[derive(Debug, Flagenum)]
    enum Days {
        Monday = 0b00000001,
        Tuesday = 0b00000010,
        Wednesday = 0b00000100,
        Thursday = 0b00001000,
        Friday = 0b00010000,
        Saturday = 0b00100000,
        Sunday = 0b01000000,
    }

    impl TryFrom<u8> for Days {
        type Error = String;

        fn try_from(value: u8) -> Result<Self, Self::Error> {
            match value {
                0b00000001 => Ok(Days::Monday),
                0b00000010 => Ok(Days::Tuesday),
                0b00000100 => Ok(Days::Wednesday),
                0b00001000 => Ok(Days::Thursday),
                0b00010000 => Ok(Days::Friday),
                0b00100000 => Ok(Days::Saturday),
                0b01000000 => Ok(Days::Sunday),
                _ => Err(format!("Invalid value for {}", stringify!($name))),
            }
        }
    }

    impl From<Days> for u8 {
        fn from(value: Days) -> Self {
            value as u8
        }
    }

    impl From<Days> for Bitfield8 {
        fn from(value: Days) -> Self {
            (value as u8).into()
        }
    }

    #[test]
    fn testing() {
        for i in 0..8 {
            let day = Days::from_pos(i);
            println!("{:?}", day);

            let day = Days::try_from(1 << i);
            println!("{:?}", day);
        }
    }
}
