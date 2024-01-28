pub mod bitfield;
pub mod bitfield128;
pub mod bitfield16;
pub mod bitfield32;
pub mod bitfield64;
pub mod bitfield8;

pub mod conversion;
pub mod iter;

pub mod prelude {
    use super::*;

    pub use bitfield::Bitfield;
    pub use bitfield128::Bitfield128;
    pub use bitfield16::Bitfield16;
    pub use bitfield32::Bitfield32;
    pub use bitfield64::Bitfield64;
    pub use bitfield8::Bitfield8;

    pub use iter::BitIter;
}

mod private {
    pub trait BitfieldMarker {}

    pub trait BitfieldHelper<T> {
        const BIT: T;
        const EMPTY: T;
        const ALL: T;
    }
}

#[cfg(test)]
mod tests {
    use super::prelude::*;

    #[repr(u8)]
    #[derive(Clone, Copy, Debug)]
    enum Letters {
        A = 0b00000001,
        B = 0b00000010,
        C = 0b00000100,
        D = 0b00001000,
        E = 0b00010000,
        F = 0b00100000,
        G = 0b01000000,
        H = 0b10000000,
    }

    impl From<u8> for Letters {
        fn from(value: u8) -> Self {
            match value {
                0b00000001 => Letters::A,
                0b00000010 => Letters::B,
                0b00000100 => Letters::C,
                0b00001000 => Letters::D,
                0b00010000 => Letters::E,
                0b00100000 => Letters::F,
                0b01000000 => Letters::G,
                0b10000000 => Letters::H,
                _ => panic!("Error converting from u8 to Letters"),
            }
        }
    }

    impl Into<u8> for Letters {
        fn into(self) -> u8 {
            match self {
                Self::A => 0b00000001,
                Self::B => 0b00000010,
                Self::C => 0b00000100,
                Self::D => 0b00001000,
                Self::E => 0b00010000,
                Self::F => 0b00100000,
                Self::G => 0b01000000,
                Self::H => 0b10000000,
            }
        }
    }

    #[test]
    fn it_works() {
        let bitfield = Bitfield8::from(170);
        let letters = bitfield
            .into_iter()
            .enumerate()
            .filter(|(_, flag)| *flag)
            .map(|(i, _)| Letters::from(1 << i))
            .collect::<Vec<_>>();
        println!("{:?}", letters);

        let bitfield = Bitfield8::default()
            .check_flag(1)
            .check_flag(3)
            .check_flag(5)
            .check_flag(7)
            .build();

        println!("{bitfield}");

        let bit_iter = bitfield.into_iter();

        for b in bitfield {
            println!("{b}");
        }

        let bitfield: Bitfield8 = bit_iter.collect();

        println!("{bitfield}");
    }
}
