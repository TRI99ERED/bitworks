pub mod bitfield;
pub mod bitfield128;
pub mod bitfield16;
pub mod bitfield32;
pub mod bitfield64;
pub mod bitfield8;

pub mod error;
pub mod flagenum;
pub mod iter;

pub mod prelude {
    use super::*;

    pub use bitfield::Bitfield;
    pub use bitfield128::Bitfield128;
    pub use bitfield16::Bitfield16;
    pub use bitfield32::Bitfield32;
    pub use bitfield64::Bitfield64;
    pub use bitfield8::Bitfield8;

    pub use flagenum::Flagenum;
    pub use iter::BitIter;
}

#[cfg(test)]
mod tests {
    use super::prelude::*;

    #[derive(Debug)]
    enum Days {
        Monday = 0b00000001,
        Tuesday = 0b00000010,
        Wednesday = 0b00000100,
        Thursday = 0b00001000,
        Friday = 0b00010000,
        Saturday = 0b00100000,
        Sunday = 0b01000000,
    }

    impl TryFrom<Bitfield8> for Days {
        type Error = String;

        fn try_from(value: Bitfield8) -> Result<Self, Self::Error> {
            match value.value() {
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

    impl Flagenum for Days {
        type Bitfield = Bitfield8;
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
    fn it_works() {
        let bitfield = Bitfield8::from(170);
        let days = bitfield
            .into_iter()
            .enumerate()
            .filter(|(_, flag)| *flag)
            .map(|(i, _)| Days::try_from_bitfield(Bitfield8::from(i as u8)))
            .collect::<Vec<_>>();
        println!("{:?}", days);

        let bitfield = Bitfield8::default()
            .check_bit(1)
            .check_bit(3)
            .check_bit(5)
            .check_bit(7);

        println!("{bitfield}");

        let bit_iter = bitfield.into_iter();

        for b in bitfield {
            println!("{b}");
        }

        let bitfield: Bitfield8 = bit_iter.collect();

        println!("{bitfield}");
    }
}
