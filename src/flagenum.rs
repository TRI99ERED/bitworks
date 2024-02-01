use crate::{
    bitfield::Bitfield,
    error::{BitfieldError, BitfieldResult},
};

pub trait Flagenum: Sized + TryFrom<Self::Bitfield>
where
    Self::Bitfield: Bitfield,
{
    type Bitfield;

    fn try_from_bitfield(bitfield: Self::Bitfield) -> BitfieldResult<Self> {
        Self::try_from(bitfield).map_err(|_| BitfieldError::IntoEnum)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitfield8::Bitfield8;

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

    #[test]
    fn testing() {
        for i in 0..8 {
            let day = Days::try_from_bitfield(Bitfield8::from(i as u8));
            println!("{:?}", day);

            let day = Days::try_from(Bitfield8::IDENT << i);
            println!("{:?}", day);
        }
    }
}
