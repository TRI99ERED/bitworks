use crate::{
    bitfield::Bitfield, error::{BitfieldError, BitfieldResult}, index::BitfieldIndex
};

pub trait Flagenum: Sized + TryFrom<BitfieldIndex<Self::Bitfield>>
where
    Self::Bitfield: Bitfield,
{
    type Bitfield;

    fn try_from_index(i: BitfieldIndex<Self::Bitfield>) -> BitfieldResult<Self> {
        Self::try_from(i).map_err(|_| BitfieldError::IntoEnum)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitfield8::Bitfield8;

    #[test]
    fn normal_representation() {
        #[derive(Debug, PartialEq, Eq)]
        enum WeekDay {
            Monday = 0,
            Tuesday = 1,
            Wednesday = 2,
            Thursday = 3,
            Friday = 4,
            Saturday = 5,
            Sunday = 6,
        }

        impl TryFrom<BitfieldIndex<Bitfield8>> for WeekDay {
            type Error = String;

            fn try_from(value: BitfieldIndex<Bitfield8>) -> Result<Self, Self::Error> {
                match value.value() {
                    0 => Ok(WeekDay::Monday),
                    1 => Ok(WeekDay::Tuesday),
                    2 => Ok(WeekDay::Wednesday),
                    3 => Ok(WeekDay::Thursday),
                    4 => Ok(WeekDay::Friday),
                    5 => Ok(WeekDay::Saturday),
                    6 => Ok(WeekDay::Sunday),
                    _ => Err("Invalid value for WeekDay".to_owned()),
                }
            }
        }

        impl Flagenum for WeekDay {
            type Bitfield = Bitfield8;
        }

        let mut iter = Bitfield8::ALL.selected_variant_iter::<WeekDay>();

        assert_eq!(iter.next().unwrap(), WeekDay::Monday);
        assert_eq!(iter.next().unwrap(), WeekDay::Tuesday);
        assert_eq!(iter.next().unwrap(), WeekDay::Wednesday);
        assert_eq!(iter.next().unwrap(), WeekDay::Thursday);
        assert_eq!(iter.next().unwrap(), WeekDay::Friday);
        assert_eq!(iter.next().unwrap(), WeekDay::Saturday);
        assert_eq!(iter.next().unwrap(), WeekDay::Sunday);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn shift_representation() {
        #[derive(Debug, PartialEq, Eq)]
        enum WeekDay {
            Monday = 0b00000001,
            Tuesday = 0b00000010,
            Wednesday = 0b00000100,
            Thursday = 0b00001000,
            Friday = 0b00010000,
            Saturday = 0b00100000,
            Sunday = 0b01000000,
        }

        impl TryFrom<BitfieldIndex<Bitfield8>> for WeekDay {
            type Error = String;

            fn try_from(value: BitfieldIndex<Bitfield8>) -> Result<Self, Self::Error> {
                match value.value() {
                    0 => Ok(WeekDay::Monday),
                    1 => Ok(WeekDay::Tuesday),
                    2 => Ok(WeekDay::Wednesday),
                    3 => Ok(WeekDay::Thursday),
                    4 => Ok(WeekDay::Friday),
                    5 => Ok(WeekDay::Saturday),
                    6 => Ok(WeekDay::Sunday),
                    _ => Err("Invalid value for WeekDay".to_owned()),
                }
            }
        }

        impl Flagenum for WeekDay {
            type Bitfield = Bitfield8;
        }

        let mut iter = Bitfield8::ALL.selected_variant_iter::<WeekDay>();

        assert_eq!(iter.next().unwrap(), WeekDay::Monday);
        assert_eq!(iter.next().unwrap(), WeekDay::Tuesday);
        assert_eq!(iter.next().unwrap(), WeekDay::Wednesday);
        assert_eq!(iter.next().unwrap(), WeekDay::Thursday);
        assert_eq!(iter.next().unwrap(), WeekDay::Friday);
        assert_eq!(iter.next().unwrap(), WeekDay::Saturday);
        assert_eq!(iter.next().unwrap(), WeekDay::Sunday);
        assert_eq!(iter.next(), None);
    }
}
