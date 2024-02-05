//! Module containing [`FlagsEnum`].

use crate::{bitfield::Bitfield, index::BitfieldIndex};

/// Marker trait for [`enum`]s, whose variants represent the different indeces of [`Bitfield`].
///
/// # Examples
/// ```
/// use simple_bitfield::{prelude::{Bitfield, Bitfield8, FlagsEnum, BitfieldIndex}, error::{ConvError, ConvTarget}};
///
/// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// enum WeekDay {
///     Monday = 0,
///     Tuesday = 1,
///     Wednesday = 2,
///     Thursday = 3,
///     Friday = 4,
///     Saturday = 5,
///     Sunday = 6,
/// }
///
/// impl TryFrom<BitfieldIndex<Bitfield8>> for WeekDay {
///     type Error = ConvError;
///
///     fn try_from(value: BitfieldIndex<Bitfield8>) -> Result<Self, Self::Error> {
///         match value.into_inner() {
///             0 => Ok(WeekDay::Monday),
///             1 => Ok(WeekDay::Tuesday),
///             2 => Ok(WeekDay::Wednesday),
///             3 => Ok(WeekDay::Thursday),
///             4 => Ok(WeekDay::Friday),
///             5 => Ok(WeekDay::Saturday),
///             6 => Ok(WeekDay::Sunday),
///             _ => Err(ConvError::new(ConvTarget::Index(8), ConvTarget::Enum(8))),
///         }
///     }
/// }
///
/// impl From<WeekDay> for BitfieldIndex<Bitfield8> {
///     fn from(value: WeekDay) -> Self {
///         Self::try_from(value as usize).unwrap()
///     }
/// }
///
/// impl FlagsEnum for WeekDay {
///     type Bitfield = Bitfield8;
/// }
///
/// fn example() {
///     let mut iter = Bitfield8::ALL.selected_variants::<WeekDay>();
///
///     assert_eq!(iter.next().unwrap(), WeekDay::Monday);
///     assert_eq!(iter.next().unwrap(), WeekDay::Tuesday);
///     assert_eq!(iter.next().unwrap(), WeekDay::Wednesday);
///     assert_eq!(iter.next().unwrap(), WeekDay::Thursday);
///     assert_eq!(iter.next().unwrap(), WeekDay::Friday);
///     assert_eq!(iter.next().unwrap(), WeekDay::Saturday);
///     assert_eq!(iter.next().unwrap(), WeekDay::Sunday);
///     assert_eq!(iter.next(), None);
///
///     let bitfield = Bitfield8::from(0b10101010);
///     let iter = bitfield.selected_variants::<WeekDay>();
///     assert_eq!(iter.collect::<Bitfield8>(), Bitfield8::from(0b00101010));
/// }
/// ```
pub trait FlagsEnum: Sized + Clone + TryFrom<BitfieldIndex<Self::Bitfield>>
where
    Self::Bitfield: Bitfield,
    BitfieldIndex<Self::Bitfield>: From<Self>,
{
    /// [`Bitfield`] which bits `FlagsEnum` enumerates
    type Bitfield;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        bitfield8::Bitfield8,
        error::{ConvError, ConvTarget},
    };

    #[test]
    fn normal_representation() {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
            type Error = ConvError;

            fn try_from(value: BitfieldIndex<Bitfield8>) -> Result<Self, Self::Error> {
                match value.into_inner() {
                    0 => Ok(WeekDay::Monday),
                    1 => Ok(WeekDay::Tuesday),
                    2 => Ok(WeekDay::Wednesday),
                    3 => Ok(WeekDay::Thursday),
                    4 => Ok(WeekDay::Friday),
                    5 => Ok(WeekDay::Saturday),
                    6 => Ok(WeekDay::Sunday),
                    _ => Err(ConvError::new(ConvTarget::Index(8), ConvTarget::Enum(8))),
                }
            }
        }

        impl From<WeekDay> for BitfieldIndex<Bitfield8> {
            fn from(value: WeekDay) -> Self {
                Self::try_from(value as usize).unwrap()
            }
        }

        impl FlagsEnum for WeekDay {
            type Bitfield = Bitfield8;
        }

        let mut iter = Bitfield8::ALL.selected_variants::<WeekDay>();

        assert_eq!(iter.next().unwrap(), WeekDay::Monday);
        assert_eq!(iter.next().unwrap(), WeekDay::Tuesday);
        assert_eq!(iter.next().unwrap(), WeekDay::Wednesday);
        assert_eq!(iter.next().unwrap(), WeekDay::Thursday);
        assert_eq!(iter.next().unwrap(), WeekDay::Friday);
        assert_eq!(iter.next().unwrap(), WeekDay::Saturday);
        assert_eq!(iter.next().unwrap(), WeekDay::Sunday);
        assert_eq!(iter.next(), None);

        let bitfield = Bitfield8::from(0b10101010);
        let iter = bitfield.selected_variants::<WeekDay>();
        assert_eq!(iter.collect::<Bitfield8>(), Bitfield8::from(0b00101010));
    }

    #[test]
    fn shift_representation() {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
            type Error = ConvError;

            fn try_from(value: BitfieldIndex<Bitfield8>) -> Result<Self, Self::Error> {
                match value.into_inner() {
                    0 => Ok(WeekDay::Monday),
                    1 => Ok(WeekDay::Tuesday),
                    2 => Ok(WeekDay::Wednesday),
                    3 => Ok(WeekDay::Thursday),
                    4 => Ok(WeekDay::Friday),
                    5 => Ok(WeekDay::Saturday),
                    6 => Ok(WeekDay::Sunday),
                    _ => Err(ConvError::new(ConvTarget::Index(8), ConvTarget::Enum(8))),
                }
            }
        }

        impl From<WeekDay> for BitfieldIndex<Bitfield8> {
            fn from(value: WeekDay) -> Self {
                match value {
                    WeekDay::Monday => 0.try_into().unwrap(),
                    WeekDay::Tuesday => 1.try_into().unwrap(),
                    WeekDay::Wednesday => 2.try_into().unwrap(),
                    WeekDay::Thursday => 3.try_into().unwrap(),
                    WeekDay::Friday => 4.try_into().unwrap(),
                    WeekDay::Saturday => 5.try_into().unwrap(),
                    WeekDay::Sunday => 6.try_into().unwrap(),
                }
            }
        }

        impl FlagsEnum for WeekDay {
            type Bitfield = Bitfield8;
        }

        let mut iter = Bitfield8::ALL.selected_variants::<WeekDay>();

        assert_eq!(iter.next().unwrap(), WeekDay::Monday);
        assert_eq!(iter.next().unwrap(), WeekDay::Tuesday);
        assert_eq!(iter.next().unwrap(), WeekDay::Wednesday);
        assert_eq!(iter.next().unwrap(), WeekDay::Thursday);
        assert_eq!(iter.next().unwrap(), WeekDay::Friday);
        assert_eq!(iter.next().unwrap(), WeekDay::Saturday);
        assert_eq!(iter.next().unwrap(), WeekDay::Sunday);
        assert_eq!(iter.next(), None);

        let bitfield = Bitfield8::from(0b10101010);
        let iter = bitfield.selected_variants::<WeekDay>();
        assert_eq!(iter.collect::<Bitfield8>(), Bitfield8::from(0b00101010));
    }
}
