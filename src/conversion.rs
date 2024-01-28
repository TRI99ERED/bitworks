use crate::private::BitfieldMarker;

pub trait IntoBitfield<B>
where
    B: BitfieldMarker,
{
    fn into_bitfield(self) -> B;
}

pub trait FromBitfield<B>
where
    B: BitfieldMarker,
{
    fn from_bitfield(bitfield: B) -> Self;
}
