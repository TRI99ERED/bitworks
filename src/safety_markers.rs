//! Module containing size safety markers for compile time checks on some methods.

pub trait SizeMarker: Sized {}

pub trait Bigger<Small: SizeMarker>: SizeMarker {}

pub trait Smaller<Big: SizeMarker>: SizeMarker {}

impl<Big, Small> Smaller<Big> for Small
where
    Big: SizeMarker + Bigger<Small>,
    Small: SizeMarker,
{
}

pub trait Splits<Part1: SizeMarker, Part2: SizeMarker>:
    SizeMarker + Bigger<Part1> + Bigger<Part2>
{
}

pub trait Combines<Other: SizeMarker, Whole: SizeMarker + Bigger<Self> + Bigger<Other>>:
    SizeMarker
{
}

impl<Whole, Part1, Part2> Combines<Part2, Whole> for Part1
where
    Whole: SizeMarker + Splits<Part1, Part2> + Bigger<Part1> + Bigger<Part2>,
    Part1: SizeMarker,
    Part2: SizeMarker,
{
}

pub struct Size<const BYTES: usize>;

impl<const BYTES: usize> SizeMarker for Size<BYTES> {}

impl Bigger<Size<1>> for Size<2> {}
impl Bigger<Size<1>> for Size<4> {}
impl Bigger<Size<1>> for Size<8> {}
impl Bigger<Size<1>> for Size<16> {}
impl Bigger<Size<1>> for Size<32> {}
impl Bigger<Size<1>> for Size<64> {}
impl Bigger<Size<1>> for Size<128> {}
impl Bigger<Size<2>> for Size<4> {}
impl Bigger<Size<2>> for Size<8> {}
impl Bigger<Size<2>> for Size<16> {}
impl Bigger<Size<2>> for Size<32> {}
impl Bigger<Size<2>> for Size<64> {}
impl Bigger<Size<2>> for Size<128> {}
impl Bigger<Size<4>> for Size<8> {}
impl Bigger<Size<4>> for Size<16> {}
impl Bigger<Size<4>> for Size<32> {}
impl Bigger<Size<4>> for Size<64> {}
impl Bigger<Size<4>> for Size<128> {}
impl Bigger<Size<8>> for Size<16> {}
impl Bigger<Size<8>> for Size<32> {}
impl Bigger<Size<8>> for Size<64> {}
impl Bigger<Size<8>> for Size<128> {}
impl Bigger<Size<16>> for Size<32> {}
impl Bigger<Size<16>> for Size<64> {}
impl Bigger<Size<16>> for Size<128> {}
impl Bigger<Size<32>> for Size<64> {}
impl Bigger<Size<32>> for Size<128> {}
impl Bigger<Size<64>> for Size<128> {}

impl Splits<Size<1>, Size<1>> for Size<2> {}
impl Splits<Size<2>, Size<2>> for Size<4> {}
impl Splits<Size<4>, Size<4>> for Size<8> {}
impl Splits<Size<8>, Size<8>> for Size<16> {}
impl Splits<Size<16>, Size<16>> for Size<32> {}
impl Splits<Size<32>, Size<32>> for Size<64> {}
impl Splits<Size<64>, Size<64>> for Size<128> {}
