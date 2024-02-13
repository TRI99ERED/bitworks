//! Module containing size safety markers for compile time checks on some methods.

/// Marker for [`Bitsets`][crate::bitset::Bitset] used in size comparisons.
///
/// Is not relevant to users of this crate, unless they intend to define their own methods using it or
/// implement `Bitset` on custom types.
///
/// [`Size`] is a built-in implementor. Please use it, over defining your own type, if possible.
/// It's not meant to be implemented on the implementors of `Bitset` itself.
pub trait SizeMarker: Sized {}

/// Marker for [`Bitsets`][crate::bitset::Bitset] used in size comparisons. Implementing this trait
/// means, that `Self` is bigger in byte size, than `S`.
///
/// Is not relevant to users of this crate, unless they intend to define their own methods using it or
/// implement `Bitset` on custom types.
///
/// [`Size`] is a built-in implementor. Please use it, over defining your own type, if possible.
/// It's not meant to be implemented on the implementors of `Bitset` itself.
pub trait Bigger<S: SizeMarker>: SizeMarker {}

/// Marker for [`Bitsets`][crate::bitset::Bitset] used in size comparisons. Implementing this trait
/// means, that `Self` is smaller in byte size, than `B`.
///
/// `Smaller<B>` is automatically implemented for `T`, if `B` implements `Bigger<T>`.
///
/// Is not relevant to users of this crate, unless they intend to define their own methods using it or
/// implement `Bitset` on custom types.
///
/// [`Size`] is a built-in implementor. Please use it, over defining your own type, if possible.
/// It's not meant to be implemented on the implementors of `Bitset` itself.
pub trait Smaller<B: SizeMarker>: SizeMarker {}

impl<B, S> Smaller<B> for S
where
    B: SizeMarker + Bigger<S>,
    S: SizeMarker,
{
}

/// Marker for [`Bitsets`][crate::bitset::Bitset] used in size comparisons. Implementing this trait
/// means, that the byte size of `Self` is exactly equal to the sum of the byte sizes of `P1` and `P2`.
///
/// Is not relevant to users of this crate, unless they intend to define their own methods using it or
/// implement `Bitset` on custom types.
///
/// [`Size`] is a built-in implementor. Please use it, over defining your own type, if possible.
/// It's not meant to be implemented on the implementors of `Bitset` itself.
pub trait Splits<P1: SizeMarker, P2: SizeMarker>: SizeMarker + Bigger<P1> + Bigger<P2> {}

/// Marker for [`Bitsets`][crate::bitset::Bitset] used in size comparisons. Implementing this trait
/// means, that the sum of the byte sizes of `Self` and `O` is exactly equal to the byte size of `W`.
///
/// `Combines<O, W>` is automatically implemented for `T`, if `W` implements `Split<T, O>`.
///
/// Is not relevant to users of this crate, unless they intend to define their own methods using it or
/// implement `Bitset` on custom types.
///
/// [`Size`] is a built-in implementor. Please use it, over defining your own type, if possible.
/// It's not meant to be implemented on the implementors of `Bitset` itself.
pub trait Combines<O: SizeMarker, W: SizeMarker + Bigger<Self> + Bigger<O>>: SizeMarker {}

impl<W, P1, P2> Combines<P2, W> for P1
where
    W: SizeMarker + Splits<P1, P2> + Bigger<P1> + Bigger<P2>,
    P1: SizeMarker,
    P2: SizeMarker,
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
