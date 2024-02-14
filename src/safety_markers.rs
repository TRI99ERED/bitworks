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

// Bigger than 1
impl Bigger<Size<1>> for Size<3> {}
impl Bigger<Size<1>> for Size<5> {}
impl Bigger<Size<1>> for Size<6> {}
impl Bigger<Size<1>> for Size<7> {}
impl Bigger<Size<1>> for Size<9> {}
impl Bigger<Size<1>> for Size<10> {}
impl Bigger<Size<1>> for Size<11> {}
impl Bigger<Size<1>> for Size<12> {}
impl Bigger<Size<1>> for Size<13> {}
impl Bigger<Size<1>> for Size<14> {}
impl Bigger<Size<1>> for Size<15> {}

// Bigger than 2
impl Bigger<Size<2>> for Size<3> {}
impl Bigger<Size<2>> for Size<5> {}
impl Bigger<Size<2>> for Size<6> {}
impl Bigger<Size<2>> for Size<7> {}
impl Bigger<Size<2>> for Size<9> {}
impl Bigger<Size<2>> for Size<10> {}
impl Bigger<Size<2>> for Size<11> {}
impl Bigger<Size<2>> for Size<12> {}
impl Bigger<Size<2>> for Size<13> {}
impl Bigger<Size<2>> for Size<14> {}
impl Bigger<Size<2>> for Size<15> {}

// Bigger than 3
impl Bigger<Size<3>> for Size<3> {}
impl Bigger<Size<3>> for Size<4> {}
impl Bigger<Size<3>> for Size<5> {}
impl Bigger<Size<3>> for Size<6> {}
impl Bigger<Size<3>> for Size<7> {}
impl Bigger<Size<3>> for Size<8> {}
impl Bigger<Size<3>> for Size<9> {}
impl Bigger<Size<3>> for Size<10> {}
impl Bigger<Size<3>> for Size<11> {}
impl Bigger<Size<3>> for Size<12> {}
impl Bigger<Size<3>> for Size<13> {}
impl Bigger<Size<3>> for Size<14> {}
impl Bigger<Size<3>> for Size<15> {}
impl Bigger<Size<3>> for Size<16> {}

// Bigger than 4
impl Bigger<Size<4>> for Size<5> {}
impl Bigger<Size<4>> for Size<6> {}
impl Bigger<Size<4>> for Size<7> {}
impl Bigger<Size<4>> for Size<9> {}
impl Bigger<Size<4>> for Size<10> {}
impl Bigger<Size<4>> for Size<11> {}
impl Bigger<Size<4>> for Size<12> {}
impl Bigger<Size<4>> for Size<13> {}
impl Bigger<Size<4>> for Size<14> {}
impl Bigger<Size<4>> for Size<15> {}

// Bigger than 5
impl Bigger<Size<5>> for Size<6> {}
impl Bigger<Size<5>> for Size<7> {}
impl Bigger<Size<5>> for Size<8> {}
impl Bigger<Size<5>> for Size<9> {}
impl Bigger<Size<5>> for Size<10> {}
impl Bigger<Size<5>> for Size<11> {}
impl Bigger<Size<5>> for Size<12> {}
impl Bigger<Size<5>> for Size<13> {}
impl Bigger<Size<5>> for Size<14> {}
impl Bigger<Size<5>> for Size<15> {}
impl Bigger<Size<5>> for Size<16> {}

// Bigger than 6
impl Bigger<Size<6>> for Size<7> {}
impl Bigger<Size<6>> for Size<8> {}
impl Bigger<Size<6>> for Size<9> {}
impl Bigger<Size<6>> for Size<10> {}
impl Bigger<Size<6>> for Size<11> {}
impl Bigger<Size<6>> for Size<12> {}
impl Bigger<Size<6>> for Size<13> {}
impl Bigger<Size<6>> for Size<14> {}
impl Bigger<Size<6>> for Size<15> {}
impl Bigger<Size<6>> for Size<16> {}

// Bigger than 7
impl Bigger<Size<7>> for Size<8> {}
impl Bigger<Size<7>> for Size<9> {}
impl Bigger<Size<7>> for Size<10> {}
impl Bigger<Size<7>> for Size<11> {}
impl Bigger<Size<7>> for Size<12> {}
impl Bigger<Size<7>> for Size<13> {}
impl Bigger<Size<7>> for Size<14> {}
impl Bigger<Size<7>> for Size<15> {}
impl Bigger<Size<7>> for Size<16> {}

// Bigger than 8
impl Bigger<Size<8>> for Size<9> {}
impl Bigger<Size<8>> for Size<10> {}
impl Bigger<Size<8>> for Size<11> {}
impl Bigger<Size<8>> for Size<12> {}
impl Bigger<Size<8>> for Size<13> {}
impl Bigger<Size<8>> for Size<14> {}
impl Bigger<Size<8>> for Size<15> {}

// Bigger than 9
impl Bigger<Size<9>> for Size<10> {}
impl Bigger<Size<9>> for Size<11> {}
impl Bigger<Size<9>> for Size<12> {}
impl Bigger<Size<9>> for Size<13> {}
impl Bigger<Size<9>> for Size<14> {}
impl Bigger<Size<9>> for Size<15> {}
impl Bigger<Size<9>> for Size<16> {}

// Bigger than 10
impl Bigger<Size<10>> for Size<11> {}
impl Bigger<Size<10>> for Size<12> {}
impl Bigger<Size<10>> for Size<13> {}
impl Bigger<Size<10>> for Size<14> {}
impl Bigger<Size<10>> for Size<15> {}
impl Bigger<Size<10>> for Size<16> {}

// Bigger than 11
impl Bigger<Size<11>> for Size<12> {}
impl Bigger<Size<11>> for Size<13> {}
impl Bigger<Size<11>> for Size<14> {}
impl Bigger<Size<11>> for Size<15> {}
impl Bigger<Size<11>> for Size<16> {}

// Bigger than 12
impl Bigger<Size<12>> for Size<13> {}
impl Bigger<Size<12>> for Size<14> {}
impl Bigger<Size<12>> for Size<15> {}
impl Bigger<Size<12>> for Size<16> {}

// Bigger than 13
impl Bigger<Size<13>> for Size<14> {}
impl Bigger<Size<13>> for Size<15> {}
impl Bigger<Size<13>> for Size<16> {}

// Bigger than 14
impl Bigger<Size<14>> for Size<15> {}
impl Bigger<Size<14>> for Size<16> {}

// Bigger than 15
impl Bigger<Size<15>> for Size<16> {}

// 3 splits into
impl Splits<Size<1>, Size<2>> for Size<3> {}
impl Splits<Size<2>, Size<1>> for Size<3> {}

// 4 splits into
impl Splits<Size<1>, Size<3>> for Size<4> {}
impl Splits<Size<3>, Size<1>> for Size<4> {}

// 5 splits into
impl Splits<Size<1>, Size<4>> for Size<5> {}
impl Splits<Size<4>, Size<1>> for Size<5> {}
impl Splits<Size<2>, Size<3>> for Size<5> {}
impl Splits<Size<3>, Size<2>> for Size<5> {}

// 6 splits into
impl Splits<Size<1>, Size<5>> for Size<6> {}
impl Splits<Size<5>, Size<1>> for Size<6> {}
impl Splits<Size<2>, Size<4>> for Size<6> {}
impl Splits<Size<4>, Size<2>> for Size<6> {}
impl Splits<Size<3>, Size<3>> for Size<6> {}

// 7 splits into
impl Splits<Size<1>, Size<6>> for Size<7> {}
impl Splits<Size<6>, Size<1>> for Size<7> {}
impl Splits<Size<2>, Size<5>> for Size<7> {}
impl Splits<Size<5>, Size<2>> for Size<7> {}
impl Splits<Size<3>, Size<4>> for Size<7> {}
impl Splits<Size<4>, Size<3>> for Size<7> {}

// 8 splits into
impl Splits<Size<1>, Size<7>> for Size<8> {}
impl Splits<Size<7>, Size<1>> for Size<8> {}
impl Splits<Size<2>, Size<6>> for Size<8> {}
impl Splits<Size<6>, Size<2>> for Size<8> {}
impl Splits<Size<3>, Size<5>> for Size<8> {}
impl Splits<Size<5>, Size<3>> for Size<8> {}

// 9 splits into
impl Splits<Size<1>, Size<8>> for Size<9> {}
impl Splits<Size<8>, Size<1>> for Size<9> {}
impl Splits<Size<2>, Size<7>> for Size<9> {}
impl Splits<Size<7>, Size<2>> for Size<9> {}
impl Splits<Size<3>, Size<6>> for Size<9> {}
impl Splits<Size<6>, Size<3>> for Size<9> {}
impl Splits<Size<4>, Size<5>> for Size<9> {}
impl Splits<Size<5>, Size<4>> for Size<9> {}

// 10 splits into
impl Splits<Size<1>, Size<9>> for Size<10> {}
impl Splits<Size<9>, Size<1>> for Size<10> {}
impl Splits<Size<2>, Size<8>> for Size<10> {}
impl Splits<Size<8>, Size<2>> for Size<10> {}
impl Splits<Size<3>, Size<7>> for Size<10> {}
impl Splits<Size<7>, Size<3>> for Size<10> {}
impl Splits<Size<4>, Size<6>> for Size<10> {}
impl Splits<Size<6>, Size<4>> for Size<10> {}
impl Splits<Size<5>, Size<5>> for Size<10> {}

// 11 splits into
impl Splits<Size<1>, Size<10>> for Size<11> {}
impl Splits<Size<10>, Size<1>> for Size<11> {}
impl Splits<Size<2>, Size<9>> for Size<11> {}
impl Splits<Size<9>, Size<2>> for Size<11> {}
impl Splits<Size<3>, Size<8>> for Size<11> {}
impl Splits<Size<8>, Size<3>> for Size<11> {}
impl Splits<Size<4>, Size<7>> for Size<11> {}
impl Splits<Size<7>, Size<4>> for Size<11> {}
impl Splits<Size<5>, Size<6>> for Size<11> {}
impl Splits<Size<6>, Size<5>> for Size<11> {}

// 12 splits into
impl Splits<Size<1>, Size<11>> for Size<12> {}
impl Splits<Size<11>, Size<1>> for Size<12> {}
impl Splits<Size<2>, Size<10>> for Size<12> {}
impl Splits<Size<10>, Size<2>> for Size<12> {}
impl Splits<Size<3>, Size<9>> for Size<12> {}
impl Splits<Size<9>, Size<3>> for Size<12> {}
impl Splits<Size<4>, Size<8>> for Size<12> {}
impl Splits<Size<8>, Size<4>> for Size<12> {}
impl Splits<Size<5>, Size<7>> for Size<12> {}
impl Splits<Size<7>, Size<5>> for Size<12> {}
impl Splits<Size<6>, Size<6>> for Size<12> {}

// 13 splits into
impl Splits<Size<1>, Size<12>> for Size<13> {}
impl Splits<Size<12>, Size<1>> for Size<13> {}
impl Splits<Size<2>, Size<11>> for Size<13> {}
impl Splits<Size<11>, Size<2>> for Size<13> {}
impl Splits<Size<3>, Size<10>> for Size<13> {}
impl Splits<Size<10>, Size<3>> for Size<13> {}
impl Splits<Size<4>, Size<9>> for Size<13> {}
impl Splits<Size<9>, Size<4>> for Size<13> {}
impl Splits<Size<5>, Size<8>> for Size<13> {}
impl Splits<Size<8>, Size<5>> for Size<13> {}
impl Splits<Size<6>, Size<7>> for Size<13> {}
impl Splits<Size<7>, Size<6>> for Size<13> {}

// 14 splits into
impl Splits<Size<1>, Size<13>> for Size<14> {}
impl Splits<Size<13>, Size<1>> for Size<14> {}
impl Splits<Size<2>, Size<12>> for Size<14> {}
impl Splits<Size<12>, Size<2>> for Size<14> {}
impl Splits<Size<3>, Size<11>> for Size<14> {}
impl Splits<Size<11>, Size<3>> for Size<14> {}
impl Splits<Size<4>, Size<10>> for Size<14> {}
impl Splits<Size<10>, Size<4>> for Size<14> {}
impl Splits<Size<5>, Size<9>> for Size<14> {}
impl Splits<Size<9>, Size<5>> for Size<14> {}
impl Splits<Size<6>, Size<8>> for Size<14> {}
impl Splits<Size<8>, Size<6>> for Size<14> {}
impl Splits<Size<7>, Size<7>> for Size<14> {}

// 15 splits into
impl Splits<Size<1>, Size<14>> for Size<15> {}
impl Splits<Size<14>, Size<1>> for Size<15> {}
impl Splits<Size<2>, Size<13>> for Size<15> {}
impl Splits<Size<13>, Size<2>> for Size<15> {}
impl Splits<Size<3>, Size<12>> for Size<15> {}
impl Splits<Size<12>, Size<3>> for Size<15> {}
impl Splits<Size<4>, Size<11>> for Size<15> {}
impl Splits<Size<11>, Size<4>> for Size<15> {}
impl Splits<Size<5>, Size<10>> for Size<15> {}
impl Splits<Size<10>, Size<5>> for Size<15> {}
impl Splits<Size<6>, Size<9>> for Size<15> {}
impl Splits<Size<9>, Size<6>> for Size<15> {}
impl Splits<Size<7>, Size<8>> for Size<15> {}
impl Splits<Size<8>, Size<7>> for Size<15> {}

// 16 splits into
impl Splits<Size<1>, Size<15>> for Size<16> {}
impl Splits<Size<15>, Size<1>> for Size<16> {}
impl Splits<Size<2>, Size<14>> for Size<16> {}
impl Splits<Size<14>, Size<2>> for Size<16> {}
impl Splits<Size<3>, Size<13>> for Size<16> {}
impl Splits<Size<13>, Size<3>> for Size<16> {}
impl Splits<Size<4>, Size<12>> for Size<16> {}
impl Splits<Size<12>, Size<4>> for Size<16> {}
impl Splits<Size<5>, Size<11>> for Size<16> {}
impl Splits<Size<11>, Size<5>> for Size<16> {}
impl Splits<Size<6>, Size<10>> for Size<16> {}
impl Splits<Size<10>, Size<6>> for Size<16> {}
impl Splits<Size<7>, Size<9>> for Size<16> {}
impl Splits<Size<9>, Size<7>> for Size<16> {}
