use bitworks::prelude::*;

#[test]
fn main() {
    let mut bitset = Bitset8::NONE
        .clone()
        .include(Bitset8::new(0b10000000))
        .set(Index8::from_usize(1))
        .replace(Index8::from_usize(3), One)
        .flip(Index8::from_usize(5))
        .build();

    assert_eq!(bitset.into_inner(), 0b10101010);

    for mut bit in bitset.bits_mut() {
        *bit = !*bit;
    }

    assert_eq!(bitset.into_inner(), 0b01010101);

    assert_eq!(bitset.bit(Index8::from_usize(7)), Zero);

    let other = Bitset8::new(0b11110000);

    let bitset = bitset.complement();

    assert_eq!(bitset.into_inner(), 0b10101010);
    assert_eq!(bitset.union(other).into_inner(), 0b11111010);
    assert_eq!(bitset.intersection(other).into_inner(), 0b10100000);
    assert_eq!(bitset.difference(other).into_inner(), 0b00001010);
    assert_eq!(bitset.sym_difference(other).into_inner(), 0b01011010);

    assert!(bitset.intersects(&other));
    assert!(!bitset.includes(&other));
    assert!(Bitset8::ALL.includes(&bitset));

    let bigger_bitset: Bitset16 = bitset.expand();

    assert_eq!(bigger_bitset.into_inner(), 0b0000000010101010);

    let combined: Bitset16 = bitset.combine(other);

    assert_eq!(combined.into_inner(), 0b1111000010101010);

    let (bitset, other) = combined.split::<Bitset8, Bitset8>();

    assert_eq!(bitset.into_inner(), 0b10101010);
    assert_eq!(other.into_inner(), 0b11110000);

    let v: Vec<Bit> = bitset.bits().rev().collect();

    assert_eq!(&v, &[One, Zero, One, Zero, One, Zero, One, Zero]);

    let bitset = Bitset8::from_iterable(&v);
    assert_eq!(bitset.into_inner(), 0b01010101);
}
