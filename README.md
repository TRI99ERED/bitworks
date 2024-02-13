[![Rust](https://github.com/TRI99ERED/simple-bitfield/actions/workflows/rust.yml/badge.svg)](https://github.com/TRI99ERED/simple-bitfield/actions/workflows/rust.yml)

Crate meant to provide easy to use bitsets, with some out of the box functionality.

Enable feature "serde" to enable `serde::Serialize` and `serde::Deserialize` for most applicable types.

## Usage overview
```rust
use bitworks::prelude::*;

fn main() {
    // Build the bitset with variety of methods.
    let mut bitset = Bitset8::NONE
        .clone()
        .include(Bitset8::new(0b10000000))
        .set(Index8::from_usize(1))
        .replace(Index8::from_usize(3), One)
        .flip(Index8::from_usize(5))
        .build();

    assert_eq!(bitset.into_inner(), 0b10101010);

    // Iterate over bits as copies, references or mutable references.
    for mut bit in bitset.bits_mut() {
        *bit = !*bit;
    }

    assert_eq!(bitset.into_inner(), 0b01010101);

    assert_eq!(bitset.bit(Index8::from_usize(7)), Zero);

    let other = Bitset8::new(0b11110000);

    // Use Set operations.
    let bitset = bitset.complement();

    assert_eq!(bitset.into_inner(), 0b10101010);
    assert_eq!(bitset.union(other).into_inner(), 0b11111010);
    assert_eq!(bitset.intersection(other).into_inner(), 0b10100000);
    assert_eq!(bitset.difference(other).into_inner(), 0b00001010);
    assert_eq!(bitset.sym_difference(other).into_inner(), 0b01011010);

    assert!(bitset.intersects(&other));
    assert!(!bitset.includes(&other));
    assert!(Bitset8::ALL.includes(&bitset));

    // Expand, combine and split.
    let bigger_bitset: Bitset16 = bitset.expand();

    assert_eq!(bigger_bitset.into_inner(), 0b0000000010101010);

    let combined: Bitset16 = bitset.combine(other);

    assert_eq!(combined.into_inner(), 0b1111000010101010);

    let (bitset, other) = combined.split::<Bitset8, Bitset8>();

    assert_eq!(bitset.into_inner(), 0b10101010);
    assert_eq!(other.into_inner(), 0b11110000);

    // Collect in other collections and construct from them.
    let v: Vec<Bit> = bitset.bits().rev().collect();

    assert_eq!(&v, &[One, Zero, One, Zero, One, Zero, One, Zero]);

    let bitset = Bitset8::from_iterable(&v);
    assert_eq!(bitset.into_inner(), 0b01010101);
}

```

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.