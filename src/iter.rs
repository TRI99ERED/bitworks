//! Module containing BitIter.

use crate::prelude::{Bitfield, BitfieldIndex};

/// Iterator over bits of T, where T implements Bitfield.
#[derive(Clone)]
pub struct BitIter<T>
where
    T: Bitfield,
{
    bitfield: T,
    index: BitfieldIndex<T>,
}

impl<T> BitIter<T>
where
    T: Bitfield,
{
    /// Constructs new value of BitIter.
    #[inline(always)]
    pub fn new(bitfield: T, index: BitfieldIndex<T>) -> Self {
        BitIter::<T> { bitfield, index }
    }
}

impl<T> Iterator for BitIter<T>
where
    T: Bitfield,
{
    type Item = bool;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index.value() <= BitfieldIndex::<T>::MAX.value() {
            let bit = (self.bitfield.clone() >> self.index.clone())
                & T::from(BitfieldIndex::<T>::MIN)
                != T::NONE;
            self.index = self.index.__add(BitfieldIndex::<T>::ONE);
            Some(bit)
        } else {
            None
        }
    }
}
