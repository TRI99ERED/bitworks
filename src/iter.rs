use std::{
    mem::size_of,
    ops::{BitAnd, Shr, ShrAssign},
};

#[derive(Clone, Copy)]
pub struct BitIter<T>
where
    T: Clone + Copy + PartialEq + Eq + BitAnd<Output = T> + Shr<Output = T> + From<u8>,
{
    pub bitfield: T,
    pub index: u8,
}

impl<T> Iterator for BitIter<T>
where
    T: Clone + Copy + PartialEq + Eq + BitAnd<Output = T> + Shr<Output = T> + From<u8>,
{
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < (size_of::<T>() * 8) as u8 {
            let bit = (self.bitfield >> self.index.into()) & 1u8.into() != 0u8.into();
            self.index += 1;
            Some(bit)
        } else {
            None
        }
    }
}
