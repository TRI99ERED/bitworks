pub trait Bitenum: Sized + TryFrom<u8> {
    const COUNT: usize;

    fn from_pos(pos: usize) -> Option<Self> {
        if pos >= Self::COUNT {
            None
        } else {
            Some((pos as u8).try_into().ok()).flatten()
        }
    }
}

#[macro_export]
macro_rules! count_variants {
    () => { 0 };
    ($head:ident $(, $tail:ident)*) => { 1 + count_variants!($($tail),*) };
}

#[macro_export]
macro_rules! benum {
    {enum $name: ident {
        $($variant: ident $(= $repr: expr)?),+ $(,)?
    }} => {
        #[repr(u8)]
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        enum $name {
            $($variant $(= $repr)?),+
        }

        impl TryFrom<u8> for $name {
            type Error = String;

            fn try_from(value: u8) -> Result<Self, Self::Error> {
                match value {
                    $(n if n == $name::$variant as u8 => Ok($name::$variant),)+
                    _ => Err(format!("Invalid value for {}", stringify!($name))),
                }
            }
        }

        impl Bitenum for $name {
            const COUNT: usize = count_variants!($($variant),+);
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    benum! {
        enum Letters {
            A = 0b00000001,
            B = 0b00000010,
            C = 0b00000100,
            D = 0b00001000,
            E = 0b00010000,
            F = 0b00100000,
            G = 0b01000000,
            H = 0b10000000,
        }
    }

    #[test]
    fn testing() {
        for i in 0..10 {
            let letter = Letters::try_from(i);
            println!("{:?}", letter);
        }
    }
}
