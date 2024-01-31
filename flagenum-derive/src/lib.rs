extern crate proc_macro;
extern crate syn;
#[macro_use]
extern crate quote;
extern crate proc_macro2;

use proc_macro::TokenStream;
use proc_macro2::Span;
use syn::{parse_macro_input, DeriveInput, Ident};

#[proc_macro_derive(Flagenum)]
pub fn flagenum(input: TokenStream) -> TokenStream {
    // Parse the string representation
    let ast = parse_macro_input!(input as DeriveInput);

    // Build the impl
    impl_flagenum(&ast)
}

fn impl_flagenum(ast: &DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let count = match &ast.data {
        syn::Data::Enum(data) => data.variants.len(),
        _ => panic!("Flagenum can only be derived for enums!"),
    };
    let ty = match count {
        0..=7 => Ident::new("Bitfield8", Span::call_site()),
        9..=15 => Ident::new("Bitfield16", Span::call_site()),
        17..=31 => Ident::new("Bitfield32", Span::call_site()),
        33..=63 => Ident::new("Bitfield64", Span::call_site()),
        65..=127 => Ident::new("Bitfield128", Span::call_site()),
        _ => panic!("The enum has too many variants! Can't exceed 128!"),
    };
    quote! {
        impl Flagenum for #name {
            type Bitfield = #ty;
            const COUNT: usize = #count;
        }
    }
    .into()
}
