#![recursion_limit = "128"]

extern crate proc_macro;
extern crate proc_macro2;

mod de;
mod ser;

use proc_macro::TokenStream;
use quote::quote;
use syn::*;

fn struct_impl(name: Ident, sd: DataStruct) -> TokenStream {
    let kser = ser::struct_impl::kson_ser(name.clone(), sd.clone());
    let kser_ref = ser::struct_ref_impl::kson_ser_ref(name.clone(), sd.clone());
    let kde = de::struct_impl::kson_de(name, sd);

    let imp = quote! {
        #kser
        #kde
        #kser_ref
    };

    imp.into()
}

fn enum_impl(name: Ident, sd: DataEnum) -> TokenStream {
    let kser = ser::enum_impl::kson_ser(name.clone(), sd.clone());
    let kde = de::enum_impl::kson_de(name, sd);

    let imp = quote! {
        #kser
        #kde
    };

    imp.into()
}

#[proc_macro_derive(KSerDe)]
pub fn kserde_derive(input: TokenStream) -> TokenStream {
    // Construct a representation of Rust code as a syntax tree
    // that we can manipulate
    let ast = syn::parse(input).unwrap();

    // Build the trait implementation
    impl_kserde_macro(&ast)
}

fn impl_kserde_macro(ast: &syn::DeriveInput) -> TokenStream {
    let name = ast.ident.clone();

    match ast.data.clone() {
        Data::Struct(sd) => struct_impl(name, sd),
        Data::Enum(ed) => enum_impl(name, ed),
        _ => quote! {}.into(),
    }
}
