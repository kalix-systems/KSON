#![recursion_limit = "128"]

extern crate proc_macro;
extern crate proc_macro2;

/// Support for enum auto-derive.
mod enum_impl;
/// Support for struct auto-derive.
mod struct_impl;

use proc_macro::TokenStream;
use quote::quote;
use syn::*;

#[proc_macro_derive(KsonRep)]
pub fn kson_rep_derive(input: TokenStream) -> TokenStream {
    // Construct a representation of Rust code as a syntax tree
    // that we can manipulate
    let ast = syn::parse(input).unwrap();

    // Build the trait implementation
    impl_kson_rep_macro(&ast)
}

fn impl_kson_rep_macro(ast: &syn::DeriveInput) -> TokenStream {
    let name = ast.ident.clone();
    let imp = match ast.data.clone() {
        Data::Struct(sd) => struct_impl::kson_rep(name, sd),
        Data::Enum(ed) => enum_impl::kson_rep(name, ed),
        _ => quote! {},
    };
    imp.into()
}
