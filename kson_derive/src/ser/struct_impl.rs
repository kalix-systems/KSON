use proc_macro2::Literal;
use quote::quote;
use syn::*;

pub fn kson_ser(name: Ident, data: DataStruct) -> proc_macro2::TokenStream {
    let impl_ser = match data.fields {
        // C-style structs
        Fields::Named(fields) => {
            let field_idents: Vec<Ident> = Fields::Named(fields)
                .iter()
                .map(|field| field.ident.clone().unwrap())
                .collect();
            let field_strs: Vec<String> = field_idents
                .iter()
                .map(std::string::ToString::to_string)
                .collect();

            let length = field_idents.len();

            let impl_ser = {
                let pairs = field_idents
                    .iter()
                    .zip(field_strs.iter())
                    .map(|(ident, ident_string)| quote! { #ident_string, self.#ident });

                quote! {
                    let mut state = s.map_start(#length);

                    #(s.map_put(&mut state, #pairs);)*

                    s.map_finalize(state);
                }
            };

            impl_ser
        }
        // Tuple structs
        Fields::Unnamed(fields) => {
            let fields: Vec<Type> = Fields::Unnamed(fields)
                .iter()
                .map(|field| field.ty.clone())
                .collect();
            let seq_len: usize = fields.len() + 1;

            let ident_string = name.to_string();

            let impl_ser = {
                let kargs = (0..fields.len())
                    .map(Literal::usize_unsuffixed)
                    .map(|index| quote! {self.#index});

                quote! {
                    let mut state = s.seq_start(#seq_len);
                    // name
                    s.seq_put(&mut state, #ident_string);

                    // fields
                    #(s.seq_put(&mut state, #kargs);)*

                    s.seq_finalize(state);
                }
            };

            impl_ser
        }
        // Unit-like structs
        Fields::Unit => {
            let ident_string = name.to_string();

            let impl_ser = {
                quote! {
                    #ident_string.ser(s)
                }
            };

            impl_ser
        }
    };

    quote! {
        impl Ser for #name {
            fn ser<S: Serializer>(self, s: &mut S) {
                #impl_ser
            }
        }
    }
}
