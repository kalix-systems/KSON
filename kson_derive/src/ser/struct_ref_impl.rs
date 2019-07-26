use proc_macro2::Literal;
use quote::quote;
use syn::*;

pub fn kson_ser_ref(name: Ident, data: DataStruct) -> proc_macro2::TokenStream {
    let impl_ser = match data.fields {
        // C-style structs
        Fields::Named(fields) => {
            let mut field_stuff: Vec<(Ident, String)> = Fields::Named(fields)
                .iter()
                .map(|field| field.ident.clone().unwrap())
                .map(|ident| (ident.clone(), ident.to_string()))
                .collect();

            field_stuff.sort_unstable_by(|(_, k1), (_, k2)| k1.cmp(k2));

            let length = field_stuff.len();

            let pairs = field_stuff
                .into_iter()
                .map(|(ident, ident_string)| quote! { #ident_string, &(self.#ident) });

            quote! {
                let mut state = s.map_start(#length);

                #(s.map_put(&mut state, #pairs);)*

                s.map_finalize(state);
            }
        }
        // Tuple structs
        Fields::Unnamed(fields) => {
            let fields: Vec<Type> = Fields::Unnamed(fields)
                .iter()
                .map(|field| field.ty.clone())
                .collect();
            let seq_len: usize = fields.len() + 1;

            let ident_string = name.to_string();

            let kargs = (0..fields.len())
                .map(Literal::usize_unsuffixed)
                .map(|index| quote! {&(self.#index)});

            quote! {
                let mut state = s.seq_start(#seq_len);
                // name
                s.seq_put(&mut state, #ident_string);

                // fields
                #(s.seq_put(&mut state, #kargs);)*

                s.seq_finalize(state);
            }
        }
        // Unit-like structs
        Fields::Unit => {
            let ident_string = name.to_string();

            quote! {
                #ident_string.ser(s)
            }
        }
    };

    quote! {
        impl Ser for &#name {
            fn ser<S: Serializer>(self, s: &mut S) {
                #impl_ser
            }
        }

    }
}
