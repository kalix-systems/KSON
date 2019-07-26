use proc_macro2::Span;
use quote::quote;
use syn::*;

pub fn kson_ser(name: Ident, data: DataEnum) -> proc_macro2::TokenStream {
    let branches = data.variants.iter().map(|variant| {
        let fields = variant.fields.clone();
        let variant = variant.ident.clone();
        let name_string = variant.to_string();

        match &fields {
            // C-style
            Fields::Named(_fields) => {
                let mut field_stuff: Vec<(Ident, String)> = fields
                    .iter()
                    .cloned()
                    .map(|field| field.ident.unwrap())
                    .map(|ident| (ident.clone(), ident.to_string()))
                    .collect();

                field_stuff.sort_unstable_by(|(_, k1), (_, k2)| k1.cmp(k2));

                let field_idents = field_stuff.iter().map(|(ident, _)| ident.clone());
                let seq_len: usize = field_idents.len() + 1;

                let pairs = field_stuff.iter().map(|(ident, ident_string)| {
                    quote! {
                        #ident_string, #ident
                    }
                });

                quote! {
                    #name::#variant{ #(#field_idents),*} =>  {
                        let mut sequence_state = s.seq_start(#seq_len);
                        s.seq_put(&mut sequence_state, #name_string);

                        let mut map_state = s.map_start(#seq_len - 1);
                        #(s.map_put(&mut map_state, #pairs);)*
                        s.map_finalize(map_state);

                        s.seq_finalize(sequence_state);
                    }
                }
            }
            // Tuple
            Fields::Unnamed(_fields) => {
                let field_idents: Vec<Ident> = (0..fields.iter().len())
                    .map(|i| Ident::new(&format!("field{}", i), Span::call_site()))
                    .collect();

                let seq_len: usize = field_idents.len() + 1;

                let kargs = field_idents
                    .clone()
                    .into_iter()
                    .map(|variant_ident| quote! {#variant_ident});

                quote! {
                    #name::#variant(#(#field_idents),*) => {
                        let mut state = s.seq_start(#seq_len);
                        // name
                        s.seq_put(&mut state, #name_string);

                        // fields
                        #(s.seq_put(&mut state, #kargs);)*

                        s.seq_finalize(state);
                    }
                }
            }
            // Unit-like
            Fields::Unit => {
                quote! {
                    #name::#variant => {
                        let mut state = s.seq_start(1);
                        s.seq_put(&mut state, #name_string);
                        s.seq_finalize(state);
                    }
                }
            }
        }
    });

    let impl_ser = quote! {
            fn ser<S: Serializer>(self, s: &mut S) {
                match self {
                    #(#branches)*
                }
            }
    };

    quote! {
        impl Ser for #name {
            #impl_ser
        }

        impl Ser for &#name {
            #impl_ser
        }
    }
}
