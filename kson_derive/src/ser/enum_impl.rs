use proc_macro2::Span;
use quote::quote;
use syn::*;

pub fn kson_ser(name: Ident, data: DataEnum) -> proc_macro2::TokenStream {
    let variant_id_fields: Vec<(Ident, Vec<Ident>, Fields, String)> = data
        .variants // variants of the enum
        .iter()
        .map(|variant| {
            // fields of the variant
            let field_idents = match &variant.fields {
                Fields::Named(_fields) => {
                    variant
                        .fields
                        .iter()
                        .map(|field| field.ident.clone().unwrap())
                        .collect()
                }
                _ => {
                    (0..variant.fields.iter().len())
                        .map(|i| Ident::new(&format!("field{}", i), Span::call_site()))
                        .collect()
                }
            };
            (
                variant.ident.clone(),
                field_idents,
                variant.fields.clone(),
                variant.ident.to_string(),
            )
        })
        .collect();

    // ser
    let impl_ser = {
        let branches =
            variant_id_fields
                .iter()
                .map(|(variant, field_idents, fields, ident_string)| {
                    match &fields {
                        // C-style
                        Fields::Named(_fields) => {
                            let seq_len: usize = field_idents.len() + 1;

                            let field_strs: Vec<String> = field_idents
                                .iter()
                                .map(std::string::ToString::to_string)
                                .collect();
                            let pairs = field_idents.iter().zip(field_strs.iter()).map(
                                |(ident, ident_string)| {
                                    quote! {
                                        #ident_string, #ident
                                    }
                                },
                            );

                            quote! {
                                #name::#variant{ #(#field_idents),*} =>  {
                                    let mut sequence_state = s.seq_start(#seq_len);
                                    s.seq_put(&mut sequence_state, #ident_string);

                                    let mut map_state = s.map_start(#seq_len - 1);
                                    #(s.map_put(&mut map_state, #pairs);)*
                                    s.map_finalize(map_state);

                                    s.seq_finalize(sequence_state);
                                }
                            }
                        }
                        // Tuple
                        Fields::Unnamed(_fields) => {
                            let seq_len: usize = field_idents.len() + 1;

                            let kargs = field_idents
                                .iter()
                                .map(|variant_ident| quote! {#variant_ident});
                            quote! {
                                #name::#variant(#(#field_idents),*) => {
                                    let mut state = s.seq_start(#seq_len);
                                    // name
                                    s.seq_put(&mut state, #ident_string);

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
                                    s.seq_put(&mut state, #ident_string);
                                    s.seq_finalize(state);
                                }
                            }
                        }
                    }
                });
        quote! {
            fn ser<S: Serializer>(self, s: &mut S) {
                match self {
                    #(#branches)*
                }
            }
        }
    };

    quote! {
        impl Ser for #name {
            #impl_ser
        }
    }
}
