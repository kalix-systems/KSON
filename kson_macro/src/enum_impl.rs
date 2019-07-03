use proc_macro2::Span;
use quote::quote;
use syn::*;

pub fn kson_rep(name: Ident, data: DataEnum) -> proc_macro2::TokenStream {
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

    // to_kson
    let impl_to_kson = {
        let branches =
            variant_id_fields
                .iter()
                .map(|(variant, field_idents, fields, ident_string)| {
                    match &fields {
                        // unit-like struct
                        Fields::Unit => {
                            quote! {
                                #name::#variant => {
                                    vec![Kson::from_buf(#ident_string)].to_kson()
                                }
                            }
                        }
                        // tuple struct
                        Fields::Unnamed(_fields) => {
                            let kargs = field_idents
                                .iter()
                                .map(|variant_ident| quote! {#variant_ident.to_kson()});

                            if kargs.len() == 0 {
                                quote! {
                                    #name::#variant => {
                                        vec![Kson::from_buf(#ident_string)].to_kson()
                                    }
                                }
                            } else {
                                quote! {
                                    #name::#variant(#(#field_idents),*) => {
                                        vec![
                                            Kson::from_buf(#ident_string), #(#kargs),*
                                        ].to_kson()
                                    }
                                }
                            }
                        }
                        // c-style struct
                        Fields::Named(_fields) => {
                            let field_strs: Vec<String> = field_idents
                                .iter()
                                .map(std::string::ToString::to_string)
                                .collect();
                            let pairs = field_idents.iter().zip(field_strs.iter()).map(
                                |(ident, ident_string)| {
                                    quote! {
                                        (#ident_string, #ident.to_kson())
                                    }
                                },
                            );

                            quote! {
                                #name::#variant{ #(#field_idents),*} =>  {
                                    let vm: VecMap<Bytes, Kson> = vec![#(#pairs),*]
                                        .into_iter()
                                        .map(|(k, v)| (Bytes::from_buf(k), v.to_kson())).collect();
                                    vec![Kson::from_buf(#ident_string), vm.to_kson()].to_kson()
                                }
                            }
                        }
                    }
                });
        quote! {
            fn to_kson(&self) -> Kson {
                match self {
                    #(#branches)*
                }
            }
        }
    };

    // into_kson
    let impl_into_kson = {
        let branches = variant_id_fields.iter().map(
            |(variant, field_idents, fields, ident_string)| {
                match &fields {
                    // unit-like struct
                    Fields::Unit => {
                        quote! {
                            #name::#variant => {
                                vec![Kson::from_buf(#ident_string)].into_kson()
                            }
                        }
                    }
                    // tuple struct
                    Fields::Unnamed(_fields) => {
                        let kargs = field_idents
                            .iter()
                            .map(|variant_ident| quote! {#variant_ident.into_kson()});
                        quote! {
                            #name::#variant(#(#field_idents),*) => {
                                vec![
                                    Kson::from_buf(#ident_string), #(#kargs),*
                                ].into_kson()
                            }
                        }
                    }
                    // c-style struct
                    Fields::Named(_fields) => {
                        let field_strs: Vec<String> = field_idents
                            .iter()
                            .map(std::string::ToString::to_string)
                            .collect();
                        let pairs = field_idents.iter().zip(field_strs.iter()).map(
                            |(ident, ident_string)| {
                                quote! {
                                    (#ident_string, #ident.into_kson())
                                }
                            },
                        );

                        quote! {
                            #name::#variant{ #(#field_idents),*} =>  {
                                let vm: VecMap<Bytes, Kson> = vec![#(#pairs),*]
                                    .into_iter()
                                    .map(|(k, v)| (Bytes::from_buf(k), v.into_kson())).collect();
                                vec![Kson::from_buf(#ident_string), vm.into_kson()].into_kson()
                            }
                        }
                    }
                }
            },
        );
        quote! {
            fn into_kson(self) -> Kson {
                match self {
                    #(#branches)*
                }
            }
        }
    };

    // from_kson
    let impl_from_kson = {
        let pairs = variant_id_fields.into_iter().map(
            |(m_variant, m_field_idents, m_fields, m_ident_string)| {
                let constructor = quote! { #name::#m_variant };

                match &m_fields {
                    // Unit-like variant
                    Fields::Unit => {
                        quote! {
                            #m_ident_string => {
                                // there shouldn't be any fields left
                                match k_iter.next() {
                                    None => Ok(#constructor),
                                    _ => { 
                                        bail!(
                                                "Unit-like variants shouldn't have fields, \
                                                but a field was found."
                                        )
                                    }
                                }
                            }
                        }
                    }
                    // Named-tuple variant
                    Fields::Unnamed(_fields) => {
                        let popped = m_fields.iter().map(|_| quote! { pop_kson(&mut k_iter)? });

                        quote! {
                            #m_ident_string => {
                                {
                                    // evaluate the iterator
                                    let out = Ok(#constructor(#(#popped),*));

                                    // there shouldn't be any fields left
                                    match k_iter.next() {
                                        None => out,
                                        _ => bail!(
                                                    "Too many fields found for `{}`",
                                                    #m_ident_string
                                        ),
                                    }
                                }
                            }
                        }
                    }
                    // C-style struct variant
                    Fields::Named(_fields) => {
                        let field_strs: Vec<String> = m_field_idents
                            .iter()
                            .map(std::string::ToString::to_string)
                            .collect();

                        let popped = m_field_idents
                            .iter()
                            .map(|ident| quote! { #ident: pop_kson(&mut fields)? });

                        quote! {
                            #m_ident_string => {
                                #[inline]
                                fn helper(ks: Kson, names: &[&str]) -> Result<Vec<Kson>, Error> {
                                    let mut m = ks.into_map()?;
                                    let out_fields: Option<Vec<Kson>> = names
                                        .iter()
                                        .map(|n| m.remove(&Bytes::from_buf(*n)))
                                        .collect();

                                    let (out, actual_len) = match out_fields {
                                        None => (Err(format_err!("C-style structs must have at least one field, but none were found")), 0),
                                        Some(v) => { 
                                            let vector = v;
                                            let vec_len = vector.len();
                                            (Ok(vector), vec_len) 
                                        },
                                    };

                                    if m.is_empty() {
                                        out
                                    } else {
                                        bail!(
                                                "Found {actual} fields, expected {exp} for `{name}`",
                                                         actual = actual_len,
                                                         exp = names.len(),
                                                         name = #m_ident_string,
                                                         )
                                    }
                                }

                                let km = match k_iter.next() {
                                    None => {
                                        bail!("C-style structs must have at least one field, but none were found")
                                    }
                                    Some(km) => km,
                                };

                                let mut fields = helper(km, &[#(#field_strs),*])?.into_iter();
                                let out = Ok(#constructor {#(#popped),*});

                                if k_iter.next().is_none() && fields.next().is_none() {
                                    out
                                } else {
                                    bail!(
                                            "Encoding for `{}` is malformed, \
                                                      it contains too many elements",
                                                      #m_ident_string)
                                }
                            }
                        }
                    }
                }
            },
            );
        quote! {
            fn from_kson(ks: Kson) -> Result<Self, Error> {
                let mut k_iter = ks.into_vec()?.into_iter();

                let match_string: String = match k_iter.next() {
                    Some(ks) => String::from_kson(ks),
                    None => bail!("Name of variant not found")
                }?;

                match match_string.as_str() {
                    #(#pairs)*
                    unknown => bail!("`{}` is not a variant of this enum", unknown),
                }
            }
        }
    };

    quote! {
        impl KsonRep for #name {
            #impl_into_kson
            #impl_to_kson
            #impl_from_kson
        }
    }
}
