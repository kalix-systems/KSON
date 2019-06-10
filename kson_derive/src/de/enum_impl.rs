use proc_macro2::Span;
use quote::quote;
use syn::*;

pub fn kson_de(name: Ident, data: DataEnum) -> proc_macro2::TokenStream {
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

    // de
    let impl_de = {
        let pairs = variant_id_fields.into_iter().map(
            |(m_variant, m_field_idents, m_fields, m_ident_string)| {
                let constructor = quote! { #name::#m_variant };

                match &m_fields {
                    // Unit-like variant
                    Fields::Unit => {
                        quote! {
                            #m_ident_string => {
                                // there shouldn't be any fields left
                                if len != 1 {
                                    bail!(
                                        "`{}` is unit-like and shouldn't have fields, but a field was found.",
                                        #m_ident_string,
                                        )
                                } else {
                                    Ok(#constructor)
                                }
                            }
                        }
                    }
                    // Named-tuple variant
                    Fields::Unnamed(_fields) => {
                        let exp_len = m_field_idents.len();
                        let typ = m_fields.iter().map(|f| f.ty.clone());

                        quote! {
                            #m_ident_string => {
                                {
                                    if len - 1 != #exp_len {
                                        bail!(
                                            "Wrong number of fields for `{}`:
                                        expected {}, but found {}",
                                        #m_ident_string,
                                        #exp_len,
                                        len - 1
                                        )
                                    }

                                    // evaluate the iterator
                                    let out = Ok(#constructor(#(d.take::<#typ>(&mut iter)?),*));

                                    out
                                }
                            }
                        }
                    }
                    // C-style struct variant
                    Fields::Named(_fields) => {
                        let mut field_stuff: Vec<(Ident, String)> = m_fields
                            .iter()
                            .map(|field| field.ident.clone().unwrap())
                            .map(|field| (field.clone(), field.to_string()))
                            .collect();

                        field_stuff.sort_unstable_by(|(_, k1), (_, k2)| k1.cmp(k2));

                        let (field_names, field_strings): (Vec<Ident>, Vec<String>) = field_stuff.into_iter().unzip();

                        let exp_len = field_names.len();

                        quote! {
                            #m_ident_string => {
                                let (mut state, len) = d.take_map()?;
                                if len != #exp_len {
                                    bail!(
                                        "Wrong number of fields for `{}`: expected {}, found {}",
                                        #m_ident_string,
                                        #exp_len,
                                        len
                                    )
                                }
                                let strct = #constructor {
                                    #(#field_names: de::check_entry(d.take_key(&mut state)?, d.take_val(&mut state)?, #field_strings)?,)*

                                };

                                Ok(strct)
                            }
                        }
                    }
                }
            },
            );
        quote! {
            let (mut iter, len) = d.read()?;

            match d.take::<String>(&mut iter)?.as_str() {
                #(#pairs)*
                unknown => bail!("`{}` is not a variant of this enum", unknown),
            }
        }
    };

    quote! {
        impl De for #name {
            fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
                #impl_de
            }
        }
    }
}
