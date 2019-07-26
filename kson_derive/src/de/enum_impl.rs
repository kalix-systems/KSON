use quote::quote;
use syn::*;

pub fn kson_de(name: Ident, data: DataEnum) -> proc_macro2::TokenStream {
    let pairs = data.variants.iter().cloned().map(
        |variant| {
            let variant_ident = variant.ident;
            let name_string = variant_ident.to_string();
            let constructor = quote! { #name::#variant_ident };
            let fields = variant.fields;
            let exp_len = fields.iter().len();

            match &fields {
                // C-style struct variant
                Fields::Named(_fields) => {
                    let mut field_stuff: Vec<(Ident, String)> = fields
                        .iter()
                        .map(|field| field.ident.clone().unwrap())
                        .map(|field| (field.clone(), field.to_string()))
                        .collect();

                    field_stuff.sort_unstable_by(|(_, k1), (_, k2)| k1.cmp(k2));

                    let (field_names, field_strings): (Vec<Ident>, Vec<String>) = field_stuff.into_iter().unzip();

                    quote! {
                        #name_string => {
                            let (mut state, len) = d.take_map()?;
                            if len != #exp_len {
                                bail!(
                                    "Wrong number of fields for `{}`: expected {}, found {}",
                                    #name_string,
                                    #exp_len,
                                    len
                                )
                            }

                            Ok(#constructor {
                                #(#field_names: de::check_entry(d.take_key(&mut state)?, d.take_val(&mut state)?, #field_strings)?,)*

                            })
                        }
                    }
                }
                // Named-tuple variant
                Fields::Unnamed(_fields) => {
                    let typ = fields.iter().map(|f| f.ty.clone());

                    quote! {
                        #name_string => {
                            {
                                if len - 1 != #exp_len {
                                    bail!(
                                        "Wrong number of fields for `{}`:
                                        expected {}, but found {}",
                                        #name_string,
                                        #exp_len,
                                        len - 1
                                    )
                                }

                                Ok(#constructor(#(d.take::<#typ>(&mut iter)?),*))
                            }
                        }
                    }
                }
                // Unit-like variant
                Fields::Unit => {
                    quote! {
                        #name_string => {
                            // there shouldn't be any fields, only a name
                            if len != 1 {
                                bail!(
                                    "`{}` is unit-like and shouldn't have fields, but a field was found.",
                                    #name_string,
                                    )
                            }

                            Ok(#constructor)
                        }
                    }
                }
            }
        },
        );

    quote! {
        impl De for #name {
            fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
                let (mut iter, len) = d.read()?;

                match d.take::<String>(&mut iter)?.as_str() {
                    #(#pairs)*
                    unknown => bail!("`{}` is not a variant of this enum", unknown),
                }
            }
        }
    }
}
