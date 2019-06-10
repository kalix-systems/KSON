use quote::quote;
use syn::*;

pub fn kson_de(name: Ident, data: DataStruct) -> proc_macro2::TokenStream {
    let impl_de = match data.fields {
        // C-style structs
        Fields::Named(fields) => {
            let mut field_stuff: Vec<(Ident, String)> = Fields::Named(fields)
                .iter()
                .map(|field| field.ident.clone().unwrap())
                .map(|field| (field.clone(), field.to_string()))
                .collect();

            field_stuff.sort_unstable_by(|(_, k1), (_, k2)| k1.cmp(k2));

            let (field_names, field_strings): (Vec<Ident>, Vec<String>) =
                field_stuff.into_iter().unzip();

            let exp_len = field_names.len();

            // de
            let impl_de = {
                let ident_string = name.to_string();
                quote! {
                    let (mut state, len) = d.take_map()?;
                    if len == #exp_len {
                        let strct = #name {
                            #(#field_names: de::check_entry(d.take_key(&mut state)?, d.take_val(&mut state)?, #field_strings)?,)*
                        };
                        Ok(strct)
                    }
                    else {
                        bail!("`{}` has {} fields, found {}",
                              #ident_string,
                              #exp_len,
                              len,
                              )
                    }

                }
            };
            impl_de
        }
        // Tuple structs
        Fields::Unnamed(fields) => {
            let fields: Vec<Type> = Fields::Unnamed(fields)
                .iter()
                .map(|field| field.ty.clone())
                .collect();
            let fields_len: usize = fields.len();

            let ident_string = name.to_string();

            // de
            let impl_de = {
                let exp_len = fields_len;

                let match_string = quote! { match d.take::<String>(&mut iter) {
                    Ok(s) => s,
                    Err(e) => bail!("Missing name of tuple-like struct: {}", e),
                }.as_str()};

                let out = quote! {
                    Ok(#name(#(d.take::<#fields>(&mut iter)?,)*))
                };

                quote! {
                    let (mut iter, len) = d.read()?;
                    if len - 1 != #exp_len {
                        bail!("`{}` has {} fields, found {}",
                              #ident_string,
                              #exp_len,
                              len - 1,
                        )
                    }

                    match #match_string {
                        #ident_string => #out,
                        unknown => {
                            bail!("Expected `{}`, found `{}`", #ident_string, unknown)
                        }
                    }
                }
            };
            impl_de
        }
        // Unit-like structs
        Fields::Unit => {
            let ident_string = name.to_string();

            // de
            let impl_de = {
                quote! {
                    match String::de(d)?.as_str() {
                        #ident_string => Ok(Self),
                        unknown => {
                            bail!("`{}` is not the name of this struct", unknown)
                        }
                    }
                }
            };
            impl_de
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
