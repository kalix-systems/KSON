use proc_macro2::Literal;
use quote::quote;
use syn::*;

pub fn kson_rep(name: Ident, data: DataStruct) -> proc_macro2::TokenStream {
    let (impl_to_kson, impl_into_kson, impl_from_kson) = match data.fields {
        // C-style structs
        Fields::Named(fields) => {
            let field_names: Vec<Ident> = Fields::Named(fields)
                .iter()
                .map(|field| field.ident.clone().unwrap())
                .collect();
            let field_strs: Vec<String> = field_names
                .iter()
                .map(std::string::ToString::to_string)
                .collect();

            // to_kson
            let impl_to_kson = {
                let pairs =
                    field_names
                        .iter()
                        .zip(field_strs.iter())
                        .map(|(ident, ident_string)| {
                            quote! {
                                (#ident_string, self.#ident.to_kson())
                            }
                        });

                quote! {
                    fn to_kson(&self) -> Kson {
                        let vm: VecMap<Bytes, Kson> =
                            vec![#(#pairs),*]
                            .into_iter()
                            .map(|(k, v)| (Bytes::from_buf(k), v)).collect();
                        vm.to_kson()
                    }
                }
            };

            // into_kson
            let impl_into_kson = {
                let pairs = field_names.iter().zip(field_strs.iter()).map(
                    |(ident, ident_string)| quote! { (#ident_string, self.#ident.into_kson()) },
                );
                quote! {
                    fn into_kson(self) -> Kson {
                        let vm: VecMap<Bytes, Kson> =
                            vec![#(#pairs),*]
                            .into_iter()
                            .map(|(k, v)| (Bytes::from_buf(k), v)).collect();
                        vm.into_kson()
                    }
                }
            };

            // from_kson
            let impl_from_kson = {
                let ident_string = name.to_string();
                let popped = field_names
                    .iter()
                    .map(|ident| quote! { #ident: pop_kson(&mut fields)? });
                quote! {
                    fn from_kson(ks: Kson) -> Result<Self, Error> {
                        #[inline]
                        fn helper(ks: Kson, names: &[&'static str])
                            -> Result<Vec<Kson>, Error> {
                                let mut m = ks.into_map()?;
                                let outs: Vec<Kson> = names
                                    .iter()
                                    .filter_map(|n| m.remove(&Bytes::from_buf(n)))
                                    .collect();
                                if outs.len() == names.len() && m.len() == 0 {
                                    Ok(outs)
                                } else {
                                    bail!(
                                         "Found {actual} fields, expected {exp} for `{name}`",
                                                     actual = outs.len(),
                                                     exp = names.len(),
                                                     name = #ident_string,
                                        )
                                }
                            }

                        let mut fields = helper(ks, &[#(#field_strs),*])?.into_iter();

                        Ok(#name {#(#popped),*})
                    }
                }
            };
            (impl_to_kson, impl_into_kson, impl_from_kson)
        }
        // Tuple structs
        Fields::Unnamed(fields) => {
            let fields: Vec<Type> = Fields::Unnamed(fields)
                .iter()
                .map(|field| field.ty.clone())
                .collect();
            let fields_len: usize = fields.len();

            let ident_string = name.to_string();

            // to_kson
            let impl_to_kson = {
                let kargs = (0..fields_len)
                    .map(Literal::usize_unsuffixed)
                    .map(|index| quote! {self.#index.to_kson()});

                let elements = quote! {
                    vec![Kson::from_buf(#ident_string), #(#kargs),*].to_kson()
                };

                quote! {
                    fn to_kson(&self) -> Kson {
                        #elements
                    }
                }
            };

            let impl_into_kson = {
                let kargs = (0..fields_len)
                    .map(Literal::usize_unsuffixed)
                    .map(|index| quote! {self.#index.to_kson()});

                let elements = quote! {
                    vec![Kson::from_buf(#ident_string), #(#kargs),*].to_kson()
                };

                quote! {
                    fn into_kson(self) -> Kson {
                        #elements
                    }
                }
            };

            // from_kson
            let impl_from_kson = {
                let match_string = quote! { String::from_kson(match k_iter.next() {
                        None => bail!("Missing name of tuple-like struct"),
                        Some(ks) => ks,
                    })?.as_str()
                };

                let popped = (0..fields_len).map(|_| quote! { pop_kson(&mut k_iter)? });
                let out = quote! {
                    {
                        let tuple_struct = Ok(#name(#(#popped),*));
                        match k_iter.next() {
                            None => tuple_struct,
                            _ => bail!("Found too many fields"),
                        }
                    }
                };

                quote! {
                    fn from_kson(ks: Kson) -> Result<Self, Error> {
                        let mut k_iter = ks.into_vec()?.into_iter();

                        match #match_string {
                            #ident_string => #out,
                            unknown => {
                                bail!("Expected `{}`, found `{}`", #ident_string, unknown)
                            }
                        }
                    }
                }
            };

            (impl_to_kson, impl_into_kson, impl_from_kson)
        }
        // Unit-like structs
        Fields::Unit => {
            let ident_string = name.to_string();
            // to_kson
            let impl_to_kson = {
                quote! {
                    fn to_kson(&self) -> Kson {
                        Kson::from_buf(#ident_string)
                    }
                }
            };

            // into_kson
            let impl_into_kson = {
                quote! {
                    fn into_kson(self) -> Kson {
                        Kson::from_buf(#ident_string)
                    }
                }
            };

            // from_kson
            let impl_from_kson = {
                quote! {
                    fn from_kson(ks: Kson) -> Result<Self, Error> {
                        match String::from_kson(ks)?.as_str() {
                            #ident_string => Ok(Self),
                            unknown => {
                                bail!("`{}` is not the name of this struct", unknown)
                            }
                        }
                    }
                }
            };
            (impl_to_kson, impl_into_kson, impl_from_kson)
        }
    };

    quote! {
        impl KsonRep for #name {
            #impl_to_kson
            #impl_into_kson
            #impl_from_kson
        }
    }
}
