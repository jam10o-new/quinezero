use proc_macro::TokenStream;
use quote::{quote, format_ident};
use syn::{parse_macro_input, Data, DeriveInput, Fields, Ident};

#[proc_macro_derive(LazyDeserializer)]
pub fn lazy_deserializer_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = &input.ident;
    let iter_name = Ident::new(&format!("{}LazyDeserializer", name), name.span());
    let mut arms = Vec::new();
    let mut reverse_arms = Vec::new();
    let mut inner_arms = Vec::new();

    if let Data::Enum(data_enum) = input.data {
        let first_variant_name = &data_enum.variants[0].ident;
        let first_variant_fields_count = match &data_enum.variants[0].fields {
            Fields::Unnamed(fields) => fields.unnamed.len(),
            _ => 0,
        };

        assert_eq!(
            first_variant_fields_count, 0,
            "First variant of enum: {} must have no fields", name
        );

        for (i_usize, variant) in data_enum.variants.iter().enumerate() {
            let i = i_usize as u8;
            let variant_name = &variant.ident;
        
            let arm;
            let reverse_arm;
            let inner_arm;

            match &variant.fields {
                Fields::Unnamed(fields) => {
                    let number_of_fields = fields.unnamed.len();
                    let fields: Vec<_> = (0..number_of_fields)
                        .map(|_| quote! {Box::new(self.next().unwrap_or(#name::#first_variant_name))})
                        .collect();
                    arm = quote! {
                        #i => #name::#variant_name(#(#fields),*),
                    };
                    let inner_fields: Vec<_> = (0..number_of_fields)
                        .map(|n| format_ident!("inner{}", n))
                        .collect();
                    let reverse_fields: Vec<_> = (0..number_of_fields)
                        .map(|_| format_ident!("_"))
                        .collect();
                    reverse_arm = quote! {
                        #name::#variant_name(#(#reverse_fields),*) => #i,
                    };
                    inner_arm = quote! {
                        #name::#variant_name(#(#inner_fields),*) => vec![#(#inner_fields),*],
                    };
                }
                Fields::Unit => {
                    arm = quote! {
                        #i => #name::#variant_name,
                    };
                    reverse_arm = quote! {
                        #name::#variant_name => #i,
                    };
                    inner_arm = quote! {
                        #name::#variant_name => vec![],
                    };
                }
                _ => unimplemented!("We do not yet support named Enum fields"),
            };
        
            if arms.len() < u8::MAX as usize {
                arms.push(arm);
                reverse_arms.push(reverse_arm);
                inner_arms.push(inner_arm);
            } else {
                panic!("Enum: {:?} too large to deserialize from bytes!", name);
            }
        }

        let arms_len = arms.len() as u8;

        let expanded = quote! {
            pub struct #iter_name {
                pub inner_data: Arc<Vec<AtomicU8Arc>>,
                index: usize
            }

            impl #name {
                pub fn len(&self) -> usize {
                    let inner_chains = self.get_inner();
                    if inner_chains.is_empty() {
                        1
                    } else {
                        1 + inner_chains
                            .into_iter()
                            .map(|inner| inner.len())
                            .sum::<usize>()
                    }
                }

                pub fn get_inner(&self) -> Vec<&#name> {
                    match self {
                        #(#inner_arms)*
                    }
                }

                pub fn to_bytes(&self) -> Vec<u8> {
                    let mut res = Vec::new();
                    res.push(match self {
                        #(#reverse_arms)*
                    });
                    let inner: Vec<u8> = self.get_inner()
                        .iter()
                        .flat_map(|inner_self|inner_self.to_bytes())
                        .collect();
                    res.extend(inner);
                    res
                }

                pub fn from_bytes(bytes: Vec<u8>) -> Vec<Self> {
                    #iter_name::from_bytes(bytes).collect()
                }

                pub fn iter(&self) -> #iter_name {
                    #iter_name::from_bytes(self.to_bytes())
                }
            }

            impl Ord for #name {
                fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                    self.len().cmp(&other.len())
                }
            }

            impl #iter_name {
                pub fn new(bytes: Arc<Vec<AtomicU8Arc>>) -> Self {
                    Self { inner_data: bytes, index: 0 }
                }

                pub fn from_bytes(raw_bytes: Vec<u8>) -> Self {
                    let atomic_bytes: Vec<AtomicU8Arc> = raw_bytes.iter().map(|&raw_byte|
                        Arc::new(Atomic::new(raw_byte))
                    ).collect();
                    Self {
                        inner_data: Arc::new(
                            atomic_bytes
                        ),
                        index: 0,
                    }
                }

                pub fn to_bytes(&self) -> Vec<u8> {
                    self.inner_data.iter().map(|atomic_byte|{
                        atomic_byte.load(Ordering::Acquire)
                    }).collect()
                }
            }

            impl Iterator for #iter_name {
                type Item = #name;

                fn next(&mut self) -> Option<Self::Item> {
                    if self.index < self.inner_data.len() {
                        let byte = &self.inner_data[self.index];
                        self.index += 1;
                        Some(match byte.load(Ordering::Acquire) % #arms_len {
                            #(#arms)*
                            _ => #name::#first_variant_name,
                        })
                    } else {
                        None
                    }
                }
            }
        };

        TokenStream::from(expanded)
    } else {
        panic!("Can only derive a LazyDeserializer for a recursive Enum")
    }
}
