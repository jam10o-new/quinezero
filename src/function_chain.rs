
use crate::space::prelude::*;
use crate::space::{LiveRegionView, SharedSpace, LocalSharedSpace, DesparsedRegionView};
use itertools::Itertools;
use lazydeseriter::LazyDeserializer;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::{ToPrimitive, Zero};
use std::cell::Cell;
use std::ops::{Add, Div, Mul, Sub};

pub mod lang {

    use super::*;

    #[derive(Clone)]
    pub enum Phrase {
        Chain(FunctionChain),
        Bytes(Vec<u8>),
        Point(Point),
        Name(Vec<u8>)
    }
    
    const SILLY_NUMBER: i32 = -1;
    const TEMP_NUMBER: i32 = -2;
    const CHAIN_STORE: [i32; 8] = [0, 0, 0, 0, 0, SILLY_NUMBER, 0, 0];
    const BYTE_STORE: [i32; 8] = [0, 0, 0, 0, 0, SILLY_NUMBER, 0, 1];
    const POINT_STORE: [i32; 8] = [0, 0, 0, 0, 0, SILLY_NUMBER, 0, 2];
    // names are converted to points and appended to the NAME_STORE,
    // data contained is a point in one of the stores (constructed by suffixing the name)
    // or a link to another name
    const NAME_STORE: [i32; 8] = [0, 0, 0, 0, 0, SILLY_NUMBER, 0, 3];

    fn name_to_point(name: Vec<u8>) -> Point {
        let mut result: Point = NAME_STORE.clone().to_vec();
        let mut suffix: Point = name.clone().iter().map(|&a| a as i32).collect();
        result.append(&mut suffix);
        result
    }

    //this is black magic and was a complete PITA to figure out :crying:
    macro_rules! fc {
        ($variant:ident $(, $( $child:tt ),* )? ) => {
            FunctionChain::$variant$((
                $(Box::new(generate_function_chain!($child))),*
            ))?
        };
        (($variant:ident $(, $( $child:tt ),* )? )) => {
            FunctionChain::$variant$((
                $(Box::new(generate_function_chain!($child))),*
            ))?
        };
    }

    // A simple functionchain with param 
    // placeholders (End) that writes
    // data to a point
    fn fc_store_data_at_point_placeholder() -> FunctionChain {
        fc! {
            WriteToPoint4, (Pass, End), (Pass, End)
        }
    }
    
    fn merge_function_chains(chains: Vec<FunctionChain>) -> FunctionChain {
        if chains.is_empty() {
            // Handle empty input appropriately; maybe return a FunctionChain::End or similar.
            return FunctionChain::End;
        }
        chains.into_iter().fold(
            FunctionChain::End, // Starting value, could also be chains[0] if guaranteed non-empty
            |acc, chain| FunctionChain::ElseEager(
                Box::new(acc),
                Box::new(chain)
            )
        )
    }

    fn count_placeholders(target: &Vec<u8>) -> usize {
        if target.len() == 1 {
            // explicit end, has no children
            // shouldn't be replaced in compile step
            0
        } else {
            target.iter().filter(|&n| *n == 0u8).count()
        }
    }

    fn replace_placeholders(target: &mut Vec<u8>, replacements: &[Vec<u8>]) {
        let mut i = 0;
        let mut rep_idx = 0;
    
        while i < target.len() && rep_idx < replacements.len() {
            if target[i] == 0u8 {
                let pholder = target.remove(i); // Remove the placeholder
                if let Some(replacement) = replacements.get(rep_idx){
                    for &byte in replacement.iter().rev() {
                        target.insert(i, byte); // Insert each byte in reverse so that the sequence remains as intended
                    }
                    i += replacement.len();
                    rep_idx += 1; 
                } else {
                    target.insert(i, pholder);
                    i += 1;
                    rep_idx += 1;
                }
            } else {
                i += 1;
            }
        }
    }

    fn compile_phrases<S: SharedSpace + Clone>(context: &mut S, params: Vec<Phrase>) -> Vec<Vec<u8>> {
        params.iter().map(|phrase|{
            match phrase {
                Phrase::Chain(data) => {
                    data.to_bytes()
                }
                Phrase::Bytes(data) => {
                    data.clone()
                }
                Phrase::Point(data) => {
                    _dims::point_to_bytes(data.clone())
                }
                Phrase::Name(data) => {
                    let name_point = name_to_point(data.clone());
                    let data_point_abytes = context.get(&name_point, None);
                    let data_point_bytes = data_point_abytes.iter().map(|atomic_byte|{
                        atomic_byte.load(Ordering::Acquire)
                    }).collect();
                    let data_point = _dims::bytes_to_point(data_point_bytes, _dims::BytesPerDim::Four);
                    let data_abytes = context.get(&data_point, None);
                    data_abytes.iter().map(|atomic_byte|{
                        atomic_byte.load(Ordering::Acquire)
                    }).collect()
                }
            }
        }).collect()
    }

    fn gen_store_instruction(name: Vec<u8>, phrase: Phrase) -> FunctionChain {
        let name_point = name_to_point(name);
        let mut stored_data;
        let data_point = match phrase {
            Phrase::Chain(data) => {
                stored_data = data.to_bytes();
                let mut res = CHAIN_STORE.clone().to_vec();
                let mut app = name_point.clone();
                res.append(&mut app);
                res
            }
            Phrase::Bytes(data) => {
                stored_data = data.clone();
                let mut res = BYTE_STORE.clone().to_vec();
                let mut app = name_point.clone();
                res.append(&mut app);
                res
            }
            Phrase::Point(data) => {
                stored_data = super::_dims::point_to_bytes(data);
                let mut res = POINT_STORE.clone().to_vec();
                let mut app = name_point.clone();
                res.append(&mut app);
                res
            }
            Phrase::Name(data) => {
                stored_data = data.clone();
                let res = name_to_point(data);
                res
            }
        };
        let name_point_bytes = super::_dims::point_to_bytes(name_point);
        let data_point_bytes = super::_dims::point_to_bytes(data_point);

        let mut name_chain_bytes = fc_store_data_at_point_placeholder().to_bytes();
        let mut data_chain_bytes = fc_store_data_at_point_placeholder().to_bytes();

        replace_placeholders(&mut name_chain_bytes, &[name_point_bytes, data_point_bytes.clone()]);
        replace_placeholders(&mut data_chain_bytes, &[data_point_bytes, stored_data]);

        let name_chains = FunctionChain::from_bytes(name_chain_bytes);
        let data_chains = FunctionChain::from_bytes(data_chain_bytes);

        let final_chain = merge_function_chains([name_chains, data_chains].into_iter().flatten().collect());

        final_chain
    }
    
    pub struct StatementRunner {
        // core stores temp vars and chains while
        // building and executing a statement runner
        core: LocalSharedSpace,
        tmp: Vec<Phrase>
    }
    
    impl StatementRunner {
        fn start() -> Self {
            StatementRunner {
                core: LocalSharedSpace::new(),
                tmp: Vec::new()
            }
        }
    
        fn do_after(&mut self, p: Phrase) -> &Self {
            self.tmp.push(p);
            self
        }
     
        fn name(&mut self, name: Vec<u8>, phrase: Phrase) -> &Self {
            let instruction_chain = gen_store_instruction(name, phrase);
            exec_function_chain(&mut self.core, Box::new(instruction_chain));
            self
        }
    
        fn sname(&mut self, name_str: String, phrase: Phrase) -> &Self {
            let name = name_str.into_bytes();
            let instruction_chain = gen_store_instruction(name, phrase);
            exec_function_chain(&mut self.core, Box::new(instruction_chain));
            self
        }
    
        fn compile(&mut self) -> &Self {
            // Create an empty list to hold the roots of the function tree
            let mut function_tree_roots: Vec<FunctionChain> = Vec::new();
            
            // Process the phrases to build the function tree
            while !self.tmp.is_empty() {
            // Take the next phrase from the remaining phrases
            let current_phrase = self.tmp.remove(0);
            let mut cur_res;
            
                // Check if it's a Chain phrase
                if let Phrase::Chain(function_chain) = current_phrase {
                    // Count the number of placeholders in the function chain
                    let num_placeholders = count_placeholders(&function_chain.to_bytes());
                    
                    // Consume the next `num_placeholders` phrases from the remaining phrases
                    let consumed_phrases: Vec<Phrase> = self.tmp.drain(..num_placeholders).collect();
                    
                    // Compile the consumed phrases into a new function chain
                    let compiled_phrases = compile_phrases(&mut self.core, consumed_phrases);
                    let mut fc_bytes = function_chain.to_bytes();
                    replace_placeholders(&mut fc_bytes, &compiled_phrases);
                    cur_res = merge_function_chains(FunctionChain::from_bytes(fc_bytes));
                } else {
                    let compiled = compile_phrases(&mut self.core, vec![current_phrase]).iter().flat_map(|bytes|FunctionChain::from_bytes(bytes.clone())).collect();
                    cur_res = merge_function_chains(compiled);
                }
                
                // Add the current phrase's function chain to the list of roots
                function_tree_roots.push(cur_res);
            }
            
            // Merge the roots into a single function tree
            let final_function_tree = merge_function_chains(function_tree_roots);
            
            let compiled_loc = vec![];
            self.core.set(compiled_loc, final_function_tree.to_bytes()
                .iter()
                .map(|&byte| Arc::new(Atomic::new(byte)))
                .collect()
            );
            self
        }
    
        fn run<S: SharedSpace + Clone>(&mut self, space: &mut S) -> Vec<u8> {
            if !self.tmp.is_empty() {
                self.compile();
            }
            let compiled_loc = vec![];
            let bytes = self.core.get(&compiled_loc, None);
            let iter = FunctionChainLazyDeserializer::new(bytes);
            let fc = merge_function_chains(iter.collect());
            exec_function_chain(space, Box::new(fc))
        }
    
        fn execute<S: SharedSpace + Clone>(&mut self, space: &mut S) -> &Self {
            self.run(space);
            self
        }
    
        fn run_with_params<S: SharedSpace + Clone>(&mut self, params: Vec<Phrase>, space: &mut S) -> Vec<u8> {
            if !self.tmp.is_empty() {
                self.compile();
            }
            let compiled_loc = vec![];
            let pre_bytes = self.core.get(&compiled_loc, None);
            let iter = FunctionChainLazyDeserializer::new(pre_bytes);
            let pre_fc = merge_function_chains(iter.collect());
            let mut bytes = pre_fc.to_bytes();
            let compiled_params = compile_phrases(&mut self.core, params);
            replace_placeholders(&mut bytes, &compiled_params);
            let fc = merge_function_chains(FunctionChain::from_bytes(bytes));
            exec_function_chain(space, Box::new(fc))
        }
    
        fn execute_with_params<S: SharedSpace + Clone>(&mut self, params: Vec<Phrase>, space: &mut S) -> &Self {
            self.run_with_params(params, space);
            self
        }
    }    
}

mod _dims {
    use crate::space::prelude::Point;

    #[derive(Clone, Copy)]
    pub enum BytesPerDim {
        One,
        Two,
        Four,
    }

    pub fn bytes_to_point(bytes: Vec<u8>, bpd: BytesPerDim) -> Point {
        match bpd {
            BytesPerDim::One => bytes.iter().map(|&byte| byte as i32).collect(),
            BytesPerDim::Two => bytes
                .chunks(2)
                .map(|chunk| {
                    let mut arr = [0; 2];
                    for (i, byte) in chunk.iter().enumerate() {
                        arr[i] = *byte;
                    }
                    i16::from_le_bytes(arr) as i32
                })
                .collect(),
            BytesPerDim::Four => bytes
                .chunks(4)
                .map(|chunk| {
                    let mut arr = [0; 4];
                    for (i, byte) in chunk.iter().enumerate() {
                        arr[i] = *byte;
                    }
                    i32::from_le_bytes(arr)
                })
                .collect(),
        }
    }

    // we can only assume bpd 4 otherwise this is lossy.
    pub fn point_to_bytes(point: Vec<i32>) -> Vec<u8> {
        point
            .iter()
            .flat_map(|&p| {
                let bytes: [u8; 4] = p.to_le_bytes();
                bytes.iter().copied().collect::<Vec<u8>>()
            })
            .collect()
    }
}

pub mod similarity {}

#[derive(Debug, PartialEq, Eq, PartialOrd, LazyDeserializer, Clone)]
pub enum FunctionChain {
    // Units
    End, // also 0
    One,
    // Pure functions
    Eq(Box<FunctionChain>, Box<FunctionChain>),
    Add(Box<FunctionChain>, Box<FunctionChain>),
    Sub(Box<FunctionChain>, Box<FunctionChain>),
    Mul(Box<FunctionChain>, Box<FunctionChain>),
    Div(Box<FunctionChain>, Box<FunctionChain>),
    Cat(Box<FunctionChain>, Box<FunctionChain>),
    BitAddSat(Box<FunctionChain>, Box<FunctionChain>),
    BitAddOvf(Box<FunctionChain>, Box<FunctionChain>), //lossy
    Len(Box<FunctionChain>),
    Rev(Box<FunctionChain>),
    Modpow(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),

    // Maths as ratios
    AddAsRatios(
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
    ),
    SubAsRatios(
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
    ),
    MulAsRatios(
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
    ),
    DivAsRatios(
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
    ),
    // Maths as floats (lossy)
    AddAsFloats(Box<FunctionChain>, Box<FunctionChain>),
    SubAsFloats(Box<FunctionChain>, Box<FunctionChain>),
    MulAsFloats(Box<FunctionChain>, Box<FunctionChain>),
    DivAsFloats(Box<FunctionChain>, Box<FunctionChain>),

    // Functions that read, including references
    Reference(Box<FunctionChain>),

    // Maths with second parameter from within space, read point as Reference, first dimension
    AddDown(Box<FunctionChain>, Box<FunctionChain>),
    SubDown(Box<FunctionChain>, Box<FunctionChain>),
    MulDown(Box<FunctionChain>, Box<FunctionChain>),
    DivDown(Box<FunctionChain>, Box<FunctionChain>),
    // nth dimension
    AddDownN(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    SubDownN(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    MulDownN(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    DivDownN(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),

    // Same as above, but point dims are two u8s instead of 1 (divides dimensionality, multiplies space (i16 dims))
    Reference2(Box<FunctionChain>),
    AddDown2(Box<FunctionChain>, Box<FunctionChain>),
    SubDown2(Box<FunctionChain>, Box<FunctionChain>),
    MulDown2(Box<FunctionChain>, Box<FunctionChain>),
    DivDown2(Box<FunctionChain>, Box<FunctionChain>),
    AddDownN2(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    SubDownN2(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    MulDownN2(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    DivDownN2(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),

    // 4 instead of 1 (divides dimensionality, multiplies space (i32 dims))
    Reference4(Box<FunctionChain>),
    AddDown4(Box<FunctionChain>, Box<FunctionChain>),
    SubDown4(Box<FunctionChain>, Box<FunctionChain>),
    MulDown4(Box<FunctionChain>, Box<FunctionChain>),
    DivDown4(Box<FunctionChain>, Box<FunctionChain>),
    AddDownN4(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    SubDownN4(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    MulDownN4(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    DivDownN4(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),

    // Control flow and multiplexing
    Else(Box<FunctionChain>, Box<FunctionChain>),
    ElseEager(Box<FunctionChain>, Box<FunctionChain>),
    ElseReference(Box<FunctionChain>, Box<FunctionChain>),
    ElseRunReference(Box<FunctionChain>, Box<FunctionChain>),
    ElseEagerRunReference(Box<FunctionChain>, Box<FunctionChain>),
    IfElse(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    IfElseEager(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    IfElseReference(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    IfElseEagerRunReference(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    Pass(Box<FunctionChain>),
    RunReference(Box<FunctionChain>),
    RunReference2(Box<FunctionChain>),
    RunReference4(Box<FunctionChain>),
    RunAndPass(Box<FunctionChain>),
    RunAndPass2(Box<FunctionChain>),
    RunAndPass4(Box<FunctionChain>),
    RunReferenceAndPass(Box<FunctionChain>),
    RunReferenceAndPass2(Box<FunctionChain>),
    RunReferenceAndPass4(Box<FunctionChain>),
    RunReferenceAndReference(Box<FunctionChain>),
    RunReferenceAndReference2(Box<FunctionChain>),
    RunReferenceAndReference4(Box<FunctionChain>),
    CompareAndSelect(
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
    ),
    CompareAndSelectEager(
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
    ),
    CompareAndSelectReference(
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
    ),
    CompareAndRunReference(
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
    ),
    CompareAndEagerRunReference(
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
    ),
    RunRelative(Box<FunctionChain>, Box<FunctionChain>), //point, dim number
    RunRegion(Box<FunctionChain>, Box<FunctionChain>),   //origin, dims
    SelectFromRegion(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    RunPrefixedRegion(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>), //origin, dims, prefix
    RunReferencePrefixedRegion(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    RunRegionDense(Box<FunctionChain>, Box<FunctionChain>), //origin, dims
    SelectFromRegionDense(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    RunPrefixedRegionDense(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>), //origin, dims, prefix
    RunReferencePrefixedRegionDense(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),

    //Precise manipulations
    DropStartFrom(Box<FunctionChain>, Box<FunctionChain>),
    DropEndFrom(Box<FunctionChain>, Box<FunctionChain>),
    DropStartFromReference(Box<FunctionChain>, Box<FunctionChain>),
    DropEndFromReference(Box<FunctionChain>, Box<FunctionChain>),
    DropStartFromRunReference(Box<FunctionChain>, Box<FunctionChain>),
    DropEndFromRunReference(Box<FunctionChain>, Box<FunctionChain>),
    RangeFrom(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),
    RangeFromReference(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>), //may read random from out of index
    RangeFromRunReference(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),

    // Functions that delete or modify things
    DeletePoint(Box<FunctionChain>),
    ZeroPoint(Box<FunctionChain>),
    WriteToPoint(Box<FunctionChain>, Box<FunctionChain>),

    //raw space operations
    DuplicatePointToPoint(Box<FunctionChain>, Box<FunctionChain>),
    LinkPointToPoint(Box<FunctionChain>, Box<FunctionChain>),

    // 2
    DeletePoint2(Box<FunctionChain>),
    ZeroPoint2(Box<FunctionChain>),
    WriteToPoint2(Box<FunctionChain>, Box<FunctionChain>),
    DuplicatePointToPoint2(Box<FunctionChain>, Box<FunctionChain>),
    LinkPointToPoint2(Box<FunctionChain>, Box<FunctionChain>),

    // 4
    DeletePoint4(Box<FunctionChain>),
    ZeroPoint4(Box<FunctionChain>),
    WriteToPoint4(Box<FunctionChain>, Box<FunctionChain>),
    DuplicatePointToPoint4(Box<FunctionChain>, Box<FunctionChain>),
    LinkPointToPoint4(Box<FunctionChain>, Box<FunctionChain>),

    // DANGER OPS
    DeleteRegion(Box<FunctionChain>, Box<FunctionChain>), //TODO: PARALLELIZE
    ZeroRegion(Box<FunctionChain>, Box<FunctionChain>),   //TODO: PARALLELIZE
    WriteRegion(Box<FunctionChain>, Box<FunctionChain>, Box<FunctionChain>),

    //complex ops

    // logically used within Similarity, but useful elsewhere, so it is it's own operation.
    // generates an adjacency/proximity graph from a region, with edges for nodes in each cardinal
    // direction in the chosen (provided) dimensionality.
    // We store the resulting dense space at a point, and the dims of the resultant space in a 4-reference
    // (input origin, input dims, output point, output range ref point, N)
    // Fold a region to a min target dimensionality - a noop if we are already at a higher dimensionality
    // (input origin, input dims, output point, output range ref point, N)
    FoldToN(
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
    ),
    // Use logic from above (DesparsePlus+FoldToN) to create a space of target dimensionality N from another space.
    // Dimensionality reduction is performed whem regenerating our output space from our graph.
    // (input origin, input dims, output point, output range ref point, N)
    DesparseToN(
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
    ),
    // Similarity Score reads two regions and computes a similarity score in N dimensions,
    // only uses points in full scaled dimensionality (i32 dims)
    // (origin, dims, origin, dims, N) -> score: BigUint
    Similarity(
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
        Box<FunctionChain>,
    ),
    // going back to something simple
    // execute children with a new context
    Isolate(Box<FunctionChain>),
    // execute children in a "foreign" context
    ForeignContext(Box<FunctionChain>, Box<FunctionChain>)
}

pub fn follow_reference<S: SharedSpace + Clone>(
    context: &mut S,
    fc: Box<FunctionChain>,
    bpd: _dims::BytesPerDim,
) -> Vec<u8> {
    let point = _dims::bytes_to_point(exec_function_chain(context, fc), bpd);
    FunctionChainLazyDeserializer::new(context.get(&point, None)).to_bytes()
}

pub fn ref_as_code<S: SharedSpace + Clone>(
    context: &mut S,
    fc: Box<FunctionChain>,
    bpd: _dims::BytesPerDim,
) -> Vec<FunctionChain> {
    let point = _dims::bytes_to_point(exec_function_chain(context, fc), bpd);
    FunctionChainLazyDeserializer::new(context.get(&point, None)).collect()
}

pub fn follow_byte_reference<S: SharedSpace + Clone>(
    context: &S,
    bytes: Vec<u8>,
    bpd: _dims::BytesPerDim,
) -> Vec<u8> {
    let point = _dims::bytes_to_point(bytes, bpd);
    FunctionChainLazyDeserializer::new(context.get(&point, None)).to_bytes()
}

pub fn byte_ref_as_code<S: SharedSpace + Clone>(
    context: &S,
    bytes: Vec<u8>,
    bpd: _dims::BytesPerDim,
) -> Vec<FunctionChain> {
    let point = _dims::bytes_to_point(bytes, bpd);
    FunctionChainLazyDeserializer::new(context.get(&point, None)).collect()
}

pub fn exec_function_chains<S: SharedSpace + Clone>(context: &mut S, fcs: Vec<FunctionChain>) -> Vec<u8> {
    fcs.into_iter()
        .flat_map(|fc| exec_function_chain(context, Box::new(fc)))
        .collect()
}

pub fn exec_function_chain<S: SharedSpace + Clone>(context: &mut S, fc: Box<FunctionChain>) -> Vec<u8> {
    let maybe_dim: Cell<Option<_dims::BytesPerDim>> = Cell::new(None);
    match *fc {
        //set maybe_dim if neccesary using if guard expression side-effects!
        // intentionally unreachable.
        //Two
        FunctionChain::Reference2(_)
        | FunctionChain::AddDown2(_, _)
        | FunctionChain::SubDown2(_, _)
        | FunctionChain::MulDown2(_, _)
        | FunctionChain::DivDown2(_, _)
        | FunctionChain::AddDownN2(_, _, _)
        | FunctionChain::SubDownN2(_, _, _)
        | FunctionChain::MulDownN2(_, _, _)
        | FunctionChain::DivDownN2(_, _, _)
        | FunctionChain::RunReference2(_)
        | FunctionChain::RunReferenceAndPass2(_)
        | FunctionChain::RunAndPass2(_)
        | FunctionChain::RunReferenceAndReference2(_)
        | FunctionChain::DeletePoint2(_)
        | FunctionChain::ZeroPoint2(_)
        | FunctionChain::WriteToPoint2(_, _)
        | FunctionChain::DuplicatePointToPoint2(_, _)
        | FunctionChain::LinkPointToPoint2(_, _)
            if {
                maybe_dim.set(Some(_dims::BytesPerDim::Two));
                false
            } =>
        {
            unreachable!()
        }
        //Four
        FunctionChain::Reference4(_)
        | FunctionChain::AddDown4(_, _)
        | FunctionChain::SubDown4(_, _)
        | FunctionChain::MulDown4(_, _)
        | FunctionChain::DivDown4(_, _)
        | FunctionChain::AddDownN4(_, _, _)
        | FunctionChain::SubDownN4(_, _, _)
        | FunctionChain::MulDownN4(_, _, _)
        | FunctionChain::DivDownN4(_, _, _)
        | FunctionChain::RunReference4(_)
        | FunctionChain::RunReferenceAndPass4(_)
        | FunctionChain::RunAndPass4(_)
        | FunctionChain::RunReferenceAndReference4(_)
        | FunctionChain::DeletePoint4(_)
        | FunctionChain::ZeroPoint4(_)
        | FunctionChain::WriteToPoint4(_, _)
        | FunctionChain::DuplicatePointToPoint4(_, _)
        | FunctionChain::LinkPointToPoint4(_, _)
            if {
                maybe_dim.set(Some(_dims::BytesPerDim::Four));
                false
            } =>
        {
            unreachable!()
        }
        //actual match branches below!
        FunctionChain::End => Vec::new(),
        FunctionChain::One => {
            vec![1]
        }
        FunctionChain::Eq(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = exec_function_chain(context, child1);
            if child_res0 == child_res1 { vec![1] } else { vec![0] }
        }
        FunctionChain::Add(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = exec_function_chain(context, child1);
            let val0 = BigUint::from_bytes_le(&child_res0);
            let val1 = BigUint::from_bytes_le(&child_res1);
            let res = val0 + val1;
            res.to_bytes_le()
        }
        FunctionChain::Sub(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = exec_function_chain(context, child1);
            let val0 = BigUint::from_bytes_le(&child_res0);
            let val1 = BigUint::from_bytes_le(&child_res1);
            let res = val0 - val1;
            res.to_bytes_le()
        }
        FunctionChain::Mul(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = exec_function_chain(context, child1);
            let val0 = BigUint::from_bytes_le(&child_res0);
            let val1 = BigUint::from_bytes_le(&child_res1);
            let res = val0 * val1;
            res.to_bytes_le()
        }
        FunctionChain::Div(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = exec_function_chain(context, child1);
            let val0 = BigUint::from_bytes_le(&child_res0);
            let val1 = BigUint::from_bytes_le(&child_res1);
            let res = val0 / val1;
            res.to_bytes_le()
        }
        FunctionChain::Cat(child0, child1) => {
            let mut child_res0 = exec_function_chain(context, child0);
            let mut child_res1 = exec_function_chain(context, child1);
            child_res0.append(&mut child_res1);
            child_res0
        }
        FunctionChain::BitAddSat(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = exec_function_chain(context, child1);
            child_res0
                .iter()
                .zip_longest(child_res1.iter())
                .map(|ab| {
                    let (&a, &b) = ab.or(&0, &0);
                    a.saturating_add(b)
                })
                .collect()
        }
        FunctionChain::BitAddOvf(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = exec_function_chain(context, child1);
            child_res0
                .iter()
                .zip_longest(child_res1.iter())
                .map(|ab| {
                    let (&a, &b) = ab.or(&0, &0);
                    a.overflowing_add(b).0
                })
                .collect()
        }
        FunctionChain::Len(child) => {
            let child_res = exec_function_chain(context, child);
            child_res.len().to_le_bytes().into_iter().collect()
        }
        FunctionChain::Rev(child) => {
            let child_res = exec_function_chain(context, child);
            child_res.into_iter().rev().collect()
        }
        FunctionChain::Modpow(val_child, exp_child, mod_child) => {
            let val = BigUint::from_bytes_le(&exec_function_chain(context, val_child));
            let exp = BigUint::from_bytes_le(&exec_function_chain(context, exp_child));
            let modulus = BigUint::from_bytes_le(&exec_function_chain(context, mod_child));

            let modulus = if modulus.is_zero() {
                BigUint::from(1u32)
            } else {
                modulus
            };

            val.modpow(&exp, &modulus).to_bytes_le()
        }
        FunctionChain::AddAsRatios(num_child0, den_child0, num_child1, den_child1) => {
            let num0raw = exec_function_chain(context, num_child0);
            let den0raw = exec_function_chain(context, den_child0);
            let num1raw = exec_function_chain(context, num_child1);
            let den1raw = exec_function_chain(context, den_child1);

            let num0 = BigInt::from_signed_bytes_le(&num0raw);
            let den0 = BigInt::from_signed_bytes_le(&den0raw);
            let num1 = BigInt::from_signed_bytes_le(&num1raw);
            let den1 = BigInt::from_signed_bytes_le(&den1raw);

            // Ensure denominators are not zero
            let den0 = if den0.is_zero() {
                BigInt::from(1)
            } else {
                den0
            };
            let den1 = if den1.is_zero() {
                BigInt::from(1)
            } else {
                den1
            };

            let ratio0 = Ratio::new(num0, den0);
            let ratio1 = Ratio::new(num1, den1);

            let res = ratio0.add(ratio1).to_f64().unwrap_or(0f64);

            res.to_le_bytes().into_iter().collect()
        }
        FunctionChain::SubAsRatios(num_child0, den_child0, num_child1, den_child1) => {
            let num0raw = exec_function_chain(context, num_child0);
            let den0raw = exec_function_chain(context, den_child0);
            let num1raw = exec_function_chain(context, num_child1);
            let den1raw = exec_function_chain(context, den_child1);

            let num0 = BigInt::from_signed_bytes_le(&num0raw);
            let den0 = BigInt::from_signed_bytes_le(&den0raw);
            let num1 = BigInt::from_signed_bytes_le(&num1raw);
            let den1 = BigInt::from_signed_bytes_le(&den1raw);

            // Ensure denominators are not zero
            let den0 = if den0.is_zero() {
                BigInt::from(1)
            } else {
                den0
            };
            let den1 = if den1.is_zero() {
                BigInt::from(1)
            } else {
                den1
            };

            let ratio0 = Ratio::new(num0, den0);
            let ratio1 = Ratio::new(num1, den1);

            let res = ratio0.sub(ratio1).to_f64().unwrap_or(0f64);

            res.to_le_bytes().into_iter().collect()
        }
        FunctionChain::MulAsRatios(num_child0, den_child0, num_child1, den_child1) => {
            let num0raw = exec_function_chain(context, num_child0);
            let den0raw = exec_function_chain(context, den_child0);
            let num1raw = exec_function_chain(context, num_child1);
            let den1raw = exec_function_chain(context, den_child1);

            let num0 = BigInt::from_signed_bytes_le(&num0raw);
            let den0 = BigInt::from_signed_bytes_le(&den0raw);
            let num1 = BigInt::from_signed_bytes_le(&num1raw);
            let den1 = BigInt::from_signed_bytes_le(&den1raw);

            // Ensure denominators are not zero
            let den0 = if den0.is_zero() {
                BigInt::from(1)
            } else {
                den0
            };
            let den1 = if den1.is_zero() {
                BigInt::from(1)
            } else {
                den1
            };

            let ratio0 = Ratio::new(num0, den0);
            let ratio1 = Ratio::new(num1, den1);

            let res = ratio0.mul(ratio1).to_f64().unwrap_or(0f64);

            res.to_le_bytes().into_iter().collect()
        }
        FunctionChain::DivAsRatios(num_child0, den_child0, num_child1, den_child1) => {
            let num0raw = exec_function_chain(context, num_child0);
            let den0raw = exec_function_chain(context, den_child0);
            let num1raw = exec_function_chain(context, num_child1);
            let den1raw = exec_function_chain(context, den_child1);

            let num0 = BigInt::from_signed_bytes_le(&num0raw);
            let den0 = BigInt::from_signed_bytes_le(&den0raw);
            let num1 = BigInt::from_signed_bytes_le(&num1raw);
            let den1 = BigInt::from_signed_bytes_le(&den1raw);

            // Ensure denominators are not zero
            let den0 = if den0.is_zero() {
                BigInt::from(1)
            } else {
                den0
            };
            let den1 = if den1.is_zero() {
                BigInt::from(1)
            } else {
                den1
            };

            let ratio0 = Ratio::new(num0, den0);
            let ratio1 = Ratio::new(num1, den1);

            let res = ratio0.div(ratio1).to_f64().unwrap_or(0f64);

            res.to_le_bytes().into_iter().collect()
        }
        FunctionChain::AddAsFloats(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = exec_function_chain(context, child1);
            let val0 = &child_res0
                .chunks(8)
                .map(|chunk| {
                    let mut arr = [0; 8];
                    for (i, byte) in chunk.iter().enumerate() {
                        arr[i] = *byte;
                    }
                    f64::from_le_bytes(arr)
                })
                .next()
                .unwrap_or(0f64);

            let val1 = &child_res1
                .chunks(8)
                .map(|chunk| {
                    let mut arr = [0; 8];
                    for (i, byte) in chunk.iter().enumerate() {
                        arr[i] = *byte;
                    }
                    f64::from_le_bytes(arr)
                })
                .next()
                .unwrap_or(0f64);
            let res = val0 + val1;
            res.to_le_bytes().into_iter().collect()
        }
        FunctionChain::SubAsFloats(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = exec_function_chain(context, child1);

            let val0 = &child_res0
                .chunks(8)
                .map(|chunk| {
                    let mut arr = [0; 8];
                    for (i, byte) in chunk.iter().enumerate() {
                        arr[i] = *byte;
                    }
                    f64::from_le_bytes(arr)
                })
                .next()
                .unwrap_or(0f64);

            let val1 = &child_res1
                .chunks(8)
                .map(|chunk| {
                    let mut arr = [0; 8];
                    for (i, byte) in chunk.iter().enumerate() {
                        arr[i] = *byte;
                    }
                    f64::from_le_bytes(arr)
                })
                .next()
                .unwrap_or(0f64);
            //let val0 = f64::from_le_bytes(&child_res0);
            //let val1 = f64::from_le_bytes(&child_res1);
            let res = val0 - val1;
            res.to_le_bytes().into_iter().collect()
        }
        FunctionChain::MulAsFloats(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = exec_function_chain(context, child1);
            let val0 = &child_res0
                .chunks(8)
                .map(|chunk| {
                    let mut arr = [0; 8];
                    for (i, byte) in chunk.iter().enumerate() {
                        arr[i] = *byte;
                    }
                    f64::from_le_bytes(arr)
                })
                .next()
                .unwrap_or(0f64);

            let val1 = &child_res1
                .chunks(8)
                .map(|chunk| {
                    let mut arr = [0; 8];
                    for (i, byte) in chunk.iter().enumerate() {
                        arr[i] = *byte;
                    }
                    f64::from_le_bytes(arr)
                })
                .next()
                .unwrap_or(0f64);
            let res = val0 * val1;
            res.to_le_bytes().into_iter().collect()
        }
        FunctionChain::DivAsFloats(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = exec_function_chain(context, child1);
            let val0 = &child_res0
                .chunks(8)
                .map(|chunk| {
                    let mut arr = [0; 8];
                    for (i, byte) in chunk.iter().enumerate() {
                        arr[i] = *byte;
                    }
                    f64::from_le_bytes(arr)
                })
                .next()
                .unwrap_or(0f64);

            let val1 = &child_res1
                .chunks(8)
                .map(|chunk| {
                    let mut arr = [0; 8];
                    for (i, byte) in chunk.iter().enumerate() {
                        arr[i] = *byte;
                    }
                    f64::from_le_bytes(arr)
                })
                .next()
                .unwrap_or(1f64);
            let res = val0 / val1;
            res.to_le_bytes().into_iter().collect()
        }
        FunctionChain::Reference(child)
        | FunctionChain::Reference2(child)
        | FunctionChain::Reference4(child) => follow_reference(
            context,
            child,
            maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
        ),
        FunctionChain::AddDown(child0, child1)
        | FunctionChain::AddDown2(child0, child1)
        | FunctionChain::AddDown4(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let mut point = _dims::bytes_to_point(
                follow_reference(
                    context,
                    child1,
                    maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
                ),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let mut last_dim = point.pop().unwrap_or(0i32);
            last_dim += 1;
            point.push(last_dim);
            let child_res1 =
                FunctionChainLazyDeserializer::new(context.get(&point, None)).to_bytes();
            let val0 = BigUint::from_bytes_le(&child_res0);
            let val1 = BigUint::from_bytes_le(&child_res1);
            let res = val0 + val1;
            res.to_bytes_le()
        }
        FunctionChain::SubDown(child0, child1)
        | FunctionChain::SubDown2(child0, child1)
        | FunctionChain::SubDown4(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let mut point = _dims::bytes_to_point(
                follow_reference(
                    context,
                    child1,
                    maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
                ),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let mut last_dim = point.pop().unwrap_or(0i32);
            last_dim += 1;
            point.push(last_dim);
            let child_res1 =
                FunctionChainLazyDeserializer::new(context.get(&point, None)).to_bytes();
            let val0 = BigUint::from_bytes_le(&child_res0);
            let val1 = BigUint::from_bytes_le(&child_res1);
            let res = val0 - val1;
            res.to_bytes_le()
        }
        FunctionChain::MulDown(child0, child1)
        | FunctionChain::MulDown2(child0, child1)
        | FunctionChain::MulDown4(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let mut point = _dims::bytes_to_point(
                follow_reference(
                    context,
                    child1,
                    maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
                ),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let mut last_dim = point.pop().unwrap_or(0i32);
            last_dim += 1;
            point.push(last_dim);
            let child_res1 =
                FunctionChainLazyDeserializer::new(context.get(&point, None)).to_bytes();
            let val0 = BigUint::from_bytes_le(&child_res0);
            let val1 = BigUint::from_bytes_le(&child_res1);
            let res = val0 * val1;
            res.to_bytes_le()
        }
        FunctionChain::DivDown(child0, child1)
        | FunctionChain::DivDown2(child0, child1)
        | FunctionChain::DivDown4(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let mut point = _dims::bytes_to_point(
                follow_reference(
                    context,
                    child1,
                    maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
                ),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let mut last_dim = point.pop().unwrap_or(0i32);
            last_dim += 1;
            point.push(last_dim);
            let child_res1 =
                FunctionChainLazyDeserializer::new(context.get(&point, None)).to_bytes();
            let val0 = BigUint::from_bytes_le(&child_res0);
            let val1 = BigUint::from_bytes_le(&child_res1);
            let res = val0 / val1;
            res.to_bytes_le()
        }
        FunctionChain::AddDownN(child0, child1, child2)
        | FunctionChain::AddDownN2(child0, child1, child2)
        | FunctionChain::AddDownN4(child0, child1, child2) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res2 = exec_function_chain(context, child2);
            let mut point = _dims::bytes_to_point(
                follow_reference(
                    context,
                    child1,
                    maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
                ),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let val2 = BigUint::from_bytes_le(&child_res2);
            let mut idx = val2.to_u32_digits().pop().unwrap_or(0u32) as usize;
            let mut sel_dim = if point.len() <= idx {
                point.remove(idx)
            } else {
                idx = point.len();
                point.pop().unwrap_or(0i32)
            };
            sel_dim += 1;
            point.insert(idx, sel_dim);
            let child_res1 =
                FunctionChainLazyDeserializer::new(context.get(&point, None)).to_bytes();
            let val0 = BigUint::from_bytes_le(&child_res0);
            let val1 = BigUint::from_bytes_le(&child_res1);
            let res = val0 + val1;
            res.to_bytes_le()
        }
        FunctionChain::SubDownN(child0, child1, child2)
        | FunctionChain::SubDownN2(child0, child1, child2)
        | FunctionChain::SubDownN4(child0, child1, child2) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res2 = exec_function_chain(context, child2);
            let mut point = _dims::bytes_to_point(
                follow_reference(
                    context,
                    child1,
                    maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
                ),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let val2 = BigUint::from_bytes_le(&child_res2);
            let mut idx = val2.to_u32_digits().pop().unwrap_or(0u32) as usize;
            let mut sel_dim = if point.len() <= idx {
                point.remove(idx)
            } else {
                idx = point.len();
                point.pop().unwrap_or(0i32)
            };
            sel_dim += 1;
            point.insert(idx, sel_dim);
            let child_res1 =
                FunctionChainLazyDeserializer::new(context.get(&point, None)).to_bytes();
            let val0 = BigUint::from_bytes_le(&child_res0);
            let val1 = BigUint::from_bytes_le(&child_res1);
            let res = val0 - val1;
            res.to_bytes_le()
        }
        FunctionChain::MulDownN(child0, child1, child2)
        | FunctionChain::MulDownN2(child0, child1, child2)
        | FunctionChain::MulDownN4(child0, child1, child2) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res2 = exec_function_chain(context, child2);
            let mut point = _dims::bytes_to_point(
                follow_reference(
                    context,
                    child1,
                    maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
                ),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let val2 = BigUint::from_bytes_le(&child_res2);
            let mut idx = val2.to_u32_digits().pop().unwrap_or(0u32) as usize;
            let mut sel_dim = if point.len() <= idx {
                point.remove(idx)
            } else {
                idx = point.len();
                point.pop().unwrap_or(0i32)
            };
            sel_dim += 1;
            point.insert(idx, sel_dim);
            let child_res1 =
                FunctionChainLazyDeserializer::new(context.get(&point, None)).to_bytes();
            let val0 = BigUint::from_bytes_le(&child_res0);
            let val1 = BigUint::from_bytes_le(&child_res1);
            let res = val0 * val1;
            res.to_bytes_le()
        }
        FunctionChain::DivDownN(child0, child1, child2)
        | FunctionChain::DivDownN2(child0, child1, child2)
        | FunctionChain::DivDownN4(child0, child1, child2) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res2 = exec_function_chain(context, child2);
            let mut point = _dims::bytes_to_point(
                follow_reference(
                    context,
                    child1,
                    maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
                ),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let val2 = BigUint::from_bytes_le(&child_res2);
            let mut idx = val2.to_u32_digits().pop().unwrap_or(0u32) as usize;
            let mut sel_dim = if point.len() <= idx {
                point.remove(idx)
            } else {
                idx = point.len();
                point.pop().unwrap_or(0i32)
            };
            sel_dim += 1;
            point.insert(idx, sel_dim);
            let child_res1 =
                FunctionChainLazyDeserializer::new(context.get(&point, None)).to_bytes();
            let val0 = BigUint::from_bytes_le(&child_res0);
            let val1 = BigUint::from_bytes_le(&child_res1);
            let res = val0 / val1;
            res.to_bytes_le()
        }
        FunctionChain::Else(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let all_zeros = child_res0.clone().iter().all(|&b| b == 0);
            if child_res0 == vec![] || all_zeros {
                exec_function_chain(context, child1)
            } else {
                child_res0
            }
        }
        FunctionChain::ElseEager(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = exec_function_chain(context, child1);
            let all_zeros = child_res0.clone().iter().all(|&b| b == 0);
            if child_res0 == vec![] || all_zeros {
                child_res1
            } else {
                child_res0
            }
        }
        FunctionChain::ElseReference(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = follow_reference(
                context,
                child1,
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let all_zeros = child_res0.clone().iter().all(|&b| b == 0);
            if child_res0 == vec![] || all_zeros {
                child_res1
            } else {
                child_res0
            }
        }
        FunctionChain::ElseRunReference(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = ref_as_code(
                context,
                child1,
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let all_zeros = child_res0.clone().iter().all(|&b| b == 0);
            if child_res0 == vec![] || all_zeros {
                child_res0
            } else {
                exec_function_chains(context, child_res1)
            }
        }
        FunctionChain::ElseEagerRunReference(child0, child1) => {
            let child_res0 = exec_function_chain(context, child0);
            let child_res1 = ref_as_code(
                context,
                child1,
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let eager_res1 = exec_function_chains(context, child_res1);
            let all_zeros = child_res0.clone().iter().all(|&b| b == 0);
            if child_res0 == vec![] || all_zeros {
                child_res0
            } else {
                eager_res1
            }
        }
        FunctionChain::IfElse(child0, child1, child2) => {
            let child_res0 = exec_function_chain(context, child0);
            let all_zeros = child_res0.clone().iter().all(|&b| b == 0);
            if child_res0 == vec![] || all_zeros {
                exec_function_chain(context, child1)
            } else {
                exec_function_chain(context, child2)
            }
        }
        FunctionChain::IfElseEager(child0, child1, child2) => {
            let child_res0 = exec_function_chain(context, child0);
            let nonzero_res = exec_function_chain(context, child1);
            let zero_res = exec_function_chain(context, child2);
            let all_zeros = child_res0.clone().iter().all(|&b| b == 0);
            if child_res0 == vec![] || all_zeros {
                zero_res
            } else {
                nonzero_res
            }
        }
        FunctionChain::IfElseReference(child0, child1, child2) => {
            let child_res0 = exec_function_chain(context, child0);
            let all_zeros = child_res0.clone().iter().all(|&b| b == 0);
            if child_res0 == vec![] || all_zeros {
                let child_res2 = follow_reference(
                    context,
                    child2,
                    maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
                );
                child_res2
            } else {
                let child_res1 = follow_reference(
                    context,
                    child1,
                    maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
                );
                child_res1
            }
        }
        FunctionChain::IfElseEagerRunReference(child0, child1, child2) => {
            let child_res0 = exec_function_chain(context, child0);
            let all_zeros = child_res0.clone().iter().all(|&b| b == 0);
            let child_res1 = ref_as_code(
                context,
                child1,
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let child_res2 = ref_as_code(
                context,
                child2,
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let eager_res2 = exec_function_chains(context, child_res2);
            let eager_res1 = exec_function_chains(context, child_res1);
            if child_res0 == vec![] || all_zeros {
                eager_res2
            } else {
                eager_res1
            }
        }
        FunctionChain::Pass(passed) => passed.to_bytes(),
        FunctionChain::RunReference(child)
        | FunctionChain::RunReference2(child)
        | FunctionChain::RunReference4(child) => {
            let code = ref_as_code(
                context,
                child,
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            exec_function_chains(context, code)
        }
        FunctionChain::RunAndPass(child)
        | FunctionChain::RunAndPass2(child)
        | FunctionChain::RunAndPass4(child) => {
            let res = child.to_bytes();
            let _ = exec_function_chain(context, child);
            res
        }
        FunctionChain::RunReferenceAndPass(child)
        | FunctionChain::RunReferenceAndPass2(child)
        | FunctionChain::RunReferenceAndPass4(child) => {
            let ref_as_chain = ref_as_code(
                context,
                child,
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let res = ref_as_chain.iter().flat_map(|fc| fc.to_bytes()).collect();
            let _ = exec_function_chains(context, ref_as_chain);
            res
        }
        FunctionChain::RunReferenceAndReference(child)
        | FunctionChain::RunReferenceAndReference2(child)
        | FunctionChain::RunReferenceAndReference4(child) => {
            let ref_as_chain = ref_as_code(
                context,
                child,
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let res = exec_function_chains(context, ref_as_chain);
            follow_byte_reference(
                context,
                res,
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            )
        }
        FunctionChain::CompareAndSelect(child1, child2, branch1, branch2) => {
            let res1 = BigUint::from_bytes_le(&exec_function_chain(context, child1));
            let res2 = BigUint::from_bytes_le(&exec_function_chain(context, child2));

            if res1 > res2 {
                exec_function_chain(context, branch1)
            } else {
                exec_function_chain(context, branch2)
            }
        }
        FunctionChain::CompareAndSelectEager(child1, child2, branch1, branch2) => {
            let res1 = BigUint::from_bytes_le(&exec_function_chain(context, child1));
            let res2 = BigUint::from_bytes_le(&exec_function_chain(context, child2));

            let branch1_res = exec_function_chain(context, branch1);
            let branch2_res = exec_function_chain(context, branch2);

            if res1 > res2 {
                branch1_res
            } else {
                branch2_res
            }
        }
        FunctionChain::CompareAndSelectReference(child1, child2, branch1, branch2) => {
            let res1 = BigUint::from_bytes_le(&exec_function_chain(context, child1));
            let res2 = BigUint::from_bytes_le(&exec_function_chain(context, child2));

            if res1 > res2 {
                follow_reference(
                    context,
                    branch1,
                    maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
                )
            } else {
                follow_reference(
                    context,
                    branch2,
                    maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
                )
            }
        }
        FunctionChain::CompareAndRunReference(child1, child2, branch1, branch2) => {
            let res1 = BigUint::from_bytes_le(&exec_function_chain(context, child1));
            let res2 = BigUint::from_bytes_le(&exec_function_chain(context, child2));

            let branch_to_run = if res1 > res2 { branch1 } else { branch2 };
            let ref_as_chain = ref_as_code(
                context,
                branch_to_run,
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            exec_function_chains(context, ref_as_chain)
        }
        FunctionChain::CompareAndEagerRunReference(child1, child2, branch1, branch2) => {
            let res1 = BigUint::from_bytes_le(&exec_function_chain(context, child1));
            let res2 = BigUint::from_bytes_le(&exec_function_chain(context, child2));

            let branch1_chain = ref_as_code(
                context,
                branch1,
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let branch2_chain = ref_as_code(
                context,
                branch2,
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );

            let branch1_res = exec_function_chains(context, branch1_chain);
            let branch2_res = exec_function_chains(context, branch2_chain);

            if res1 > res2 {
                branch1_res
            } else {
                branch2_res
            }
        }
        FunctionChain::RunRelative(point_child, dim_num_child) => {
            let mut point_raw = _dims::bytes_to_point(
                exec_function_chain(context, point_child),
                _dims::BytesPerDim::Four,
            );
            let dim_num = BigUint::from_bytes_le(&exec_function_chain(context, dim_num_child));
            let dims = point_raw.len();
            let select_dim: usize = dim_num
                .mod_floor(&dims.try_into().unwrap())
                .try_into()
                .unwrap();
            point_raw[select_dim] = point_raw[select_dim] + 1;
            FunctionChainLazyDeserializer::new(context.get(&point_raw, None))
                .flat_map(|fc| exec_function_chain(context, Box::new(fc)))
                .collect()
        }
        FunctionChain::RunRegion(origin_child, dims_child) => {
            let origin = _dims::bytes_to_point(
                exec_function_chain(context, origin_child),
                _dims::BytesPerDim::Four,
            );
            let dims = _dims::bytes_to_point(
                exec_function_chain(context, dims_child),
                _dims::BytesPerDim::Four,
            );
            let region = LiveRegionView::new(context, origin, dims);
            let extant_points_iter = region.iter_extant();
            exec_function_chains(
                context,
                extant_points_iter
                    .flat_map(|(_, atomic_vec)| FunctionChainLazyDeserializer::new(atomic_vec))
                    .collect(),
            )
        }
        FunctionChain::SelectFromRegion(origin_child, dims_child, index_child) => {
            let origin = _dims::bytes_to_point(
                exec_function_chain(context, origin_child),
                _dims::BytesPerDim::Four,
            );
            let dims = _dims::bytes_to_point(
                exec_function_chain(context, dims_child),
                _dims::BytesPerDim::Four,
            );
            let view_space = context.clone();
            let region = LiveRegionView::new(&view_space, origin, dims);
            let index = BigUint::from_bytes_le(&exec_function_chain(context, index_child));
            type RegionPoint = (Point, Arc<Vec<AtomicU8Arc>>);
            let points: Vec<RegionPoint> = region.iter_extant().collect();
            let wrapped_index: usize = index
                .mod_floor(&(points.len().try_into().unwrap()))
                .try_into()
                .unwrap();
            let selected_point: &RegionPoint = points.get(wrapped_index).unwrap();

            FunctionChainLazyDeserializer::new(Arc::clone(&selected_point.1))
                .flat_map(|fc| exec_function_chain(context, Box::new(fc)))
                .collect()
        }
        FunctionChain::RunPrefixedRegion(origin_child, dims_child, prefix_child) => {
            let prefix = exec_function_chain(context, prefix_child); // Clone the prefix function chain.
            let origin = _dims::bytes_to_point(
                exec_function_chain(context, origin_child),
                _dims::BytesPerDim::Four,
            );
            let dims = _dims::bytes_to_point(
                exec_function_chain(context, dims_child),
                _dims::BytesPerDim::Four,
            );
            let view_space = context.clone();
            let region = LiveRegionView::new(&view_space, origin, dims);
            let extant_points_iter = region.iter_extant();
            extant_points_iter
                .flat_map(|(_, atomic_vec)| FunctionChainLazyDeserializer::new(atomic_vec))
                .flat_map(|fc| {
                    let mut resvec = prefix.clone();
                    resvec.append(&mut fc.to_bytes());
                    exec_function_chains(context, FunctionChain::from_bytes(resvec))
                })
                .collect()
        }
        FunctionChain::RunReferencePrefixedRegion(origin_child, dims_child, prefix_child) => {
            let prefix = *prefix_child; // Clone the prefix function chain.
            let origin = _dims::bytes_to_point(
                exec_function_chain(context, origin_child),
                _dims::BytesPerDim::Four,
            );
            let dims = _dims::bytes_to_point(
                exec_function_chain(context, dims_child),
                _dims::BytesPerDim::Four,
            );

            let view_space = context.clone();
            let region = LiveRegionView::new(&view_space, origin, dims);
            let extant_points_iter = region.iter_extant();
            extant_points_iter
                .flat_map(|(_, atomic_vec)| FunctionChainLazyDeserializer::new(atomic_vec))
                .flat_map(|fc| {
                    let mut resvec = prefix.to_bytes();
                    resvec.append(&mut fc.to_bytes());
                    exec_function_chains(context, FunctionChain::from_bytes(resvec))
                })
                .collect()
        }
        FunctionChain::RunRegionDense(origin_child, dims_child) => {
            let origin = _dims::bytes_to_point(
                exec_function_chain(context, origin_child),
                _dims::BytesPerDim::Four,
            );
            let dims = _dims::bytes_to_point(
                exec_function_chain(context, dims_child),
                _dims::BytesPerDim::Four,
            );
            let region = LiveRegionView::new(context, origin, dims);
            let extant_points_iter = region.iter_full();
            exec_function_chains(
                context,
                extant_points_iter
                    .flat_map(|(_, atomic_vec)| FunctionChainLazyDeserializer::new(atomic_vec))
                    .collect(),
            )
        }
        FunctionChain::SelectFromRegionDense(origin_child, dims_child, index_child) => {
            let origin = _dims::bytes_to_point(
                exec_function_chain(context, origin_child),
                _dims::BytesPerDim::Four,
            );
            let dims = _dims::bytes_to_point(
                exec_function_chain(context, dims_child),
                _dims::BytesPerDim::Four,
            );

            let view_space = context.clone();
            let region = LiveRegionView::new(&view_space, origin, dims);
            let index = BigUint::from_bytes_le(&exec_function_chain(context, index_child));
            type RegionPoint = (Point, Arc<Vec<AtomicU8Arc>>);
            let points: Vec<RegionPoint> = region.iter_full().collect();
            let wrapped_index: usize = index
                .mod_floor(&(points.len().try_into().unwrap()))
                .try_into()
                .unwrap();
            let selected_point: &RegionPoint = points.get(wrapped_index).unwrap();

            FunctionChainLazyDeserializer::new(Arc::clone(&selected_point.1))
                .flat_map(|fc| exec_function_chain(context, Box::new(fc)))
                .collect()
        }
        FunctionChain::RunPrefixedRegionDense(origin_child, dims_child, prefix_child) => {
            let prefix = exec_function_chain(context, prefix_child); // Clone the prefix function chain.
            let origin = _dims::bytes_to_point(
                exec_function_chain(context, origin_child),
                _dims::BytesPerDim::Four,
            );
            let dims = _dims::bytes_to_point(
                exec_function_chain(context, dims_child),
                _dims::BytesPerDim::Four,
            );

            let view_space = context.clone();
            let region = LiveRegionView::new(&view_space, origin, dims);
            let extant_points_iter = region.iter_full();
            extant_points_iter
                .flat_map(|(_, atomic_vec)| FunctionChainLazyDeserializer::new(atomic_vec))
                .flat_map(|fc| {
                    let mut resvec = prefix.clone();
                    resvec.append(&mut fc.to_bytes());
                    exec_function_chains(context, FunctionChain::from_bytes(resvec))
                })
                .collect()
        }
        FunctionChain::RunReferencePrefixedRegionDense(origin_child, dims_child, prefix_child) => {
            let prefix = *prefix_child; // Clone the prefix function chain.
            let origin = _dims::bytes_to_point(
                exec_function_chain(context, origin_child),
                _dims::BytesPerDim::Four,
            );
            let dims = _dims::bytes_to_point(
                exec_function_chain(context, dims_child),
                _dims::BytesPerDim::Four,
            );

            let view_space = context.clone();
            let region = LiveRegionView::new(&view_space, origin, dims);
            let extant_points_iter = region.iter_full();
            extant_points_iter
                .flat_map(|(_, atomic_vec)| FunctionChainLazyDeserializer::new(atomic_vec))
                .flat_map(|fc| {
                    let mut resvec = prefix.to_bytes();
                    resvec.append(&mut fc.to_bytes());
                    exec_function_chains(context, FunctionChain::from_bytes(resvec))
                })
                .collect()
        }
        FunctionChain::DropStartFrom(child_point, child_index) => {
            let point = _dims::bytes_to_point(
                exec_function_chain(context, child_point),
                _dims::BytesPerDim::Four,
            );
            let index = BigUint::from_bytes_le(&exec_function_chain(context, child_index));

            context.mutate(&point, None, Box::new(|extant| {
                let skip_amt = (extant.len() - index % extant.len()).to_usize().unwrap();
                let new = extant.iter().skip(skip_amt).cloned().collect();
                *extant = Arc::new(new);
            }));
            Vec::new()
        }
        FunctionChain::DropEndFrom(child_point, child_index) => {
            let point = _dims::bytes_to_point(
                exec_function_chain(context, child_point),
                _dims::BytesPerDim::Four,
            );
            let index = BigUint::from_bytes_le(&exec_function_chain(context, child_index));

            context.mutate(&point, None, Box::new(|extant| {
                let take_amt: usize = (extant.len() - index % extant.len()).to_usize().unwrap();
                let new = extant.iter().take(take_amt).cloned().collect();
                *extant = Arc::new(new);
            }));
            Vec::new()
        }
        FunctionChain::DropStartFromReference(child_point, child_index) => {
            let point = _dims::bytes_to_point(
                follow_reference(context, child_point, _dims::BytesPerDim::Four),
                _dims::BytesPerDim::Four,
            );
            let index = BigUint::from_bytes_le(&exec_function_chain(context, child_index));

            context.mutate(&point, None, Box::new(|extant| {
                let skip_amt = (extant.len() - index % extant.len()).to_usize().unwrap();
                let new = extant.iter().skip(skip_amt).cloned().collect();
                *extant = Arc::new(new);
            }));
            Vec::new()
        }
        FunctionChain::DropEndFromReference(child_point, child_index) => {
            let point = _dims::bytes_to_point(
                follow_reference(context, child_point, _dims::BytesPerDim::Four),
                _dims::BytesPerDim::Four,
            );
            let index = BigUint::from_bytes_le(&exec_function_chain(context, child_index))
                .to_usize()
                .unwrap();

            context.mutate(&point, None, Box::new(move |extant| {
                let take_amt: usize = (extant.len() - index % extant.len()).to_usize().unwrap();
                let new = extant.iter().take(take_amt).cloned().collect();
                *extant = Arc::new(new);
            }));
            Vec::new()
        }
        FunctionChain::DropStartFromRunReference(child_point, child_index) => {
            let ref_as_chain = ref_as_code(context, child_point, _dims::BytesPerDim::Four);
            let point = _dims::bytes_to_point(
                exec_function_chains(context, ref_as_chain),
                _dims::BytesPerDim::Four,
            );
            let index = BigUint::from_bytes_le(&exec_function_chain(context, child_index));

            context.mutate(&point, None, Box::new(|extant| {
                let skip_amt = (extant.len() - index % extant.len()).to_usize().unwrap();
                let new = extant.iter().skip(skip_amt).cloned().collect();
                *extant = Arc::new(new);
            }));
            Vec::new()
        }
        FunctionChain::DropEndFromRunReference(child_point, child_index) => {
            let ref_as_chain = ref_as_code(context, child_point, _dims::BytesPerDim::Four);
            let point = _dims::bytes_to_point(
                exec_function_chains(context, ref_as_chain),
                _dims::BytesPerDim::Four,
            );
            let index = BigUint::from_bytes_le(&exec_function_chain(context, child_index));

            context.mutate(&point, None, Box::new(|extant| {
                let take_amt: usize = (extant.len() - index % extant.len()).to_usize().unwrap();
                let new = extant.iter().take(take_amt).cloned().collect();
                *extant = Arc::new(new);
            }));
            Vec::new()
        }
        FunctionChain::RangeFrom(child_point, child_start, child_end) => {
            let point = _dims::bytes_to_point(
                exec_function_chain(context, child_point),
                _dims::BytesPerDim::Four,
            );
            let start = BigUint::from_bytes_le(&exec_function_chain(context, child_start));
            let end = BigUint::from_bytes_le(&exec_function_chain(context, child_end));

            let start: usize = (start % usize::MAX).to_usize().unwrap();
            let end: usize = (end % usize::MAX).to_usize().unwrap();

            context.mutate(&point, Some(start..end), Box::new(|extant| {
                let new = extant.iter().cloned().collect();
                *extant = Arc::new(new);
            }));
            Vec::new()
        }
        FunctionChain::RangeFromReference(child_point, child_start, child_end) => {
            let point = _dims::bytes_to_point(
                follow_reference(context, child_point, _dims::BytesPerDim::Four),
                _dims::BytesPerDim::Four,
            );
            let start = BigUint::from_bytes_le(&exec_function_chain(context, child_start));
            let end = BigUint::from_bytes_le(&exec_function_chain(context, child_end));

            let start: usize = (start % usize::MAX).to_usize().unwrap();
            let end: usize = (end % usize::MAX).to_usize().unwrap();

            context.mutate(&point, Some(start..end), Box::new(|extant| {
                let new = extant.iter().cloned().collect();
                *extant = Arc::new(new);
            }));
            Vec::new()
        }
        FunctionChain::RangeFromRunReference(child_point, child_start, child_end) => {
            let ref_as_chain = ref_as_code(context, child_point, _dims::BytesPerDim::Four);
            let point = _dims::bytes_to_point(
                exec_function_chains(context, ref_as_chain),
                _dims::BytesPerDim::Four,
            );
            let start = BigUint::from_bytes_le(&exec_function_chain(context, child_start));
            let end = BigUint::from_bytes_le(&exec_function_chain(context, child_end));

            let start: usize = (start % usize::MAX).to_usize().unwrap();
            let end: usize = (end % usize::MAX).to_usize().unwrap();

            context.mutate(&point, Some(start..end), Box::new(|extant| {
                let new = extant.iter().cloned().collect();
                *extant = Arc::new(new);
            }));
            Vec::new()
        }
        FunctionChain::DeletePoint(point_child)
        | FunctionChain::DeletePoint2(point_child)
        | FunctionChain::DeletePoint4(point_child) => {
            let point = _dims::bytes_to_point(
                exec_function_chain(context, point_child),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            context.set(point, Vec::new());
            Vec::new()
        }
        FunctionChain::ZeroPoint(point_child)
        | FunctionChain::ZeroPoint2(point_child)
        | FunctionChain::ZeroPoint4(point_child) => {
            let point = _dims::bytes_to_point(
                exec_function_chain(context, point_child),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            context.mutate(&point, None, Box::new(move |extant| {
                for element in extant.iter() {
                    element.store(0, Ordering::Release);
                }
            }));
            Vec::new()
        }
        FunctionChain::WriteToPoint(point_child, write_child)
        | FunctionChain::WriteToPoint2(point_child, write_child)
        | FunctionChain::WriteToPoint4(point_child, write_child) => {
            let point = _dims::bytes_to_point(
                exec_function_chain(context, point_child),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let write = exec_function_chain(context, write_child);
            let res = write.clone();
            context.mutate(&point, None, Box::new(move |extant| {
                let mut idx: usize = 0;
                let mut new = Vec::new();
                for &to_write in write.iter() {
                    if let Some(element) = extant.get(idx) {
                        element.store(to_write, Ordering::Release);
                        new.push(element.clone());
                    } else {
                        new.push(Arc::new(Atomic::new(to_write)));
                    }
                    idx += 1;
                }
                *extant = Arc::new(new);
            }));
            res
        }
        FunctionChain::DuplicatePointToPoint(point_child, target_child)
        | FunctionChain::DuplicatePointToPoint2(point_child, target_child)
        | FunctionChain::DuplicatePointToPoint4(point_child, target_child) => {
            let point = _dims::bytes_to_point(
                exec_function_chain(context, point_child),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let target = _dims::bytes_to_point(
                exec_function_chain(context, target_child),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            context.duplicate_to(&point, target, None);
            Vec::new()
        }
        FunctionChain::LinkPointToPoint(point_child, target_child)
        | FunctionChain::LinkPointToPoint2(point_child, target_child)
        | FunctionChain::LinkPointToPoint4(point_child, target_child) => {
            let point = _dims::bytes_to_point(
                exec_function_chain(context, point_child),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            let target = _dims::bytes_to_point(
                exec_function_chain(context, target_child),
                maybe_dim.get().unwrap_or(_dims::BytesPerDim::One),
            );
            context.link_to(&point, target, None);
            Vec::new()
        }
        FunctionChain::DeleteRegion(origin_child, dims_child) => {
            let origin = _dims::bytes_to_point(
                exec_function_chain(context, origin_child),
                _dims::BytesPerDim::Four,
            );
            let dims = _dims::bytes_to_point(
                exec_function_chain(context, dims_child),
                _dims::BytesPerDim::Four,
            );
            let view_space = context.clone();
            let region = LiveRegionView::new(&view_space, origin, dims);
            let extant_points_iter = region.iter_extant();
            for (point, _) in extant_points_iter {
                context.set(point, Vec::new());
            }
            Vec::new()
        }
        FunctionChain::ZeroRegion(origin_child, dims_child) => {
            let origin = _dims::bytes_to_point(
                exec_function_chain(context, origin_child),
                _dims::BytesPerDim::Four,
            );
            let dims = _dims::bytes_to_point(
                exec_function_chain(context, dims_child),
                _dims::BytesPerDim::Four,
            );
            let view_space = context.clone();
            let region = LiveRegionView::new(&view_space, origin, dims);
            let extant_points_iter = region.iter_extant();
            for (point, _) in extant_points_iter {
                context.mutate(&point, None, Box::new(|extant| {
                    for element in extant.iter() {
                        element.store(0, Ordering::Release);
                    }
                }));
            }
            Vec::new()
        }
        FunctionChain::WriteRegion(origin_child, dims_child, write_child) => {
            let origin = _dims::bytes_to_point(
                exec_function_chain(context, origin_child),
                _dims::BytesPerDim::Four,
            );
            let dims = _dims::bytes_to_point(
                exec_function_chain(context, dims_child),
                _dims::BytesPerDim::Four,
            );
            let write = exec_function_chain(context, write_child);
            let res = write.clone();
            let view_space = context.clone();
            let region = LiveRegionView::new(&view_space, origin, dims);
            let extant_points_iter = region.iter_extant();
            for (point, _) in extant_points_iter {

                let copy_write = write.clone();
                context.mutate(&point, None, Box::new(move |extant| {
                    let mut idx: usize = 0;
                    let mut new = Vec::new();
                    for &to_write in copy_write.iter() {
                        if let Some(element) = extant.get(idx) {
                            element.store(to_write, Ordering::Release);
                            new.push(element.clone());
                        } else {
                            new.push(Arc::new(Atomic::new(to_write)));
                        }
                        idx += 1;
                    }
                    *extant = Arc::new(new);
                }));
            }
            res
        }
        FunctionChain::DesparseToN(
            origin_child,
            dims_child,
            output_point_child,
            output_range_ref_point_child,
            n_child,
        ) => {
            let origin = _dims::bytes_to_point(
                exec_function_chain(context, origin_child),
                _dims::BytesPerDim::Four,
            );
            let dims = _dims::bytes_to_point(
                exec_function_chain(context, dims_child),
                _dims::BytesPerDim::Four,
            );
            let output_point = _dims::bytes_to_point(
                exec_function_chain(context, output_point_child),
                _dims::BytesPerDim::Four,
            );
            let output_range_ref_point = _dims::bytes_to_point(
                exec_function_chain(context, output_range_ref_point_child),
                _dims::BytesPerDim::Four,
            );
            let n = BigUint::from_bytes_le(&exec_function_chain(context, n_child));
            let n_usize = (n % dims.len()).to_usize().unwrap();
            let mut max_dims = output_point.clone();

            let view_space = context.clone();
            let region = LiveRegionView::new(&view_space, origin.clone(), dims);
            let desparse = DesparsedRegionView::new(region, n_usize);
            for (point, data) in desparse.map(|(point_offset, data)|{
                let mut base = output_point.clone();
                for (idx, offset_dim) in point_offset.iter().enumerate() {
                    base[idx] += offset_dim;
                    max_dims[idx] = max_dims[idx].max(base[idx]);
                }
                (base, data)
            }){
                context.set(point, data.to_vec());
            }
            context.set(
                output_range_ref_point,
                _dims::point_to_bytes(max_dims)
                    .iter()
                    .map(|&byte| Arc::new(Atomic::new(byte)))
                    .collect(),
            );
            Vec::new()
        }
        FunctionChain::FoldToN(
            origin_child,
            dims_child,
            output_point_child,
            output_range_ref_point_child,
            n_child,
        ) => {
            let origin = _dims::bytes_to_point(
                exec_function_chain(context, origin_child),
                _dims::BytesPerDim::Four,
            );
            let dims = _dims::bytes_to_point(
                exec_function_chain(context, dims_child),
                _dims::BytesPerDim::Four,
            );
            let output_point = _dims::bytes_to_point(
                exec_function_chain(context, output_point_child),
                _dims::BytesPerDim::Four,
            );
            let output_range_ref_point = _dims::bytes_to_point(
                exec_function_chain(context, output_range_ref_point_child),
                _dims::BytesPerDim::Four,
            );
            let target_dim = BigUint::from_bytes_le(&exec_function_chain(context, n_child));

            let view_space = context.clone();
            let region = LiveRegionView::new(&view_space, origin.clone(), dims);
            let extant_points_iter = region.iter_extant();

            let folding_distance = i32::MAX / 4;
            let folding_dimensions: usize = (target_dim.sub(origin.len()) % origin.len()).to_usize().unwrap();

            // Initialize max_dims with the dimensions of the output_point
            let mut max_dims = output_point.clone();

            for (point, _) in extant_points_iter {
                let mut target = output_point.clone();
                for i in 0..point.len() {
                    target[i] += point[i] - origin[i];
                }
                // If dimensionality of point is less than target_dim
                // add dimensions based on distance of point from origin
                for i in 0..folding_dimensions {
                    let fold = if (point[i] - origin[i]).abs() > folding_distance {
                        1
                    } else {
                        0
                    };
                    let new_dimension = (point[i] - origin[i]) / 2 + fold * folding_distance;
                    target.push(new_dimension);
                }

                // Update max_dims for each dimension in target
                for i in 0..target.len() {
                    max_dims[i] = max_dims[i].max(target[i]);
                }

                context.link_to(&point, target, None);
            }
            // Store the max_dims at the output_range_ref_point
            context.set(
                output_range_ref_point,
                _dims::point_to_bytes(max_dims)
                    .iter()
                    .map(|&byte| Arc::new(Atomic::new(byte)))
                    .collect(),
            );
            Vec::new()
        }
        FunctionChain::Similarity(origin_c, dims_c, origin_c2, dims_c2, dim_n_c) => {
            let origin = _dims::bytes_to_point(
                exec_function_chain(context, origin_c),
                _dims::BytesPerDim::Four,
            );
            let dims = _dims::bytes_to_point(
                exec_function_chain(context, dims_c),
                _dims::BytesPerDim::Four,
            );
            let origin2 = _dims::bytes_to_point(
                exec_function_chain(context, origin_c2),
                _dims::BytesPerDim::Four,
            );
            let dims2 = _dims::bytes_to_point(
                exec_function_chain(context, dims_c2),
                _dims::BytesPerDim::Four,
            );
            let target_dim = BigUint::from_bytes_le(&exec_function_chain(context, dim_n_c));
            /*let score = BigUint::new();
            let dest;
            let dest_2;
            let pre_dims;
            let pre_dims_2;
            let final_dest;
            let final_dest_2;
            let final_dims;
            let final_dims_2;
            // mutate space to target dimensionality
            //   - if dims.len > N
            //    - desparseToN
            //   - foldToN
            // label and link contiguous regions between spaces
            //   - create iterator joining all points from both spaces
            //    - create region number for point
            //    - create map using fill algo to find all contiguous points
            //    - iterate through region points,
            //     - query region number of other space at that point
            //     - (assign+fill if unavailable)
            //    - map most common common region as corresponding
            //    - increase score based on
            //     - corresponding region overlap
            //     - non-corresponding region overlap
            //     - region non-overlap
            //   - continue at next unregioned point.
            // return total score
            */
            unimplemented!()
        }
        FunctionChain::Isolate(child) => {
            let mut new_context = LocalSharedSpace::new();
            exec_function_chain(&mut new_context, child)
        }
        _ => {
            unimplemented!()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn function_chain_execs() {
        let mut world = LocalSharedSpace::new();
        let res0 = exec_function_chain(&mut world, Box::new(FunctionChain::One));
        assert_eq!(res0, vec![1]);
        let res1 = exec_function_chain(
            &mut world,
            Box::new(FunctionChain::Add(
                Box::new(FunctionChain::One),
                Box::new(FunctionChain::One),
            )),
        );
        assert_eq!(res1, vec![2]);
    }

    #[test]
    fn function_chain_to_from_bytes() {
        let inp: Vec<u8> = vec![
            2, 99, 2, 2, 5, 1, 0, 7, 1, 2, 1, 1, 1, 1, 23, 32, 142, 254, 0,
        ];
        let chain = FunctionChain::from_bytes(inp.clone());
        // out does not neccesarily match in - we should not expect it to, because
        // we may have multiple bytes that represent the same enum variants
        // but chain2 should always match chain.
        let out: Vec<u8> = chain.iter().flat_map(|fc| fc.to_bytes()).collect();
        let chain2 = FunctionChain::from_bytes(out.clone());
        assert_eq!(chain, chain2);
    }
}
