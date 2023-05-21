use atomic::Atomic;
use futures::StreamExt;
use prokio::pinned::mpsc::{unbounded, UnboundedReceiver};
use prokio::spawn_local;
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::sync::{Arc};

use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use std::collections::HashMap;
use std::sync::atomic::Ordering;

type Point = Vec<i32>;
type AtomicU8Arc = Arc<Atomic<u8>>;

use std::sync::RwLock;
use lazy_static::lazy_static;

lazy_static! {
    static ref MEMOIZED_POINTS: RwLock<HashMap<Point, Vec<Atomic<u8>>>> = RwLock::new(HashMap::new());
}
pub struct SharedSpace {
    inner: HashMap<Point, Arc<Vec<AtomicU8Arc>>>
}

impl SharedSpace {
    pub fn new() -> Self {
        SharedSpace {
            inner: HashMap::new()
        }
    }

    fn init_rand(&self, point: Point, range: std::ops::Range<usize>) -> Vec<u8> {
        let memoized_points = MEMOIZED_POINTS.read().unwrap();
    
        if let Some(vec) = memoized_points.get(&point) {
            if vec.len() > range.end {
                // If the end of the range is within the memoized values, return the requested sub-slice
                let new_vec: Vec<u8> = vec[range.clone()].iter().map(|v| v.load(Ordering::Relaxed)).collect();
                return new_vec;
            }
        }
    
        drop(memoized_points); // Drop the read lock
    
        let mut rng = self.seed_rng(&point);
        let mut memoized_points = MEMOIZED_POINTS.write().unwrap();
        let vec = memoized_points.entry(point.clone()).or_insert_with(|| Vec::new());
    
        for _ in vec.len()..range.end {
            let byte = Atomic::new(rng.gen::<u8>());
            vec.push(byte);
        }
    
        // Return the requested sub-slice of the RNG stream
        let new_vec: Vec<u8> = vec[range.clone()].iter().map(|v| v.load(Ordering::Relaxed)).collect();
        new_vec
    }
    
    

    pub fn duplicate(
        &self,
        source: &Point,
        maybe_range: Option<std::ops::Range<usize>>,
    ) -> Vec<AtomicU8Arc> {
        let source_vec = self.get(source, maybe_range);
        let new_vec = source_vec
            .iter()
            .map(|atom| Arc::new(Atomic::new(atom.load(Ordering::Relaxed))))
            .collect();
        new_vec
    }

    pub fn duplicate_to(
        &mut self,
        source: &Point,
        target: Point,
        maybe_range: Option<std::ops::Range<usize>>,
    ) -> Result<(), &'static str> {
        let new_bytevec = self.duplicate(source, maybe_range);
        self.inner.insert(target, Arc::new(new_bytevec));
        Ok(())
    }

    pub fn link_to(
        &mut self,
        source: &Point,
        target: Point,
        maybe_range: Option<std::ops::Range<usize>>,
    ) -> Result<(), &'static str> {
        let source_bytevec = self.get(source, maybe_range);
        self.inner.insert(target,source_bytevec);
        Ok(())
    }

    pub fn get(&self, point: &Point, maybe_range: Option<std::ops::Range<usize>>) -> Arc<Vec<AtomicU8Arc>> {
        let requested_range = maybe_range.unwrap_or(0..8);
        
        if let Some(vec) = self.inner.get(point) {
            if vec.len() >= requested_range.end {
                // We can return a reference to the existing vector directly
                Arc::clone(vec)
            } else {
                // If the existing vector doesn't cover the requested range, we need to extend it with random values
                let additional_values = self.init_rand(point.clone(), vec.len()..requested_range.end);
                let mut new_vec: Vec<AtomicU8Arc> = Vec::new();
                new_vec.extend(vec.iter().map(|x| Arc::clone(x)));
                new_vec.extend(additional_values.into_iter().map(|non_a|Arc::new(Atomic::new(non_a))));
                Arc::new(new_vec)
            }
        } else {
            // If the point doesn't exist in the map, we generate a random vector to cover the requested range
            let random_values = self.init_rand(point.clone(), requested_range).into_iter().map(|non_a|Arc::new(Atomic::new(non_a))).collect();
            Arc::new(random_values)
        }
    }

    pub fn set(&mut self, point: Point, vec: Vec<AtomicU8Arc>) {
        self.inner.insert(point, Arc::new(vec));
    }

    pub fn mutate<F>(
        &mut self,
        point: &Point,
        maybe_range: Option<std::ops::Range<usize>>,
        func: F,
    ) -> Result<(), &'static str>
    where
        F: FnOnce(&Vec<AtomicU8Arc>),
    {
        let bitvec = self.get(point, maybe_range);
        func(&bitvec);
        Ok(())
    }

    fn seed_rng(&self, point: &Point) -> ChaCha8Rng {
        let seed = point
            .iter()
            .fold(0u64, |acc, &x| acc.rotate_left(1) ^ (x as u64));
        ChaCha8Rng::seed_from_u64(seed)
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd)]
pub enum FunctionChain {
    // Pure functions
    Add(Box<FunctionChain>),
    Multiply(Box<FunctionChain>),
    Divide(Box<FunctionChain>),
    Modulo(Box<FunctionChain>),

    // Functions that read from ring buffers and foreign memory, including references
    ReadFromRingBuffer(Box<FunctionChain>),
    PeripheralRead(Box<FunctionChain>),
    Reference(Box<FunctionChain>),

    // Functions that create new ring buffers and memory locations
    SpawnRingBuffer(Box<FunctionChain>),
    CreateNode(Box<FunctionChain>),
    AddChild(Box<FunctionChain>, Box<FunctionChain>),
    SetPointer(Box<FunctionChain>, Box<FunctionChain>),

    // Functions that delete or modify things
    DeleteRingBuffer(Box<FunctionChain>),
    WriteToRingBuffer(Box<FunctionChain>),
    RotateRingBuffer(Box<FunctionChain>),
    InsertFunction(Box<FunctionChain>, Box<FunctionChain>),
    DeleteFunction(Box<FunctionChain>),
    ReplaceFunction(Box<FunctionChain>, Box<FunctionChain>),
    PeripheralWrite(Box<FunctionChain>),
    SpawnIndex(Box<FunctionChain>),

    End,
}

impl FunctionChain {
    // Add a `len` method to compute the length of the chain
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

    // Helper method to extract the inner function chains, if any
    pub fn get_inner(&self) -> Vec<&FunctionChain> {
        match self {
            FunctionChain::Add(inner) => vec![inner],
            FunctionChain::Multiply(inner) => vec![inner],
            FunctionChain::Divide(inner) => vec![inner],
            FunctionChain::Modulo(inner) => vec![inner],
            FunctionChain::ReadFromRingBuffer(inner) => vec![inner],
            FunctionChain::PeripheralRead(inner) => vec![inner],
            FunctionChain::Reference(inner) => vec![inner],
            FunctionChain::SpawnRingBuffer(inner) => vec![inner],
            FunctionChain::CreateNode(inner) => vec![inner],
            FunctionChain::AddChild(inner0, inner1) => vec![inner0, inner1],
            FunctionChain::SetPointer(inner0, inner1) => vec![inner0, inner1],
            FunctionChain::DeleteRingBuffer(inner) => vec![inner],
            FunctionChain::WriteToRingBuffer(inner) => vec![inner],
            FunctionChain::RotateRingBuffer(inner) => vec![inner],
            FunctionChain::InsertFunction(inner0, inner1) => vec![inner0, inner1],
            FunctionChain::DeleteFunction(inner) => vec![inner],
            FunctionChain::ReplaceFunction(inner0, inner1) => vec![inner0, inner1],
            FunctionChain::PeripheralWrite(inner) => vec![inner],
            FunctionChain::SpawnIndex(inner) => vec![inner],
            FunctionChain::End => vec![],
        }
    }
}

impl Ord for FunctionChain {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        todo!()
    }
}
pub struct FunctionChainIterator<'a> {
    iter: std::slice::Iter<'a, AtomicU8Arc>,
}

impl<'a> FunctionChainIterator<'a> {
    pub fn new(bytes: &'a Arc<Vec<AtomicU8Arc>>) -> Self {
        Self { iter: bytes.iter() }
    }
}

impl<'a> Iterator for FunctionChainIterator<'a> {
    type Item = FunctionChain;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|byte| {
                Some(match byte.load(Ordering::Relaxed) % 19 {
                    // Pure functions
                    0 => FunctionChain::Add(Box::new(Iterator::next(self)?)),
                    1 => FunctionChain::Multiply(Box::new(Iterator::next(self)?)),
                    2 => FunctionChain::Divide(Box::new(Iterator::next(self)?)),
                    3 => FunctionChain::Modulo(Box::new(Iterator::next(self)?)),

                    // Functions that read from ring buffers and foreign memory, including references
                    4 => FunctionChain::ReadFromRingBuffer(Box::new(Iterator::next(self)?)),
                    5 => FunctionChain::PeripheralRead(Box::new(Iterator::next(self)?)),
                    6 => FunctionChain::Reference(Box::new(Iterator::next(self)?)),

                    // Functions that create new ring buffers and memory locations
                    7 => FunctionChain::SpawnRingBuffer(Box::new(Iterator::next(self)?)),
                    8 => FunctionChain::CreateNode(Box::new(Iterator::next(self)?)),
                    9 => FunctionChain::AddChild(
                        Box::new(Iterator::next(self)?),
                        Box::new(Iterator::next(self)?),
                    ),
                    10 => FunctionChain::SetPointer(
                        Box::new(Iterator::next(self)?),
                        Box::new(Iterator::next(self)?),
                    ),

                    // Functions that delete or modify things
                    11 => FunctionChain::DeleteRingBuffer(Box::new(Iterator::next(self)?)),
                    12 => FunctionChain::WriteToRingBuffer(Box::new(Iterator::next(self)?)),
                    13 => FunctionChain::RotateRingBuffer(Box::new(Iterator::next(self)?)),
                    14 => FunctionChain::InsertFunction(
                        Box::new(Iterator::next(self)?),
                        Box::new(Iterator::next(self)?),
                    ),
                    15 => FunctionChain::DeleteFunction(Box::new(Iterator::next(self)?)),
                    16 => FunctionChain::ReplaceFunction(
                        Box::new(Iterator::next(self)?),
                        Box::new(Iterator::next(self)?),
                    ),
                    17 => FunctionChain::PeripheralWrite(Box::new(Iterator::next(self)?)),
                    18 => FunctionChain::SpawnIndex(Box::new(Iterator::next(self)?)),
                    _ => unreachable!(),
                })
            })
            .flatten()
    }
}

type PriorityQueue<T> = BinaryHeap<Reverse<T>>;

pub async fn scheduler<F>(region_view: Arc<LiveRegionView<'_>>, mut process_item: F)
where
    F: FnMut((Point, FunctionChain)) -> () + Send + 'static,
{
    let (tx, mut rx) = unbounded();

    // Spawn a task for each iterator in the LiveRegionView
    for (point, vec) in region_view.iter() {
        let vec_clone = vec.clone();
        while let Some(item) = FunctionChainIterator::new(&vec_clone).next() {
            let point_clone = point.clone();
            let tx_clone = tx.clone();
            spawn_local(async move {
                tx_clone.send_now(Reverse((point_clone.clone(), item)));
            });
        }
    }

    // Process the results
    let mut results: PriorityQueue<(Point, FunctionChain)> = PriorityQueue::new();
    while let Some(result) = rx.next().await {
        results.push(result);

        // Process the highest-priority item
        if let Some(Reverse((point, item))) = results.pop() {
            process_item((point, item));
        }
    }
}


struct RegionPoints {
    dims: Point,
    cur: Point,
}

impl RegionPoints {
    fn new(dims: Point) -> Self {
        Self {
            dims: dims.clone(),
            cur: vec![0; dims.len()],
        }
    }
}

impl Iterator for RegionPoints {
    type Item = Point;

    fn next(&mut self) -> Option<Self::Item> {
        let p = self.cur.clone();

        for i in (0..self.cur.len()).rev() {
            if self.cur[i] < self.dims[i] - 1 {
                self.cur[i] += 1;
                break;
            } else if i == 0 {
                return None; // All points have been generated.
            } else {
                self.cur[i] = 0;
            }
        }

        Some(p)
    }
}

fn generate_points_in_region(dims: Point) -> RegionPoints {
    RegionPoints::new(dims)
}
pub struct LiveRegionView<'a> {
    space: &'a SharedSpace,
    origin: Point,
    dims: Point,
}

impl<'a> LiveRegionView<'a> {
    pub fn new(space: &'a SharedSpace, origin: Point, dims: Point) -> Self {
        Self {
            space,
            origin,
            dims,
        }
    }

    pub fn get(
        &self,
        rel_point: Point,
        maybe_range: Option<std::ops::Range<usize>>,
    ) -> Arc<Vec<AtomicU8Arc>> {
        let point = self
            .origin
            .iter()
            .zip(rel_point.iter())
            .map(|(a, b)| a + b)
            .chain(if self.origin.len() > rel_point.len() {
                self.origin[rel_point.len()..].iter().cloned()
            } else {
                rel_point[self.origin.len()..].iter().cloned()
            })
            .collect();
        self.space.get(&point, maybe_range)
    }

    pub fn iter(&self) -> impl Iterator<Item = (Point, Arc<Vec<AtomicU8Arc>>)> + '_ {
        generate_points_in_region(self.dims.clone()).filter_map(move |rel_point| {
            let point = self
                .origin
                .iter()
                .zip(rel_point.iter())
                .map(|(a, b)| a + b)
                .chain(if self.origin.len() > rel_point.len() {
                    self.origin[rel_point.len()..].iter().cloned()
                } else {
                    rel_point[self.origin.len()..].iter().cloned()
                })
                .collect();
            self.space.inner.get(&point).map(|bitvec| (point, Arc::clone(bitvec)))
        })
    }
}
