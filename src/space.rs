use atomic::Atomic;
use std::sync::{Arc, Mutex};

use lazy_static::lazy_static;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use std::collections::{HashMap, HashSet};
use std::sync::atomic::Ordering;
use std::sync::RwLock;

pub mod prelude {
    pub use atomic::Atomic;
    pub use std::sync::atomic::Ordering;
    pub use std::sync::Arc;

    pub type Point = Vec<i32>;
    pub type AtomicU8Arc = Arc<Atomic<u8>>;
}

use prelude::*;

lazy_static! {
    static ref MEMOIZED_POINTS: RwLock<HashMap<Point, Vec<Atomic<u8>>>> =
        RwLock::new(HashMap::new());
}


pub trait SharedSpace: Clone {
    type HigherLevel: SharedSpace;
    fn new() -> Self;
    fn link_foreign(&mut self, foreign: Option<Arc<dyn ForeignInterface<Self::HigherLevel>>>);
    fn duplicate(
        &self,
        source: &Point,
        maybe_range: Option<std::ops::Range<usize>>,
    ) -> Vec<AtomicU8Arc>{
        vec![Arc::new(Atomic::new(0))]
    }
    fn duplicate_to(
        &mut self,
        source: &Point,
        target: Point,
        maybe_range: Option<std::ops::Range<usize>>,
    ){}
    fn link_to(
        &mut self,
        source: &Point,
        target: Point,
        maybe_range: Option<std::ops::Range<usize>>,
    ){}
    fn get(
        &self,
        point: &Point,
        maybe_range: Option<std::ops::Range<usize>>,
    ) -> Arc<Vec<AtomicU8Arc>>{
        Arc::new(Vec::new())
    }
    fn inner_get(&self, point: &Point) -> Option<&Arc<Vec<AtomicU8Arc>>>;
    fn set(&mut self, point: Point, vec: Vec<AtomicU8Arc>){}
    fn mutate<F>(&mut self, point: &Point, maybe_range: Option<std::ops::Range<usize>>, func: F)
    where F: FnOnce(&mut Arc<Vec<AtomicU8Arc>>){}
}

pub trait ForeignInterface<SharedSpace> {
    fn registered_spaces(&self) -> Vec<Point>;
    fn get_addressed_space(&self, address: Point) -> Option<Arc<Mutex<SharedSpace>>>;
}

impl<S: SharedSpace> ForeignInterface<S> for () {
    fn registered_spaces(&self) -> Vec<Point> {
        Vec::new()
    }
    fn get_addressed_space(&self, _address: Point) -> Option<Arc<Mutex<S>>>{
        None
    }
}

#[derive(Clone)]
pub struct LocalSharedSpace {
    inner: HashMap<Point, Arc<Vec<AtomicU8Arc>>>,
    foreign: Option<Arc<dyn ForeignInterface<DiskSharedSpace>>>,
}

impl SharedSpace for LocalSharedSpace {
    type HigherLevel = DiskSharedSpace;
    fn new() -> Self {
        LocalSharedSpace {
            inner: HashMap::new(),
            foreign: None
        }
    }

    fn link_foreign(&mut self, foreign: Option<Arc<dyn ForeignInterface<DiskSharedSpace>>>){
        self.foreign = foreign;
    }

    fn duplicate(
        &self,
        source: &Point,
        maybe_range: Option<std::ops::Range<usize>>,
    ) -> Vec<AtomicU8Arc> {
        let source_vec = self.get(source, maybe_range);
        let new_vec = source_vec
            .iter()
            .map(|atom| Arc::new(Atomic::new(atom.load(Ordering::Acquire))))
            .collect();
        new_vec
    }

    fn duplicate_to(
        &mut self,
        source: &Point,
        target: Point,
        maybe_range: Option<std::ops::Range<usize>>,
    ) {
        let new_bytevec = self.duplicate(source, maybe_range);
        self.inner.insert(target, Arc::new(new_bytevec));
    }

    fn link_to(
        &mut self,
        source: &Point,
        target: Point,
        maybe_range: Option<std::ops::Range<usize>>,
    ) {
        let source_bytevec = self.get(source, maybe_range);
        self.inner.insert(target, source_bytevec);
    }

    fn get(
        &self,
        point: &Point,
        maybe_range: Option<std::ops::Range<usize>>,
    ) -> Arc<Vec<AtomicU8Arc>> {
        let requested_range = maybe_range.unwrap_or(0..8);

        if let Some(vec) = self.inner.get(point) {
            if vec.len() >= requested_range.end {
                // We can return a reference to the existing vector directly
                Arc::clone(vec)
            } else {
                // If the existing vector doesn't cover the requested range, we need to extend it with random values
                let additional_values =
                    self.init_rand(point.clone(), vec.len()..requested_range.end);
                let mut new_vec: Vec<AtomicU8Arc> = Vec::new();
                new_vec.extend(vec.iter().map(|x| Arc::clone(x)));
                new_vec.extend(
                    additional_values
                        .into_iter()
                        .map(|non_a| Arc::new(Atomic::new(non_a))),
                );
                Arc::new(new_vec)
            }
        } else {
            // If the point doesn't exist in the map, we generate a random vector to cover the requested range
            let random_values = self
                .init_rand(point.clone(), requested_range)
                .into_iter()
                .map(|non_a| Arc::new(Atomic::new(non_a)))
                .collect();
            Arc::new(random_values)
        }
    }

    fn inner_get(&self, point: &Point) -> Option<&Arc<Vec<AtomicU8Arc>>> {
        self.inner.get(point)
    }

    fn set(&mut self, point: Point, vec: Vec<AtomicU8Arc>) {
        self.inner.insert(point, Arc::new(vec));
    }

    fn mutate<F>(&mut self, point: &Point, maybe_range: Option<std::ops::Range<usize>>, func: F)
    where
        F: FnOnce(&mut Arc<Vec<AtomicU8Arc>>),
    {
        let mut bitvec = self.get(point, maybe_range);
        func(&mut bitvec);
        self.set(point.clone(), bitvec.to_vec());
    }
}

impl LocalSharedSpace {

    fn init_rand(&self, point: Point, range: std::ops::Range<usize>) -> Vec<u8> {
        let memoized_points = MEMOIZED_POINTS.read().unwrap();

        if let Some(vec) = memoized_points.get(&point) {
            if vec.len() > range.end {
                // If the end of the range is within the memoized values, return the requested sub-slice
                let new_vec: Vec<u8> = vec[range.clone()]
                    .iter()
                    .map(|v| v.load(Ordering::Acquire))
                    .collect();
                return new_vec;
            }
        }

        drop(memoized_points); // Drop the read lock

        let mut rng = self.seed_rng(&point);
        let mut memoized_points = MEMOIZED_POINTS.write().unwrap();
        let vec = memoized_points
            .entry(point.clone())
            .or_insert_with(|| Vec::new());

        for _ in vec.len()..range.end {
            let byte = Atomic::new(rng.gen::<u8>());
            vec.push(byte);
        }

        // Return the requested sub-slice of the RNG stream
        let new_vec: Vec<u8> = vec[range.clone()]
            .iter()
            .map(|v| v.load(Ordering::Acquire))
            .collect();
        new_vec
    }

    fn seed_rng(&self, point: &Point) -> ChaCha8Rng {
        let seed = point
            .iter()
            .fold(0u64, |acc, &x| acc.rotate_left(1) ^ (x as u64));
        ChaCha8Rng::seed_from_u64(seed)
    }

}

#[derive(Clone)]
pub struct DiskSharedSpace {
    foreign: Option<Arc<dyn ForeignInterface<RemoteSharedSpace>>>,
}

impl SharedSpace for DiskSharedSpace {
    type HigherLevel = RemoteSharedSpace;
        fn new() -> Self {
        DiskSharedSpace {
            foreign: None
        }
    }

    fn link_foreign(&mut self, foreign: Option<Arc<dyn ForeignInterface<RemoteSharedSpace>>>){
        self.foreign = foreign;
    }

    fn inner_get(&self, point: &Point) -> Option<&Arc<Vec<AtomicU8Arc>>>{
        unimplemented!()
    }
}

#[derive(Clone)]
pub struct RemoteSharedSpace {
    // todo add a connection field when I know what networking should look like
    foreign: Option<Arc<dyn ForeignInterface<RemoteSharedSpace>>>,
}

impl SharedSpace for RemoteSharedSpace {
    type HigherLevel = RemoteSharedSpace;
    
    fn new() -> Self {
        RemoteSharedSpace {
            foreign: None
        }
    }

    fn link_foreign(&mut self, foreign: Option<Arc<dyn ForeignInterface<RemoteSharedSpace>>>){
        self.foreign = foreign;
    }

    fn inner_get(&self, point: &Point) -> Option<&Arc<Vec<AtomicU8Arc>>>{
        unimplemented!()
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
pub struct LiveRegionView<'a, S> {
    space: &'a S,
    origin: Point,
    dims: Point,
}

impl<'a, S: SharedSpace + Clone> LiveRegionView<'a, S> {
    pub fn new(space: &'a S, origin: Point, dims: Point) -> Self {
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

    pub fn iter_extant(&self) -> impl Iterator<Item = (Point, Arc<Vec<AtomicU8Arc>>)> + '_ {
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
            self.space
                .inner_get(&point)
                .map(|bitvec| (point, Arc::clone(bitvec)))
        })
    }

    pub fn iter_full(&self) -> impl Iterator<Item = (Point, Arc<Vec<AtomicU8Arc>>)> + '_ {
        generate_points_in_region(self.dims.clone()).map(move |rel_point| {
            let point: Vec<i32> = self
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
            (point.clone(), self.space.get(&point, None))
        })
    }
}

pub struct DesparsedRegionView<'a, S> {
    inner: LiveRegionView<'a, S>,
    dims: usize,
    points_map: HashMap<Point, Vec<(usize, i32, Point)>>,
    dense_map: HashMap<Point, Point>,
    stack: Vec<Point>,
    visited: HashSet<Point>,
}

impl<'a, S: SharedSpace + Clone> DesparsedRegionView<'a, S> {
    pub fn new(inner: LiveRegionView<'a, S>, dims: usize) -> Self {
        Self {
            inner,
            dims,
            points_map: HashMap::new(),
            dense_map: HashMap::new(),
            stack: Vec::new(),
            visited: HashSet::new(),
        }
    }

    fn get_direct_neighbors(&self, point: &Point) -> Vec<(usize, i32, Point)> {
        let mut neighbors = Vec::new();

        for i in 0..self.dims {
            let mut distance = 1;
            let mut search_status = (true, true); // Track search status in both directions (pos, neg).

            while search_status.0 || search_status.1 {
                // Continue if either direction is still being searched.
                let mut pos_neighbor = point.clone();
                let mut neg_neighbor = point.clone();
                pos_neighbor[i] += distance;
                neg_neighbor[i] -= distance;

                if search_status.0 && pos_neighbor[i] < self.inner.dims[i] {
                    if let Some(_) = self.inner.space.inner_get(&pos_neighbor) {
                        neighbors.push((i, distance as i32, pos_neighbor));
                        search_status.0 = false;
                    }
                } else {
                    search_status.0 = false;
                }

                if search_status.1 && neg_neighbor[i] >= 0 {
                    if let Some(_) = self.inner.space.inner_get(&neg_neighbor) {
                        neighbors.push((i, -distance as i32, neg_neighbor));
                        search_status.1 = false;
                    }
                } else {
                    search_status.1 = false;
                }

                distance += 1;
            }
        }

        neighbors
    }

    pub fn next_desparse(&mut self) -> Option<(Point, Arc<Vec<AtomicU8Arc>>)> {
        if self.points_map.is_empty() {
            for (point, _) in self.inner.iter_extant() {
                let neighbors = self.get_direct_neighbors(&point);
                self.points_map.insert(point, neighbors);
            }
            let starting_point = self.inner.origin.clone();
            self.dense_map
                .insert(starting_point.clone(), vec![0; starting_point.len()]);
            self.stack.push(starting_point);
        }

        while !self.stack.is_empty() || self.visited.len() < self.points_map.len() {
            if self.stack.is_empty() {
                if let Some(unvisited_point) =
                    self.points_map.keys().find(|k| !self.visited.contains(k.clone()))
                {
                    self.stack.push(unvisited_point.clone());
                }
            }

            if let Some(point) = self.stack.pop() {
                if !self.visited.contains(&point) {
                    self.visited.insert(point.clone());
                    if let Some(neighbors) = self.points_map.get(&point) {
                        for (dir, _, neighbor_point) in neighbors {
                            self.stack.push(neighbor_point.clone());
                            let mut dense_point = self.dense_map.get(&point).unwrap().clone();
                            dense_point[dir % self.dims] += 1;
                            self.dense_map.insert(neighbor_point.clone(), dense_point);
                        }
                    }
                    return Some((
                        self.dense_map.get(&point).unwrap().clone(),
                        self.inner.space.get(&point, None),
                    ));
                }
            }
        }
        None
    }
}

impl<'a, S: SharedSpace + Clone> Iterator for DesparsedRegionView<'a, S>{
    type Item = (Point, Arc<Vec<AtomicU8Arc>>);

    fn next(&mut self) -> Option<Self::Item> {
        self.next_desparse()
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use lazydeseriter::LazyDeserializer;

    #[derive(Debug, PartialEq, Eq, PartialOrd, LazyDeserializer)]
    pub enum TestEnum {
        End,
        A(Box<TestEnum>),
        B(Box<TestEnum>, Box<TestEnum>),
    }

    #[test]
    fn lazy_deseriter_deseriterizes() {
        let data: Arc<Vec<AtomicU8Arc>> = Arc::new(vec![
            Arc::new(Atomic::new(1)),
            Arc::new(Atomic::new(2)),
            Arc::new(Atomic::new(0)),
            Arc::new(Atomic::new(0)),
        ]);
        let mut iterator = TestEnumLazyDeserializer::new(data);

        assert_eq!(
            iterator.next(),
            Some(TestEnum::A(Box::new(TestEnum::B(
                Box::new(TestEnum::End),
                Box::new(TestEnum::End)
            ))))
        );
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn generate_chains_from_space() {
        let mut world = LocalSharedSpace::new();
        let test_origin = vec![0, 0, 0, 0, 1];
        let test_dims = vec![0, 50, 3, 2, 0];
        for target_y in 0..50 {
            if let Err(e) = world.duplicate_to(
                &vec![0, 0, 0, 0, target_y],
                vec![0, target_y, 0, 0, 1],
                None,
            ) {
                panic!("{}", e);
            }
        }
        let test_region = Arc::new(LiveRegionView::new(&world, test_origin, test_dims));
        let test_enum_full: Vec<TestEnum> = test_region
            .iter_full()
            .flat_map(|item| {
                let curr_enum_var: Vec<TestEnum> =
                    TestEnumLazyDeserializer::new(Arc::clone(&item.1)).collect();
                curr_enum_var
            })
            .collect();
        let test_enum_sparse: Vec<TestEnum> = test_region
            .iter_extant()
            .flat_map(|item| {
                let curr_enum_var: Vec<TestEnum> =
                    TestEnumLazyDeserializer::new(Arc::clone(&item.1)).collect();
                curr_enum_var
            })
            .collect();
        assert!(
            test_enum_full.len() >= 300,
            "full space must contain elements based on dimensionality (may be bigger)"
        );
        assert!(
            test_enum_sparse.len() >= 50 && test_enum_full.len() > test_enum_sparse.len(),
            "sparse space must contain only explicitly extant elements"
        );
    }
}
