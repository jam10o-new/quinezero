mod space;
use std::sync::Arc;

use prokio::*;

use crate::space::{SharedSpace, LiveRegionView, scheduler};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let world = SharedSpace::new();
    let test_origin = vec![0, 0, 0, 0, 1];
    let test_dims = vec![0, 50, 0, 0, 0];
    let test_region = Arc::new(LiveRegionView::new(&world, test_origin, test_dims));

    scheduler(test_region, |item|{
        todo!()
    }).await;

    println!("Hello, world!");
    Ok(())
     
}
