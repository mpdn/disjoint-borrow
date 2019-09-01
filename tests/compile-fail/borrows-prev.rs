extern crate disjoint_borrow;
use disjoint_borrow::DisjointSlice;

fn main() {
    let mut a = [1, 2, 3];
    let mut alpha = DisjointSlice::new(&mut a);
    let (beta, b) = alpha.get(1..2);
    drop(beta);
    alpha.get(1..2);
    //~^ cannot borrow `alpha` as mutable more than once at a time
    b[0];
}