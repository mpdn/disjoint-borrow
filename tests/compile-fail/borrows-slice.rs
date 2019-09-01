extern crate disjoint_borrow;
use disjoint_borrow::DisjointSlice;

fn main() {
    let mut a = [1, 2, 3];
    let mut sl = DisjointSlice::new(&mut a);
    a[0] = 1;
    //~^ ERROR cannot use `a` because it was mutably borrowed
    //~^^ ERROR cannot assign to `a[_]` because it is borrowed
    sl.get(0..1);
}