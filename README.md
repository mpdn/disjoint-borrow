[![Build Status](https://travis-ci.org/noctune/disjoint-borrow.svg?branch=master)](https://travis-ci.org/noctune/disjoint-borrow)

# disjoint-borrow

Disjoint borrows of slices.

Provides the [`DisjointSlice`](struct.DisjointSlice.html) type, allowing disjoint borrows over
slices by adding runtime checks. Immutable borrows are allowed to intersect with other immutable
borrows, while mutable borrows may not intersect with any borrows.

Borrow tracking is implemented as type-level list. This has the advantage that no allocation is
necessary, but also limits the number of disjoint borrows to a compile-time constant.

No-std compatible.

## Example

```rust
use disjoint_borrow::DisjointSlice;

let mut array = [1, 2, 3, 4, 5];
let mut ds = DisjointSlice::new(&mut array);
let (mut ds, mut a) = ds.get_mut(0..2);
let (_, mut b) = ds.get_mut(3..5);

a[0] *= -1;
b[1] *= -1;

assert_eq!(a, &[-1, 2]);
assert_eq!(b, &[4, -5]);
```

License: MIT
