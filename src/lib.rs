#![no_std]

//! Disjoint borrows of slices.
//!
//! Provides the [`DisjointSlice`](struct.DisjointSlice.html) type, allowing disjoint borrows over
//! slices by adding runtime checks. Immutable borrows are allowed to intersect with other immutable
//! borrows, while mutable borrows may not intersect with any borrows.
//!
//! Borrow tracking is implemented as type-level list. This has the advantage that no allocation is
//! necessary, but also limits the number of disjoint borrows to a compile-time constant.
//! 
//! No-std compatible.
//!
//! # Example
//!
//! ```
//! use disjoint_borrow::DisjointSlice;
//!
//! let mut array = [1, 2, 3, 4, 5];
//! let mut ds = DisjointSlice::new(&mut array);
//! let (mut ds, mut a) = ds.get_mut(0..2);
//! let (_, mut b) = ds.get_mut(3..5);
//! 
//! a[0] *= -1;
//! b[1] *= -1;
//!
//! assert_eq!(a, &[-1, 2]);
//! assert_eq!(b, &[4, -5]);
//! ```

use core::{
    fmt,
    marker::PhantomData,
    ops::{Bound, Range, RangeBounds},
};

/// A set of ranges.
///
/// This traits should generally not be implemented outside the `disjoint_borrow` crate, but may be
/// referenced in order to be generic over the number of disjoint borrows.
pub unsafe trait RangeSet {
    #[doc(hidden)]
    fn intersects(&self, range: &Range<usize>) -> bool;

    #[doc(hidden)]
    fn fmt(&self, _formatter: &mut fmt::Formatter, _first: bool) -> Result<(), fmt::Error> {
        Ok(())
    }
}

unsafe impl<T: RangeSet> RangeSet for &T {
    #[inline]
    fn intersects(&self, range: &Range<usize>) -> bool {
        (*self).intersects(range)
    }

    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter, first: bool) -> Result<(), fmt::Error> {
        (*self).fmt(formatter, first)
    }
}

unsafe impl RangeSet for () {
    #[inline]
    fn intersects(&self, _: &Range<usize>) -> bool {
        false
    }
}

/// A "link" in the borrow chain. Every time a new range is borrowed, a new link is added.
#[derive(Clone)]
pub struct RangeLink<T> {
    range: Range<usize>,
    next: T,
}

unsafe impl<T> RangeSet for RangeLink<T>
where
    T: RangeSet,
{
    #[inline]
    fn intersects(&self, range: &Range<usize>) -> bool {
        (self.range.end > range.start && self.range.start < range.end)
            || self.next.intersects(range)
    }

    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter, first: bool) -> Result<(), fmt::Error> {
        if !first {
            formatter.write_str(", ")?;
        }

        fmt::Debug::fmt(&self.range, formatter)?;
        self.next.fmt(formatter, false)
    }
}

/// An error when retrieving a slice.
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// An error caused by indices being out of range for the given slice.
    InvalidIndex,

    /// An error caused by two intersecting non-compatible borrows.
    BorrowIntersection,
}

/// A slice that allows disjoint borrows over its elements. Mutable borrows may not intersect any
/// other borrows, but immutable borrows may intersect other immutable borrows.
///
/// Functions that borrow slices returns a new `DisjointSlice` object as the first parameter and
/// the slice as the second. The returned `DisjointSlice` object can be used to borrow further
/// slcies.
///
/// See the package documentation for more information.
pub struct DisjointSlice<'a, T, Borrows, MutBorrows> {
    ptr: *mut T,
    len: usize,
    borrows: Borrows,
    borrows_mut: MutBorrows,
    phantom: PhantomData<&'a mut T>,
}

impl<'a, T> DisjointSlice<'a, T, (), ()> {
    /// Creates a new `DistjointSlice` from a mutable slice.
    pub fn new(slice: &'a mut [T]) -> Self {
        DisjointSlice {
            ptr: slice.as_mut_ptr(),
            len: slice.len(),
            borrows: (),
            borrows_mut: (),
            phantom: PhantomData,
        }
    }
}

impl<'a, T, Borrows, MutBorrows> DisjointSlice<'a, T, Borrows, MutBorrows>
where
    Borrows: RangeSet,
    MutBorrows: RangeSet,
{
    /// Gets the length of the underlying slice.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the underlying slice is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Rertrieves an immutable subslice, panicking if the range is out of range of the slice or it
    /// intersects with any other mutable borrowed slices.
    #[inline]
    pub fn get<'b, R>(
        &'b mut self,
        index: R,
    ) -> (
        DisjointSlice<'b, T, RangeLink<&'b Borrows>, &'b MutBorrows>,
        &'b [T],
    )
    where
        R: RangeBounds<usize>,
    {
        let range = self.range(index);

        assert!(range.start <= self.len, "Range start out of range");
        assert!(range.end <= self.len, "Range end out of range");
        assert!(
            !self.borrows_mut.intersects(&range),
            "Range intersects with mutable borrows"
        );

        let len = range.end.saturating_sub(range.start);

        let slice = unsafe { core::slice::from_raw_parts(self.ptr.add(range.start), len) };

        (
            DisjointSlice {
                ptr: self.ptr,
                len: self.len,
                borrows: RangeLink {
                    range,
                    next: &self.borrows,
                },
                borrows_mut: &self.borrows_mut,
                phantom: self.phantom,
            },
            slice,
        )
    }

    /// Retrieves an immutable subslice, returning `Ok` if successfull or `Err` if the range
    /// is out of range of the slice or intersects with a mutable borrow.
    #[inline]
    pub fn try_get<'b, R>(
        &'b mut self,
        range: R,
    ) -> Result<
        (
            DisjointSlice<'b, T, RangeLink<&'b Borrows>, &'b MutBorrows>,
            &'b [T],
        ),
        Error,
    >
    where
        R: RangeBounds<usize>,
    {
        self.try_get_range(self.range(range))
    }

    #[inline]
    fn try_get_range<'b>(
        &'b mut self,
        range: Range<usize>,
    ) -> Result<
        (
            DisjointSlice<'b, T, RangeLink<&'b Borrows>, &'b MutBorrows>,
            &'b [T],
        ),
        Error,
    > {
        if range.start > self.len {
            return Err(Error::InvalidIndex);
        }

        if range.end > self.len {
            return Err(Error::InvalidIndex);
        }

        if self.borrows_mut.intersects(&range) {
            return Err(Error::BorrowIntersection);
        }

        let len = range.end.saturating_sub(range.start);

        let slice = unsafe { core::slice::from_raw_parts(self.ptr.add(range.start), len) };

        Ok((
            DisjointSlice {
                ptr: self.ptr,
                len: self.len,
                borrows: RangeLink {
                    range,
                    next: &self.borrows,
                },
                borrows_mut: &self.borrows_mut,
                phantom: self.phantom,
            },
            slice,
        ))
    }

    /// Rertrieves a mutable subslice, panicking if the range is out of range of the slice or it
    /// intersects with any other immuitable or mutable borrowed slices.
    #[inline]
    pub fn get_mut<'b, R>(
        &'b mut self,
        index: R,
    ) -> (
        DisjointSlice<'b, T, &'b Borrows, RangeLink<&'b MutBorrows>>,
        &'b mut [T],
    )
    where
        R: RangeBounds<usize>,
    {
        let range = self.range(index);

        assert!(range.start <= self.len, "Range start out of range");
        assert!(range.end <= self.len, "Range end out of range");
        assert!(
            !self.borrows.intersects(&range),
            "Range intersects with immutable borrows"
        );
        assert!(
            !self.borrows_mut.intersects(&range),
            "Range intersects with mutable borrows"
        );

        let len = range.end.saturating_sub(range.start);

        let slice = unsafe { core::slice::from_raw_parts_mut(self.ptr.add(range.start), len) };

        (
            DisjointSlice {
                ptr: self.ptr,
                len: self.len,
                borrows: &self.borrows,
                borrows_mut: RangeLink {
                    range,
                    next: &self.borrows_mut,
                },
                phantom: self.phantom,
            },
            slice,
        )
    }

    /// Retrieves an immutable subslice, returning `Ok` if successfull or `Err` if the range
    /// is out of range of the slice or intersects with any other immutable or mutable borrow.
    #[inline]
    pub fn try_get_mut<'b, R>(
        &'b mut self,
        range: R,
    ) -> Result<
        (
            DisjointSlice<'b, T, &'b Borrows, RangeLink<&'b MutBorrows>>,
            &'b mut [T],
        ),
        Error,
    >
    where
        R: RangeBounds<usize>,
    {
        self.try_get_range_mut(self.range(range))
    }

    #[inline]
    fn try_get_range_mut<'b>(
        &'b mut self,
        range: Range<usize>,
    ) -> Result<
        (
            DisjointSlice<'b, T, &'b Borrows, RangeLink<&'b MutBorrows>>,
            &'b mut [T],
        ),
        Error,
    > {
        if range.start > self.len {
            return Err(Error::InvalidIndex);
        }

        if range.end > self.len {
            return Err(Error::InvalidIndex);
        }

        if self.borrows.intersects(&range) {
            return Err(Error::BorrowIntersection);
        }

        if self.borrows_mut.intersects(&range) {
            return Err(Error::BorrowIntersection);
        }

        let len = range.end.saturating_sub(range.start);

        let slice = unsafe { core::slice::from_raw_parts_mut(self.ptr.add(range.start), len) };

        Ok((
            DisjointSlice {
                ptr: self.ptr,
                len: self.len,
                borrows: &self.borrows,
                borrows_mut: RangeLink {
                    range,
                    next: &self.borrows_mut,
                },
                phantom: self.phantom,
            },
            slice,
        ))
    }

    #[inline]
    fn range<R>(&self, range: R) -> Range<usize>
    where
        R: RangeBounds<usize>,
    {
        let lo = match range.start_bound() {
            Bound::Included(&n) => n,
            Bound::Excluded(&n) => n + 1,
            Bound::Unbounded => 0,
        };

        let hi = match range.end_bound() {
            Bound::Included(&n) => n + 1,
            Bound::Excluded(&n) => n,
            Bound::Unbounded => self.len,
        };

        (lo..hi)
    }
}

impl<'a, T, Borrows, MutBorrows> fmt::Debug for DisjointSlice<'a, T, Borrows, MutBorrows>
where
    Borrows: RangeSet,
    MutBorrows: RangeSet,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "DisjointSlice{{ borrows: [")?;
        self.borrows.fmt(f, true)?;
        write!(f, "], borrows_mut: [")?;
        self.borrows_mut.fmt(f, true)?;
        write!(f, "]}}")
    }
}

unsafe impl<'a, T, Borrows, MutBorrows> Send for DisjointSlice<'a, T, Borrows, MutBorrows> where
    T: Send
{
}

unsafe impl<'a, T, Borrows, MutBorrows> Sync for DisjointSlice<'a, T, Borrows, MutBorrows> where
    T: Sync
{
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let mut array = [1, 2, 3, 4, 5];
        let mut ds = DisjointSlice::new(&mut array[..]);
        let (mut ds, a) = ds.get(0..1);
        let (mut ds, b) = ds.get(1..2);
        let (mut ds, c) = ds.get_mut(2..3);
        let (_, d) = ds.get_mut(3..5);

        assert_eq!(a, &[1]);
        assert_eq!(b, &[2]);
        assert_eq!(c, &[3]);
        assert_eq!(d, &[4, 5]);
    }

    #[test]
    fn slice() {
        let mut array = [1, 2, 3, 4, 5];
        let mut sl = DisjointSlice::new(&mut array[..]);
        let (mut sl, a) = sl.get_mut(..3);
        let (_, b) = sl.get_mut(3..);

        assert_eq!(a, &[1, 2, 3]);
        assert_eq!(b, &[4, 5]);
    }

    #[test]
    #[should_panic]
    fn get_after_mut() {
        let mut array = [1, 2, 3, 4, 5];
        let mut sl = DisjointSlice::new(&mut array[..]);
        let (mut sl, _) = sl.get_mut(..3);
        sl.get(2..);
    }

    #[test]
    fn scoped() {
        let mut array = [1, 2, 3, 4, 5];
        let mut sl = DisjointSlice::new(&mut array[..]);
        let (mut sl, a) = sl.get_mut(..3);

        {
            sl.get_mut(3..);
        }

        let (_, b) = sl.get_mut(3..);

        assert_eq!(a, &[1, 2, 3]);
        assert_eq!(b, &[4, 5]);
    }

    #[test]
    #[should_panic]
    fn out_of_range() {
        let mut array = [1, 2, 3, 4, 5];
        let mut sl = DisjointSlice::new(&mut array[..]);
        sl.get(6..10);
    }

    #[test]
    fn backward_range() {
        let mut array = [1, 2, 3, 4, 5];
        let mut sl = DisjointSlice::new(&mut array[..]);
        let (_, a) = sl.get(4..3);
        assert_eq!(a, &[]);
    }

    #[test]
    fn one_past_end() {
        let mut array = [1, 2, 3, 4, 5];
        let mut sl = DisjointSlice::new(&mut array[..]);
        let (_, a) = sl.get(5..5);
        assert_eq!(a, &[]);
    }

    /// Edge case: does an empty range with start inside another range count as an intersection?
    /// Currently, we say that it does.
    #[test]
    #[should_panic]
    fn empty_intersect() {
        let mut array = [1, 2, 3];
        let mut ds = DisjointSlice::new(&mut array[..]);
        let (mut ds, _) = ds.get(0..3);
        ds.get_mut(1..1);
    }

    #[test]
    #[should_panic]
    fn backward_out_of_range() {
        let mut array = [1, 2, 3, 4, 5];
        let mut sl = DisjointSlice::new(&mut array[..]);
        sl.get(10..2);
    }

    #[test]
    fn try_get_out_of_range() {
        let mut array = [1, 2, 3, 4, 5];
        let mut ds = DisjointSlice::new(&mut array[..]);
        assert_eq!(ds.try_get(6..10).unwrap_err(), Error::InvalidIndex);
    }

    #[test]
    fn try_get_intersect() {
        let mut array = [1, 2, 3, 4, 5];
        let mut ds = DisjointSlice::new(&mut array[..]);
        let (mut ds, _) = ds.get_mut(1..3);
        assert_eq!(ds.try_get(0..2).unwrap_err(), Error::BorrowIntersection);
    }

    #[test]
    fn try_get_mut_out_of_range() {
        let mut array = [1, 2, 3, 4, 5];
        let mut ds = DisjointSlice::new(&mut array[..]);
        assert_eq!(ds.try_get_mut(6..10).unwrap_err(), Error::InvalidIndex);
    }

    #[test]
    fn try_get_mut_intersect() {
        let mut array = [1, 2, 3, 4, 5];
        let mut ds = DisjointSlice::new(&mut array[..]);
        let (mut ds, _) = ds.get(1..3);
        assert_eq!(ds.try_get_mut(0..2).unwrap_err(), Error::BorrowIntersection);
    }
}
