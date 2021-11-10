//! # WGSOFT Diff Library
//!
//! This crate provides implementation of a LCS-based difference algorithm,
//! optimized for using in diff-like utilities.
//!
//! # Get Started
//!
//! This crate uses traits to implement its functionality. To get started,
//! read the documentation of following traits:
//!
//! * [`Lcs`]
//! * [`Diff`]
//! * [`Patch`]
//! * [`Patched`]
//!
//! These traits are sealed and are implemented only for slices and [`Vec`]s.
//!
//! [`Lcs`]: Lcs
//! [`Diff`]: Diff
//! [`Patch`]: Patch
//! [`Patched`]: Patched
//! [`Vec`]: Vec

use std::{cmp, ops::Range};

use self::private::Sealed;

/// An operation of deletion of a range of elements from a slice.
pub type Deletion = Range<usize>;

/// An operation of insertion a slice of elements into a slice.
#[derive(Debug, PartialEq, Eq)]
pub struct Insertion<'a, T> {
    /// Position to insert into.
    pub start: usize,
    /// Data to be inserted.
    pub data: &'a [T],
}

impl<'a, T> Insertion<'a, T> {
    /// Constructs a new [`Insertion`] from insertion position and data to be
    /// inserted.
    ///
    /// [`Insertion`]: Insertion
    pub fn new(start: usize, data: &'a [T]) -> Self {
        Insertion { start, data }
    }

    /// Convenience method that constructs an owned version of `self`.
    ///
    /// [`Insertion`]: Insertion
    pub fn to_owned(&self) -> OwnedInsertion<T>
    where
        T: Clone,
    {
        self.into()
    }
}

impl<'a, T> From<&'a OwnedInsertion<T>> for Insertion<'a, T> {
    fn from(owned_insertion: &'a OwnedInsertion<T>) -> Self {
        Insertion::new(owned_insertion.start, &owned_insertion.data)
    }
}

/// Owned version of [`Insertion`].
///
/// This `struct` cannot be used in [`patch`] method.
///
/// [`Insertion`]: Insertion
/// [`patch`]: Patch::patch
pub struct OwnedInsertion<T> {
    /// Position to insert into.
    pub start: usize,
    /// Data to be inserted.
    pub data: Vec<T>,
}

impl<T> OwnedInsertion<T> {
    /// Constructs a new [`OwnedInsertion`] from insertion position and data to
    /// be inserted.
    ///
    /// [`OwnedInsertion`]: OwnedInsertion
    pub fn new(start: usize, data: Vec<T>) -> Self {
        OwnedInsertion { start, data }
    }

    /// Convenience method that constructs a borrowed version of `self`.
    ///
    /// [`Insertion`]: Insertion
    /// [`patch`]: Patch::patch
    pub fn borrow(&self) -> Insertion<T> {
        self.into()
    }
}

impl<T: Clone> From<&Insertion<'_, T>> for OwnedInsertion<T> {
    fn from(insertion: &Insertion<T>) -> Self {
        OwnedInsertion::new(insertion.start, insertion.data.to_vec())
    }
}

/// Description of the difference between two slices.
///
/// This `struct` is the return type of [`diff`] method and can be used in
/// [`patch`] method as well.
///
/// [`diff`]: Diff::diff
/// [`patch`]: Patch::patch
#[derive(Debug, PartialEq, Eq)]
pub struct Difference<'a, T> {
    /// All operations of deletions from a slice.
    pub deletions: Vec<Deletion>,
    /// All operations of insertions into a slice.
    pub insertions: Vec<Insertion<'a, T>>,
}

impl<'a, T> Difference<'a, T> {
    /// Constructs a new [`Difference`] that represents no difference between
    /// slices.
    ///
    /// [`Difference`]: Difference
    pub fn empty() -> Self {
        Difference::new(Vec::new(), Vec::new())
    }

    /// Contructs a new [`Difference`] from [`Deletion`]s and [`Insertion`]s.
    ///
    /// [`Difference`]: Difference
    /// [`Deletion`]: Deletion
    /// [`Insertion`]: Insertion
    pub fn new(
        deletions: Vec<Deletion>,
        insertions: Vec<Insertion<'a, T>>,
    ) -> Self {
        Difference { deletions, insertions }
    }

    /// Convenience that constructs [`Difference`] from [`Deletion`]s only.
    ///
    /// [`Difference`]: Difference
    /// [`Deletion`]: Deletion
    pub fn from_deletions(deletions: Vec<Deletion>) -> Self {
        deletions.into()
    }

    /// Convenience that constructs [`Difference`] from [`Insertion`]s only.
    ///
    /// [`Difference`]: Difference
    /// [`Insertion`]: Insertion
    pub fn from_insertions(insertions: Vec<Insertion<'a, T>>) -> Self {
        insertions.into()
    }

    /// Convenience method that constructs an owned version of `self`.
    pub fn to_owned(&self) -> OwnedDifference<T>
    where
        T: Clone,
    {
        self.into()
    }
}

impl<T> From<Vec<Deletion>> for Difference<'_, T> {
    fn from(deletions: Vec<Deletion>) -> Self {
        Difference { deletions, insertions: Vec::new() }
    }
}

impl<'a, T> From<Vec<Insertion<'a, T>>> for Difference<'a, T> {
    fn from(insertions: Vec<Insertion<'a, T>>) -> Self {
        Difference { deletions: Vec::new(), insertions }
    }
}

impl<'a, T> From<&'a OwnedDifference<T>> for Difference<'a, T> {
    fn from(owned_difference: &'a OwnedDifference<T>) -> Self {
        Difference::new(
            owned_difference.deletions.clone(),
            owned_difference.insertions.iter().map(Into::into).collect(),
        )
    }
}

/// Owned version of [`Difference`].
///
/// This `struct` cannot be used in [`patch`] method.
///
/// [`Difference`]: Difference
/// [`patch`]: Patch::patch
pub struct OwnedDifference<T> {
    /// All operations of deletions from a slice.
    pub deletions: Vec<Deletion>,
    /// All operations of insertion into a slice.
    pub insertions: Vec<OwnedInsertion<T>>,
}

impl<T> OwnedDifference<T> {
    /// Constructs a new [`OwnedDifference`] that represents no difference
    /// between slices.
    ///
    /// [`OwnedDifference`]: OwnedDifference
    pub fn empty() -> Self {
        OwnedDifference::new(Vec::new(), Vec::new())
    }

    /// Constructs a new [`OwnedDifference`] from [`Deletion`]s and
    /// [`OwnedInsertion`]s.
    ///
    /// [`OwnedDifference`]: OwnedDifference
    /// [`Deletion`]: Deletion
    /// [`OwnedInsertion`]: OwnedInsertion
    pub fn new(
        deletions: Vec<Deletion>,
        insertions: Vec<OwnedInsertion<T>>,
    ) -> Self {
        OwnedDifference { deletions, insertions }
    }

    /// Convenience method that constructs a new [`OwnedDifference`] from
    /// [`Deletion`]s only.
    /// 
    /// [`OwnedDifference`]: OwnedDifference
    /// [`Deletion`]: Deletion
    pub fn from_deletions(deletions: Vec<Deletion>) -> Self {
        deletions.into()
    }

    /// Convenience method that constructs a new [`OwnedDifference`] from
    /// [`OwnedInsertion`]s only.
    /// 
    /// [`OwnedDifference`]: OwnedDifference
    /// [`OwnedInsertion`]: OwnedInsertion
    pub fn from_insertions(insertions: Vec<OwnedInsertion<T>>) -> Self {
        insertions.into()
    }

    /// Convenience method that constructs a borrowed version of `self`.
    pub fn borrow(&self) -> Difference<T> {
        self.into()
    }
}

impl<T> From<Vec<Deletion>> for OwnedDifference<T> {
    fn from(deletions: Vec<Deletion>) -> Self {
        OwnedDifference { deletions, insertions: Vec::new() }
    }
}

impl<T> From<Vec<OwnedInsertion<T>>> for OwnedDifference<T> {
    fn from(insertions: Vec<OwnedInsertion<T>>) -> Self {
        OwnedDifference { deletions: Vec::new(), insertions }
    }
}

impl<T: Clone> From<&Difference<'_, T>> for OwnedDifference<T> {
    fn from(difference: &Difference<T>) -> Self {
        OwnedDifference::new(
            difference.deletions.clone(),
            difference.insertions.iter().map(Into::into).collect(),
        )
    }
}

/// Trait that contains a method for computing Largest Common Subsequence of two
/// slices.
pub trait Lcs: Sealed {
    /// Calculates the LCS of two slices.
    ///
    /// The [`Vec`]s that this method returns contain indices of elements in
    /// the slices that are common between them. The left value in the tuple
    /// corresponds to `self` and the right value corresponds to `other`.
    fn lcs(&self, other: &Self) -> (Vec<usize>, Vec<usize>);
}

impl<T: Eq> Lcs for [T] {
    fn lcs(&self, other: &Self) -> (Vec<usize>, Vec<usize>) {
        let mut lengths = vec![vec![0; other.len() + 1]; self.len() + 1];

        for (index_self, value_self) in self.iter().enumerate().rev() {
            for (index_other, value_other) in other.iter().enumerate().rev() {
                lengths[index_self][index_other] =
                    if value_self == value_other {
                        lengths[index_self + 1][index_other + 1] + 1
                    } else {
                        cmp::max(
                            lengths[index_self + 1][index_other],
                            lengths[index_self][index_other + 1],
                        )
                    };
            }
        }

        let mut result_self = Vec::new();
        let mut result_other = Vec::new();
        let mut index_self = 0;
        let mut index_other = 0;

        while lengths[index_self][index_other] > 0 {
            if self[index_self] == other[index_other] {
                result_self.push(index_self);
                result_other.push(index_other);

                index_self += 1;
                index_other += 1;
            } else if lengths[index_self + 1][index_other]
                > lengths[index_self][index_other + 1]
            {
                index_self += 1;
            } else {
                index_other += 1;
            }
        }

        (result_self, result_other)
    }
}

impl<T: Eq> Lcs for Vec<T> {
    fn lcs(&self, other: &Self) -> (Vec<usize>, Vec<usize>) {
        (&self[..]).lcs(other)
    }
}

/// Trait that contains a method for computing the LCS based difference of two
/// slices.
pub trait Diff<T>: Lcs {
    /// Calculates the LCS based difference of two slices.
    ///
    /// `self` is assumed to be the new slice, and `old` is assumed to be the
    /// old slice, so in the return value changes are meant to be applied to
    /// `old`, giving `self` in the result.
    fn diff(&self, old: &Self) -> Difference<T>;
}

impl<T: Eq> Diff<T> for [T] {
    fn diff(&self, old: &Self) -> Difference<T> {
        let (lcs_old, lcs_self) = old.lcs(self);

        let mut result = Difference::empty();

        for index in (0..old.len()).filter(|index| {
            lcs_old.binary_search(index).is_err()
        }) {
            match result.deletions.last_mut() {
                Some(Deletion { end, .. }) if index == *end => *end += 1,
                _ => result.deletions.push(index..index + 1),
            }
        }

        for index in (0..self.len()).filter(|index| {
            lcs_self.binary_search(index).is_err()
        }) {
            match result.insertions.last_mut() {
                Some(Insertion {
                    start,
                    data,
                }) if index == *start + data.len() => {
                    *data = &self[*start..=index];
                },
                _ => result.insertions.push(
                    Insertion::new(index, &self[index..=index])
                ),
            }
        }

        result
    }
}

impl<T: Eq> Diff<T> for Vec<T> {
    fn diff(&self, old: &Self) -> Difference<T> {
        (&self[..]).diff(old)
    }
}

/// Trait that contains a method for modifying data according to previously
/// obtained [`Difference`].
///
/// [`Difference`]: Difference
pub trait Patch<T>: Diff<T> {
    /// Modifies the data according to the changes listed in `diff`.
    fn patch(&mut self, diff: Difference<T>);
}

impl<T: Eq + Clone> Patch<T> for Vec<T> {
    fn patch(&mut self, diff: Difference<T>) {
        let Difference { deletions, insertions } = diff;

        for deletion in deletions.into_iter().rev() {
            self.drain(deletion);
        }

        for Insertion { start, data } in insertions {
            self.splice(start..start, data.iter().map(Clone::clone));
        }
    }
}

/// Convenience trait that contains a method for constructing new data with
/// changes from previously obtained [`Difference`] applied.
///
/// [`Difference`]: Difference
pub trait Patched<T>: Diff<T> {
    /// Returns a modified version of `self` according to changes listed in
    /// `diff`.
    fn patched(&self, diff: Difference<T>) -> Vec<T>;
}

impl<T: Eq + Clone> Patched<T> for [T] {
    fn patched(&self, diff: Difference<T>) -> Vec<T> {
        let mut vec = self.to_vec();
        vec.patch(diff);
        vec
    }
}

impl<T: Eq + Clone> Patched<T> for Vec<T> {
    fn patched(&self, diff: Difference<T>) -> Vec<T> {
        (&self[..]).patched(diff)
    }
}

mod private {
    pub trait Sealed {}

    impl<T> Sealed for [T] {}
    
    impl<T> Sealed for Vec<T> {}
}

#[cfg(test)]
mod tests {
    use super::{Diff, Difference, Insertion, Lcs, Patched};

    #[test]
    fn lcs_1() {
        let (left_lcs, right_lcs) = b"BANANA".lcs(b"ATANA");
        assert_eq!(left_lcs, [1, 3, 4, 5]);
        assert_eq!(right_lcs, [0, 2, 3, 4]);
    }

    #[test]
    fn lcs_2() {
        let (left_lcs, right_lcs) = b"abc".lcs(b"ABC");
        assert_eq!(left_lcs, []);
        assert_eq!(right_lcs, []);
    }

    #[test]
    fn lcs_3() {
        let (left_lcs, right_lcs) = b"ABC".lcs(b"ABC");
        assert_eq!(left_lcs, [0, 1, 2]);
        assert_eq!(right_lcs, [0, 1, 2]);
    }

    #[test]
    fn lcs_4() {
        let (left_lcs, right_lcs) = b"ABC".lcs(b"");
        assert_eq!(left_lcs, []);
        assert_eq!(right_lcs, []);
    }

    #[test]
    fn lcs_5() {
        let (left_lcs, right_lcs) = b"".lcs(b"");
        assert_eq!(left_lcs, []);
        assert_eq!(right_lcs, []);
    }

    #[test]
    fn diff_1() {
        assert_eq!(b"ATANA".diff(b"BANANA"), Difference::new(
            vec![0..1, 2..3],
            vec![Insertion::new(1, b"T")],
        ));
    }

    #[test]
    fn diff_2() {
        assert_eq!(b"2345".diff(b"012389"), Difference::new(
            vec![0..2, 4..6],
            vec![Insertion::new(2, b"45")],
        ));
    }

    #[test]
    fn diff_3() {
        assert_eq!(b"72345".diff(b"012389"), Difference::new(
            vec![0..2, 4..6],
            vec![Insertion::new(0, b"7"), Insertion::new(3, b"45")],
        ));
    }

    #[test]
    fn patch_1() {
        let old = b"BANANA";
        let new = b"ATANA";
        assert_eq!(old.patched(new.diff(old)), new);
    }

    #[test]
    fn patch_2() {
        let old = b"012389";
        let new = b"2345";
        assert_eq!(old.patched(new.diff(old)), new);
    }

    #[test]
    fn patch_3() {
        let old = b"012389";
        let new = b"72345";
        assert_eq!(old.patched(new.diff(old)), new);
    }
}
