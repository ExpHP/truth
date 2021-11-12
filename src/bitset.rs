// I couldn't find a crate for something like this on crates.io.
// They all allocated.
//        -exp

use core::fmt;

/// Bit set backed by a single integer.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Default)]
pub struct BitSet32(u32);

impl BitSet32 {
    pub const fn new() -> Self { BitSet32(0) }
    pub const fn from_mask(mask: u32) -> Self { BitSet32(mask) }
    pub const fn from_bit(index: u32) -> Self { BitSet32::new().with_bit(index) }
    pub const fn len(self) -> usize { self.0.count_ones() as usize }
    pub const fn is_empty(self) -> bool { self.0 == 0 }
    pub const fn mask(self) -> u32 { self.0 }

    pub const fn contains(self, index: u32) -> bool { self.0 & (1 << index) != 0 }
    pub const fn with_bit(self, index: u32) -> Self { BitSet32(self.0 | 1 << index) }
    pub const fn without_bit(self, index: u32) -> Self { BitSet32(self.0 & !(1 << index)) }

    pub const fn first(self) -> Option<u32> { match self.0.trailing_zeros() {
        32 => None,
        count => Some(count),
    }}
    pub const fn last(self) -> Option<u32> { match self.0.leading_zeros() {
        32 => None,
        count => Some(32 - 1 - count),
    }}

    pub fn insert(&mut self, index: u32) -> bool {
        let new = self.with_bit(index);
        let changed = *self != new;
        *self = new;
        changed
    }
    pub fn remove(&mut self, index: u32) -> bool {
        let new = self.without_bit(index);
        let changed = *self != new;
        *self = new;
        changed
    }
    pub fn set_bit(&mut self, index: u32, enabled: bool) {
        if enabled { self.insert(index); }
        else { self.remove(index); }
    }

    /// Truncate to the first `len` bits; i.e. remove entries that are `>= len`
    pub fn with_upper_bound(self, len: u32) -> Self {
        BitSet32(self.0 & 1u32.checked_shl(len).unwrap_or(0).wrapping_sub(1))
    }
    /// Compute the bitwise complement, given the universe length.
    pub fn complement(self, len: u32) -> Self {
        (!self).with_upper_bound(len)
    }
}

impl fmt::Display for BitSet32 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::UpperHex::fmt(&self.0, f)
    }
}

impl fmt::Debug for BitSet32 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self, f)
    }
}

impl core::ops::BitAnd for BitSet32 {
    type Output = BitSet32;
    fn bitand(self, rhs: BitSet32) -> BitSet32 { BitSet32(self.0 & rhs.0) }
}

impl core::ops::BitOr for BitSet32 {
    type Output = BitSet32;
    fn bitor(self, rhs: BitSet32) -> BitSet32 { BitSet32(self.0 | rhs.0) }
}

impl core::ops::BitXor for BitSet32 {
    type Output = BitSet32;
    fn bitxor(self, rhs: BitSet32) -> BitSet32 { BitSet32(self.0 ^ rhs.0) }
}

impl core::ops::Not for BitSet32 {
    type Output = BitSet32;
    fn not(self) -> BitSet32 { BitSet32(!self.0) }
}

impl IntoIterator for BitSet32 {
    type IntoIter = IntoIter32;
    type Item = u32;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter32 { mask: self.0, index: 0 }
    }
}

#[derive(Debug, Clone)]
pub struct IntoIter32 {
    index: u32,
    mask: u32,
}

impl Iterator for IntoIter32 {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        match self.mask.trailing_zeros() {
            u32::BITS => None,
            zeros => {
                self.mask = self.mask >> (zeros + 1);
                self.index += zeros + 1;
                Some(self.index - 1)
            },
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let popcount = self.len();
        (popcount, Some(popcount))
    }
}

impl ExactSizeIterator for IntoIter32 {
    fn len(&self) -> usize { self.mask.count_ones() as usize }
}

impl FromIterator<u32> for BitSet32 {
    fn from_iter<T: IntoIterator<Item=u32>>(iter: T) -> Self {
        let mut out = Self::new();
        out.extend(iter);
        out
    }
}

impl Extend<u32> for BitSet32 {
    fn extend<T: IntoIterator<Item=u32>>(&mut self, iter: T) {
        for index in iter {
            self.insert(index);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basics() {
        let original = BitSet32::from_mask(0b100010);
        assert!(original.contains(5));
        assert!(!original.contains(4));

        let with_bit = original.with_bit(6);
        let mut inserted = original.clone();
        assert!(inserted.insert(6));
        assert_eq!(inserted, with_bit);
        assert!(!inserted.insert(6));
        assert_eq!(inserted, with_bit);
        assert!(inserted.contains(6));
        assert!(!original.contains(6));

        let without_bit = original.without_bit(1);
        let mut removed = original.clone();
        assert!(removed.remove(1));
        assert_eq!(removed, without_bit);
        assert!(!removed.remove(1));
        assert_eq!(removed, without_bit);
        assert_ne!(removed, original);
        assert!(!removed.contains(1));
        assert!(original.contains(1));
    }

    #[test]
    fn test_iter() {
        fn check_input(input: Vec<u32>, expected_mask: u32, expected_output: Vec<u32>) {
            let set = BitSet32::from_iter(input);
            assert_eq!(set.mask(), expected_mask);

            let len = expected_output.len();
            assert_eq!(set.len(), len);
            let iter = set.into_iter();
            assert_eq!(iter.len(), len);
            assert_eq!(iter.size_hint(), (len, Some(len)));
            assert_eq!(iter.collect::<Vec<_>>(), expected_output);
            assert_eq!(set.first(), expected_output.first().copied());
            assert_eq!(set.last(), expected_output.last().copied());
        }

        check_input(vec![1, 7, 2, 7, 31], 0x8000_0086, vec![1, 2, 7, 31]);
        check_input(vec![0], 0x1, vec![0]);
        check_input(vec![], 0x0, vec![]);
    }

    #[test]
    fn with_upper_bound() {
        assert_eq!(BitSet32::from_mask(0b11011010).with_upper_bound(4), BitSet32::from_mask(0b1010));
        assert_eq!(BitSet32::from_mask(0xFFFF).with_upper_bound(0), BitSet32::from_mask(0));
        assert_eq!(BitSet32::from_mask(0xFFFFFFFF).with_upper_bound(32), BitSet32::from_mask(0xFFFFFFFF));
    }

    #[test]
    fn complement() {
        assert_eq!(BitSet32::from_mask(0xC1).complement(8), BitSet32::from_mask(0x3E));
        assert_eq!(BitSet32::from_mask(0x3E).complement(8), BitSet32::from_mask(0xC1));
        assert_eq!(BitSet32::from_mask(0).complement(32), BitSet32::from_mask(0xFFFFFFFF));
    }
}
