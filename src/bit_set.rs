use std::ops::BitOrAssign;
use std::{fmt, iter, mem, slice};

#[derive(Clone, Default)]
pub struct BitSet(Vec<u32>);

impl BitSet {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn contains(&self, x: u32) -> bool {
        self.0
            .get((x / u32::BITS) as usize)
            .map_or(false, |&u| u & 1 << (x % u32::BITS) != 0)
    }

    pub fn insert(&mut self, x: u32) {
        let i: usize = (x / u32::BITS) as usize;
        self.0
            .extend(iter::repeat(0).take((i + 1).saturating_sub(self.0.len())));
        self.0[i] |= 1 << (x % u32::BITS);
    }

    pub fn len(&self) -> u32 {
        self.0.iter().copied().map(u32::count_ones).sum()
    }

    pub fn clear(&mut self) {
        self.0.fill(0);
    }

    pub fn iter(&self) -> Iter<iter::Copied<slice::Iter<u32>>> {
        Iter::new(self.0.iter().copied())
    }
}

impl BitOrAssign<&BitSet> for BitSet {
    fn bitor_assign(&mut self, rhs: &BitSet) {
        for (a, &b) in self.0.iter_mut().zip(rhs.0.iter()) {
            *a |= b;
        }
        self.0
            .extend_from_slice(rhs.0.get(self.0.len()..).unwrap_or(&[]));
    }
}

impl BitOrAssign<BitSet> for BitSet {
    fn bitor_assign(&mut self, mut rhs: BitSet) {
        if rhs.0.len() > self.0.len() {
            mem::swap(self, &mut rhs);
        }
        *self |= &rhs;
    }
}

impl FromIterator<u32> for BitSet {
    fn from_iter<T: IntoIterator<Item = u32>>(iter: T) -> Self {
        let mut set = Self::new();
        for x in iter {
            set.insert(x);
        }
        set
    }
}

#[derive(Debug)]
pub struct Iter<I> {
    offset: u32,
    head: u32,
    tail: I,
}

impl<I: Iterator<Item = u32>> Iter<I> {
    fn new(mut iter: I) -> Self {
        Self {
            offset: 0,
            head: iter.next().unwrap_or(0),
            tail: iter,
        }
    }
}

impl<I: Iterator<Item = u32>> Iterator for Iter<I> {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        while self.head == 0 {
            self.head = self.tail.next()?;
            self.offset += u32::BITS;
        }
        let i = self.offset + self.head.trailing_zeros();
        self.head &= self.head - 1;
        Some(i)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.tail.size_hint() {
            (_, Some(h)) => (0, Some((1 + h) * u32::BITS as usize)),
            _ => (0, None),
        }
    }
}

impl<'a> IntoIterator for &'a BitSet {
    type Item = u32;
    type IntoIter = Iter<iter::Copied<slice::Iter<'a, u32>>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl fmt::Debug for BitSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_set().entries(self).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn try_insert() {
        let mut s = BitSet::new();
        s.insert(3);
        s.insert(64);
        assert_eq!(s.0.len(), 3);

        assert!(s.contains(3));
        assert!(s.contains(64));

        let mut iter = s.iter();
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(64));
        assert_eq!(iter.next(), None);
    }
}
