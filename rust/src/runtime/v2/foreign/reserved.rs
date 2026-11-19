// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The reserved suffix of the binary host's inputs, and typed positions in it.
//!
//! Values that no binary circuit reads (the split mask R, the adapter's
//! one-time pads) are placed in a reserved suffix beyond the format circuit's
//! own input width, so the format circuit cannot address them. The
//! composition allocates the suffix; the adapter mode places its pads in it.
use crate::runtime::v2::zk::storage::Group;

/// A typed position of an N-bit word in the binary input array.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct BitGroup<const N: usize>(Group);
impl<const N: usize> BitGroup<N> {
    pub(crate) fn group(self) -> Group {
        self.0
    }
}

/// Allocator for the reserved suffix that follows the format circuit's inputs.
/// Allocation order is the witness order: `bits` places values accordingly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReservedSuffix {
    start: usize,
    end: usize,
}
impl ReservedSuffix {
    /// `format_width` is the format circuit's `ninput`.
    pub(crate) fn new(format_width: usize) -> Self {
        Self {
            start: format_width,
            end: format_width,
        }
    }
    /// The next N-bit word; rejects a suffix whose end would overflow.
    pub(crate) fn word<const N: usize>(&mut self) -> Result<BitGroup<N>, String> {
        Ok(BitGroup(self.group(N)?))
    }
    /// The next `width` bits; rejects a suffix whose end would overflow.
    pub(crate) fn group(&mut self, width: usize) -> Result<Group, String> {
        let start = self.advance(width)?;
        Group::new(start, width)
    }
    /// Reserve `width` bits and return where they start. The end is checked
    /// before it is stored, so every group handed out has a valid end.
    fn advance(&mut self, width: usize) -> Result<usize, String> {
        let start = self.end;
        self.end = start
            .checked_add(width)
            .ok_or("reserved suffix end overflows")?;
        Ok(start)
    }
    #[cfg(test)]
    pub(crate) fn start(&self) -> usize {
        self.start
    }
    pub(crate) fn end(&self) -> usize {
        self.end
    }
    #[cfg(any(test, feature = "prover"))]
    pub(crate) fn len(&self) -> usize {
        self.end - self.start
    }
    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.start == self.end
    }
    /// A zeroed witness segment for the whole suffix.
    #[cfg(any(test, feature = "prover"))]
    pub(crate) fn witness(&self) -> ReservedWitness<'_> {
        ReservedWitness {
            suffix: self,
            bits: vec![false; self.len()],
        }
    }
}

/// The prover's values for a reserved suffix, written by typed position.
#[cfg(any(test, feature = "prover"))]
pub(crate) struct ReservedWitness<'a> {
    suffix: &'a ReservedSuffix,
    bits: Vec<bool>,
}
#[cfg(any(test, feature = "prover"))]
impl ReservedWitness<'_> {
    pub(crate) fn set(
        &mut self,
        group: Group,
        bits: impl IntoIterator<Item = bool>,
    ) -> Result<(), String> {
        if group.start() < self.suffix.start || group.end() > self.suffix.end {
            return Err("bit group outside the reserved suffix".into());
        }
        let bits: Vec<bool> = bits.into_iter().collect();
        if bits.len() != group.width() {
            return Err("bit count does not match the group width".into());
        }
        let at = group.start() - self.suffix.start;
        self.bits[at..at + group.width()].copy_from_slice(&bits);
        Ok(())
    }
    pub(crate) fn into_bits(self) -> Vec<bool> {
        self.bits
    }
}

#[cfg(test)]
mod tests;
