// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Where a frontend's values live, and typed positions in the binary inputs.
//!
//! A frontend value is either a cell of its own field's commitment or a group
//! of bits in the binary commitment. Bit groups are absolute indices into the
//! binary participant's shared input array, least significant bit first.
//! Values that no binary circuit reads (masks, pads, one-time pads) are placed
//! in a reserved suffix beyond the format circuit's own input width, so the
//! format circuit cannot address them.

/// An untyped bit group: `width` consecutive binary inputs from `start`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Group {
    pub start: usize,
    pub width: usize,
}
impl Group {
    pub fn end(&self) -> usize {
        self.start + self.width
    }
    pub fn bit(&self, j: usize) -> usize {
        assert!(j < self.width);
        self.start + j
    }
}

/// A typed position of an N-bit word in the binary input array.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BitGroup<const N: usize> {
    start: usize,
}
impl<const N: usize> BitGroup<N> {
    pub fn group(self) -> Group {
        Group {
            start: self.start,
            width: N,
        }
    }
}

/// Allocator for the reserved suffix that follows the format circuit's inputs.
/// Allocation order is the witness order: `bits` places values accordingly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReservedSuffix {
    start: usize,
    end: usize,
}
impl ReservedSuffix {
    /// `format_width` is the format circuit's `ninput`.
    pub fn new(format_width: usize) -> Self {
        Self {
            start: format_width,
            end: format_width,
        }
    }
    pub fn word<const N: usize>(&mut self) -> BitGroup<N> {
        let start = self.end;
        self.end += N;
        BitGroup { start }
    }
    pub fn group(&mut self, width: usize) -> Group {
        let start = self.end;
        self.end += width;
        Group { start, width }
    }
    pub fn start(&self) -> usize {
        self.start
    }
    pub fn end(&self) -> usize {
        self.end
    }
    pub fn len(&self) -> usize {
        self.end - self.start
    }
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }
    /// A zeroed witness segment for the whole suffix.
    pub fn witness(&self) -> ReservedWitness<'_> {
        ReservedWitness {
            suffix: self,
            bits: vec![false; self.len()],
        }
    }
}

/// The prover's values for a reserved suffix, written by typed position.
pub struct ReservedWitness<'a> {
    suffix: &'a ReservedSuffix,
    bits: Vec<bool>,
}
impl ReservedWitness<'_> {
    pub fn set(
        &mut self,
        group: Group,
        bits: impl IntoIterator<Item = bool>,
    ) -> Result<(), String> {
        if group.start < self.suffix.start || group.end() > self.suffix.end {
            return Err("bit group outside the reserved suffix".into());
        }
        let bits: Vec<bool> = bits.into_iter().collect();
        if bits.len() != group.width {
            return Err("bit count does not match the group width".into());
        }
        let at = group.start - self.suffix.start;
        self.bits[at..at + group.width].copy_from_slice(&bits);
        Ok(())
    }
    pub fn into_bits(self) -> Vec<bool> {
        self.bits
    }
}

/// Where one value of a foreign-capable frontend lives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Storage {
    /// Cell index in this frontend's own commitment.
    Native(usize),
    /// The bits of a prime-field value in the binary commitment.
    Foreign(Group),
}

/// Storage of a frontend's value vector `[private inputs | sumcheck pads]`.
/// Native cells are numbered densely in vector order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StorageMap {
    entries: Vec<Storage>,
    native: usize,
}
impl StorageMap {
    /// Store values listed in `foreign` (value index, group) as bits in the
    /// binary commitment; all others natively.
    pub fn new(values: usize, foreign: &[(usize, Group)]) -> Result<Self, String> {
        let mut entries: Vec<Option<Group>> = vec![None; values];
        for &(v, group) in foreign {
            let slot = entries.get_mut(v).ok_or("foreign value index")?;
            if slot.replace(group).is_some() {
                return Err("foreign value listed twice".into());
            }
        }
        let mut native = 0;
        let entries = entries
            .into_iter()
            .map(|s| match s {
                Some(group) => Storage::Foreign(group),
                None => {
                    native += 1;
                    Storage::Native(native - 1)
                }
            })
            .collect();
        Ok(Self { entries, native })
    }
    pub fn entries(&self) -> &[Storage] {
        &self.entries
    }
    pub fn native_cells(&self) -> usize {
        self.native
    }
    pub fn is_pure_foreign(&self) -> bool {
        self.native == 0
    }
}

/// A maximal run of consecutive values stored alike. Runs are the storage
/// map's layout parameters as they are bound to the transcript.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Run {
    /// Values `first..first+count` in native cells `cell..cell+count`.
    Native {
        first: usize,
        count: usize,
        cell: usize,
    },
    /// Values `first..first+count`, each a prime-field value whose bits are
    /// the group of `width` bits at `start + i*width`.
    Prime {
        first: usize,
        count: usize,
        start: usize,
        width: usize,
    },
}
impl StorageMap {
    /// The map as maximal runs, in value order. The encoding is canonical:
    /// equal maps give equal runs.
    pub fn runs(&self) -> Vec<Run> {
        let mut runs: Vec<Run> = Vec::new();
        for (v, s) in self.entries.iter().enumerate() {
            let extended = match (runs.last_mut(), s) {
                (
                    Some(Run::Native {
                        first,
                        count,
                        cell: c0,
                    }),
                    Storage::Native(cell),
                ) if *first + *count == v && *c0 + *count == *cell => {
                    *count += 1;
                    true
                }
                (
                    Some(Run::Prime {
                        first,
                        count,
                        start,
                        width,
                    }),
                    Storage::Foreign(g),
                ) if *first + *count == v
                    && g.width == *width
                    && g.start == *start + *count * *width =>
                {
                    *count += 1;
                    true
                }
                _ => false,
            };
            if !extended {
                runs.push(match *s {
                    Storage::Native(cell) => Run::Native {
                        first: v,
                        count: 1,
                        cell,
                    },
                    Storage::Foreign(g) => Run::Prime {
                        first: v,
                        count: 1,
                        start: g.start,
                        width: g.width,
                    },
                });
            }
        }
        runs
    }
}

/// A linear claim over foreign-stored values, modulo the claim field's order.
/// Splitting a frontend's claim produces it; the cross-field adapter proves it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModularClaim<E> {
    pub terms: Vec<(Group, E)>,
    pub target: E,
}
impl<E> ModularClaim<E> {
    /// Total committed bits read by the claim.
    pub fn bits(&self) -> usize {
        self.terms.iter().map(|(g, _)| g.width).sum()
    }
}

#[cfg(test)]
#[path = "../tests/storage.rs"]
mod tests;
