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

/// One stored base-field coordinate of a foreign value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Coordinate {
    pub index: usize,
    pub group: Group,
}

/// Where one value of a foreign-capable frontend lives.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Storage {
    /// Cell index in this frontend's own commitment.
    Native(usize),
    /// Base-field coordinates held as bits in the binary commitment, in
    /// increasing coordinate order. Coordinates not listed are zero: a value
    /// of an extension field may store only its base-field part.
    Foreign(Vec<Coordinate>),
}
impl Storage {
    /// The single group of a prime-field foreign value.
    pub fn prime_group(&self) -> Option<Group> {
        match self {
            Storage::Foreign(c) if c.len() == 1 && c[0].index == 0 => Some(c[0].group),
            _ => None,
        }
    }
}

/// Storage of a frontend's value vector `[private inputs | sumcheck pads]`.
/// Native cells are numbered densely in vector order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StorageMap {
    entries: Vec<Storage>,
    native: usize,
}
impl StorageMap {
    /// Store values listed in `foreign` (value index, group) as single
    /// prime-field coordinates in the binary commitment; all others natively.
    pub fn new(values: usize, foreign: &[(usize, Group)]) -> Result<Self, String> {
        let coordinates: Vec<_> = foreign.iter().map(|&(v, g)| (v, 0, g)).collect();
        Self::with_coordinates(values, &coordinates)
    }
    /// Store the listed (value, coordinate, group) triples in the binary
    /// commitment; values with no listed coordinate are native.
    pub fn with_coordinates(
        values: usize,
        foreign: &[(usize, usize, Group)],
    ) -> Result<Self, String> {
        let mut entries: Vec<Option<Vec<Coordinate>>> = vec![None; values];
        for &(v, index, group) in foreign {
            let slot = entries
                .get_mut(v)
                .ok_or("foreign value index")?
                .get_or_insert_with(Vec::new);
            if slot.last().is_some_and(|c| c.index >= index) {
                return Err("foreign coordinates must be listed in increasing order".into());
            }
            slot.push(Coordinate { index, group });
        }
        let mut native = 0;
        let entries = entries
            .into_iter()
            .map(|s| match s {
                Some(coordinates) => Storage::Foreign(coordinates),
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
    /// One value stored as the listed base-field coordinates.
    Coordinates {
        value: usize,
        coordinates: Vec<Coordinate>,
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
                    _,
                ) if *first + *count == v
                    && s.prime_group().is_some_and(|g| {
                        g.width == *width && g.start == *start + *count * *width
                    }) =>
                {
                    *count += 1;
                    true
                }
                _ => false,
            };
            if !extended {
                runs.push(match s {
                    Storage::Native(cell) => Run::Native {
                        first: v,
                        count: 1,
                        cell: *cell,
                    },
                    Storage::Foreign(coordinates) => match s.prime_group() {
                        Some(g) => Run::Prime {
                            first: v,
                            count: 1,
                            start: g.start,
                            width: g.width,
                        },
                        None => Run::Coordinates {
                            value: v,
                            coordinates: coordinates.clone(),
                        },
                    },
                });
            }
        }
        runs
    }
}
