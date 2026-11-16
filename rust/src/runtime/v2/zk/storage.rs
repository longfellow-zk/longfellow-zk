// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Where a frontend's values live, and untyped positions in the binary inputs.
//!
//! A frontend value is either a cell of its own field's commitment or a group
//! of bits in the binary commitment. Bit groups are absolute indices into the
//! binary participant's shared input array, least significant bit first. The
//! reserved suffix after the format circuit's inputs, and the typed words in
//! it, belong to the composition (`foreign::reserved`).

/// An untyped bit group: `width` consecutive binary inputs from `start`.
///
/// Constructors check that `start + width` fits, so `end` never overflows and
/// writers need no per-write range arithmetic. Its fields are private, so
/// only the constructors build one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Group {
    start: usize,
    width: usize,
}
impl Group {
    /// The empty group at position 0.
    pub(crate) const EMPTY: Self = Self { start: 0, width: 0 };
    /// `width` bits from `start`; rejects a group whose end overflows.
    #[cfg_attr(not(any(test, feature = "mdoc")), allow(dead_code))]
    pub(crate) fn new(start: usize, width: usize) -> Result<Self, String> {
        start.checked_add(width).ok_or("bit group end overflows")?;
        Ok(Self { start, width })
    }
    pub(crate) fn start(&self) -> usize {
        self.start
    }
    pub(crate) fn width(&self) -> usize {
        self.width
    }
    pub(crate) fn end(&self) -> usize {
        self.start + self.width
    }
    pub(crate) fn bit(&self, j: usize) -> usize {
        assert!(j < self.width);
        self.start + j
    }
}

/// Where one value of a foreign-capable frontend lives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Storage {
    /// Cell index in this frontend's own commitment.
    Native(usize),
    /// The bits of a prime-field value in the binary commitment.
    Foreign(Group),
}

/// Storage of a frontend's value vector `[private inputs | sumcheck pads]`.
/// Native cells are numbered densely in vector order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct StorageMap {
    entries: Vec<Storage>,
    native: usize,
}
impl StorageMap {
    /// Store values listed in `foreign` (value index, group) as bits in the
    /// binary commitment; all others natively.
    #[cfg_attr(not(any(test, feature = "mdoc")), allow(dead_code))]
    pub(crate) fn new(values: usize, foreign: &[(usize, Group)]) -> Result<Self, String> {
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
    pub(crate) fn entries(&self) -> &[Storage] {
        &self.entries
    }
    pub(crate) fn native_cells(&self) -> usize {
        self.native
    }
    pub(crate) fn is_pure_foreign(&self) -> bool {
        self.native == 0
    }
}

/// A maximal run of consecutive values stored alike. Runs are the storage
/// map's layout parameters as they are bound to the transcript.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Run {
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
    pub(crate) fn runs(&self) -> Vec<Run> {
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
#[must_use = "The modular claim must be discharged by the cross-field adapter."]
pub(crate) struct ModularClaim<E> {
    pub(crate) terms: Vec<(Group, E)>,
    pub(crate) target: E,
}

/// Storage of a participant whose values are not all native.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Split {
    pub(crate) map: StorageMap,
    /// Bits of R in the binary commitment; absent for pure foreign storage.
    pub(crate) mask: Option<Group>,
    /// Physical cell of R: after every native value.
    pub(crate) mask_cell: usize,
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl Split {
    /// Validate a storage map over `values` values, the first `private` of
    /// them private inputs and the rest pads, and derive its split layout.
    pub(crate) fn new(
        map: StorageMap,
        mask: Option<Group>,
        private: usize,
        values: usize,
    ) -> Result<Self, String> {
        if map.entries().len() != values {
            return Err("storage map does not cover the participant's values".into());
        }
        if !map
            .entries()
            .iter()
            .any(|s| matches!(s, Storage::Foreign(_)))
        {
            return Err("storage map has no foreign value; use native storage".into());
        }
        let pure = map.is_pure_foreign();
        if pure != mask.is_none() {
            return Err("a mask is required exactly when some values are native".into());
        }
        if !pure
            && map.entries()[private..]
                .iter()
                .any(|s| !matches!(s, Storage::Native(_)))
        {
            return Err("mixed storage keeps every pad native".into());
        }
        let mask_cell = map.native_cells();
        Ok(Self {
            map,
            mask,
            mask_cell,
        })
    }
    /// Physical cell of the value at `index`, which must be native. Native
    /// values are committed in value order, so this is the map's own cell.
    pub(crate) fn native_cell(&self, index: usize) -> Result<usize, String> {
        match self.map.entries().get(index) {
            Some(Storage::Native(cell)) => Ok(*cell),
            _ => Err("native row reads a foreign value".into()),
        }
    }
}

#[cfg(test)]
mod tests;
