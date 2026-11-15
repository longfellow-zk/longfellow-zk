// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Coordinate storage: extension-field values held as base-field coordinates
//! in bit groups of the binary commitment.
//!
//! `storage::Storage::Foreign` holds one prime-field value as one bit group.
//! A frontend over an extension field E of degree d over its prime field
//! instead stores each value `x = sum_c x_c e_c` as up to d groups, one per
//! stored coordinate `x_c`. Unlisted coordinates are zero, so a value may
//! store only its base-field part. Explicit affine metadata may instead store
//! `x_c = scale * b_c + offset` with an unsigned bounded b_c; both roles bind
//! these parameters before commitment.
//!
//! This layers on pure-foreign storage without changing `Storage`:
//!
//! - `CoordinateMap::storage_map` builds the pure-foreign `StorageMap` which records each value's
//!   whole bit span. A value's stored coordinates must therefore be contiguous, in increasing
//!   coordinate order. Only this map decodes a span into coordinates: `pure_claim` would read a
//!   span as one integer and must not be used for such a participant.
//! - `CoordinateMap::modular_claim` expands the participant's batched claim `<w, v> = t` into one
//!   term per stored coordinate: coordinate `c` of value `v` has weight `w_v e_c`. Each coordinate
//!   of that E-valued claim is a claim modulo the prime over the same groups. Affine coordinates
//!   multiply this weight by their scale and subtract the weighted offset from the target;
//!   `pure_claim` cannot do this conversion.
//! - `CoordinateMap::write_layout` binds the map in the initial statement, as runs, before the
//!   shared root. The frontend's circuit message binds the circuit identity.
use std::collections::{btree_map::Entry, BTreeMap};

use super::{
    batching::LinearClaim,
    storage::{Group, ModularClaim, StorageMap},
};
use crate::{core::algebra::AlgebraicField, runtime::v2::transcript::Header};
mod affine;
pub(crate) use affine::AffineEncoding;
mod transcript;

/// One stored base-field coordinate of a foreign value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Coordinate {
    pub index: usize,
    pub group: Group,
}

/// The stored coordinates of every value `[private inputs | pads]` of a
/// pure-foreign frontend over an extension of degree `degree`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CoordinateMap {
    degree: usize,
    values: Vec<Vec<Coordinate>>,
    affine: Option<Vec<AffineEncoding>>,
}

/// A maximal run of consecutive values with the same stored coordinates and
/// equal widths, whose groups are consecutive: coordinate `j` of value
/// `first + i` is the group at `start + (i * coordinates.len() + j) * width`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CoordinateRun {
    pub first: usize,
    pub count: usize,
    pub coordinates: Vec<usize>,
    pub start: usize,
    pub width: usize,
}

impl CoordinateMap {
    /// `stored` lists (value, coordinate, group) triples. Every value must
    /// store at least one coordinate, and a value's coordinates must be listed
    /// in increasing order with contiguous groups.
    pub(crate) fn new(
        values: usize,
        degree: usize,
        stored: &[(usize, usize, Group)],
    ) -> Result<Self, String> {
        if degree == 0 {
            return Err("coordinate extension has zero degree".into());
        }
        let mut out: Vec<Vec<Coordinate>> = vec![Vec::new(); values];
        for &(v, index, group) in stored {
            if index >= degree || group.width() == 0 {
                return Err("coordinate outside the extension or empty group".into());
            }
            let slot = out.get_mut(v).ok_or("coordinate value index")?;
            if let Some(last) = slot.last() {
                if last.index >= index || last.group.end() != group.start() {
                    return Err("coordinates must be increasing and contiguous".into());
                }
            }
            slot.push(Coordinate { index, group });
        }
        if out.iter().any(Vec::is_empty) {
            return Err("coordinate storage leaves a value unstored".into());
        }
        Ok(Self {
            degree,
            values: out,
            affine: None,
        })
    }
    /// Explicit affine encodings in the same order as the stored coordinates.
    /// Identity-only maps retain the original representation and transcript.
    #[cfg(any(test, feature = "mdoc"))]
    pub(crate) fn new_affine(
        values: usize,
        degree: usize,
        stored: &[(usize, usize, Group, AffineEncoding)],
    ) -> Result<Self, String> {
        let coordinates: Vec<_> = stored.iter().map(|&(v, c, g, _)| (v, c, g)).collect();
        let mut map = Self::new(values, degree, &coordinates)?;
        if stored
            .iter()
            .all(|(_, _, _, encoding)| *encoding == AffineEncoding::IDENTITY)
        {
            return Ok(map);
        }
        let mut by_value = vec![Vec::new(); values];
        for &(value, _, _, encoding) in stored {
            AffineEncoding::new(encoding.scale, encoding.offset)?;
            by_value[value].push(encoding);
        }
        let encodings: Vec<_> = by_value.into_iter().flatten().collect();
        if encodings.iter().any(|&e| e != AffineEncoding::IDENTITY) {
            map.affine = Some(encodings);
        }
        Ok(map)
    }

    /// Number of stored coordinates: the terms of the expanded claim.
    pub(crate) fn terms(&self) -> usize {
        self.values.iter().map(Vec::len).sum()
    }
    /// The groups of the expanded claim, in term order.
    pub(crate) fn groups(&self) -> impl Iterator<Item = Group> + '_ {
        self.values.iter().flatten().map(|c| c.group)
    }
    /// Each value's checked whole span, for `PureSplit` storage.
    /// Pass no mask: every frontend value is foreign.
    pub(crate) fn storage_map(&self) -> Result<StorageMap, String> {
        let spans: Vec<_> = self
            .values
            .iter()
            .enumerate()
            .map(|(v, c)| {
                let (first, last) = (c[0].group, c[c.len() - 1].group);
                (
                    v,
                    Group::new(first.start(), last.end() - first.start())
                        .expect("contiguous coordinate span"),
                )
            })
            .collect();
        StorageMap::new(self.values.len(), &spans)
    }
    /// The map as maximal runs, in value order. Equal maps give equal runs.
    pub(crate) fn runs(&self) -> Vec<CoordinateRun> {
        let mut runs: Vec<CoordinateRun> = Vec::new();
        for (v, c) in self.values.iter().enumerate() {
            let width = c[0].group.width();
            let uniform = c.iter().all(|x| x.group.width() == width);
            if let Some(run) = runs.last_mut() {
                let k = run.coordinates.len();
                if uniform
                    && run.first + run.count == v
                    && run.width == width
                    && c.len() == k
                    && c.iter().zip(&run.coordinates).all(|(x, &i)| x.index == i)
                    && c[0].group.start() == run.start + run.count * k * width
                {
                    run.count += 1;
                    continue;
                }
            }
            if uniform {
                runs.push(CoordinateRun {
                    first: v,
                    count: 1,
                    coordinates: c.iter().map(|x| x.index).collect(),
                    start: c[0].group.start(),
                    width,
                });
            } else {
                // Mixed widths within a value: one run per coordinate.
                runs.extend(c.iter().map(|x| CoordinateRun {
                    first: v,
                    count: 1,
                    coordinates: vec![x.index],
                    start: x.group.start(),
                    width: x.group.width(),
                }));
            }
        }
        runs
    }
    /// Write the map's extension degree and runs in the initial statement.
    /// The frontend writes its circuit identity separately. These are setup
    /// constants fixed by the trusted circuits, independent of the proof.
    pub(crate) fn write_layout(&self, h: &mut Header<'_>) {
        let runs = self.runs();
        // One absorption of fixed-width words; every list is length-prefixed.
        let mut words = vec![self.degree, self.values.len(), runs.len()];
        for run in runs {
            words.extend([run.first, run.count, run.start, run.width]);
            words.push(run.coordinates.len());
            words.extend(run.coordinates);
        }
        transcript::write_layout(h, &words);
        if let Some(encodings) = &self.affine {
            transcript::write_affine(h, encodings);
        }
    }
    /// Expand a pure-foreign participant's claim `<w, v> = t` into one term
    /// `(group, w_v * basis[c])` per stored coordinate `c` of each value `v`,
    /// in term order. `basis[c]` is the extension's basis element `e_c`.
    pub(crate) fn modular_claim<F: AlgebraicField>(
        &self,
        claim: &LinearClaim<F::E>,
        basis: &[F::E],
        f: &F,
    ) -> Result<ModularClaim<F::E>, String> {
        if claim.weights.len() != self.values.len() || basis.len() != self.degree {
            return Err("coordinate claim shape".into());
        }
        let one = f.one();
        let mut terms = Vec::with_capacity(self.terms());
        let mut target = claim.target.clone();
        let mut coefficients = BTreeMap::new();
        for (c, w) in self.values.iter().zip(&claim.weights) {
            for x in c {
                let e = &basis[x.index];
                let mut k = if *e == one { w.clone() } else { f.mulf(w, e) };
                if let Some(encodings) = &self.affine {
                    let encoding = encodings[terms.len()];
                    if encoding != AffineEncoding::IDENTITY {
                        let (scale, offset) = match coefficients.entry(encoding) {
                            Entry::Occupied(entry) => entry.into_mut(),
                            Entry::Vacant(entry) => entry.insert(encoding.coefficients(f)?),
                        };
                        f.sub(&mut target, &f.mulf(&k, offset));
                        f.mul(&mut k, scale);
                    }
                }
                terms.push((x.group, k));
            }
        }
        Ok(ModularClaim { terms, target })
    }
}

cfg_prover! {mod prover;}

#[cfg(test)]
mod tests;
