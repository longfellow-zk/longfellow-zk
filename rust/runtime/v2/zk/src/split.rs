// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Storage splits: claims over values stored outside a participant's own
//! commitment.
//!
//! A participant's value vector is `[private inputs | pads]`. Its storage
//! map assigns each value a native cell or foreign bits in the binary
//! commitment.
//!
//! - All native: the ordinary circuit reduction applies.
//! - Mixed: the participant commits `[native private inputs | pads | R]`, and every pad is native.
//!   The layer rows read only pads, so they go to this field's Polygero participant unchanged. The
//!   input equation `<w, v> = t` is split with a fresh nonzero challenge `eta` and one masked
//!   message `mu = eta*<w_F, v_F> + R` into:
//!   - a native row `eta*<w_N, v_N> - R + mu - eta*t = 0`, beside the layer rows;
//!   - a foreign claim `<eta*w_F, v_F> + R_bits = mu (mod p)` for the adapter.
//!
//!   R is uniform and used only here, so `mu` hides `<w_F, v_F>`.
//! - Pure foreign: the participant commits nothing. Fresh weights batch every layer row and the
//!   input equation into one foreign claim with a public target (`batching`).
use super::{
    batching::LinearClaim,
    joint::CircuitParticipant,
    storage::{Group, ModularClaim, Storage, StorageMap},
};
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{blas, PackingField, ZkField},
        v2::{
            polygero::{LinearStatement, PolygeroLinearTerm},
            proto::Digest,
            sumcheck::symbolic::Constraints,
            transcript::TranscriptRef,
        },
    },
};

#[path = "split/transcript.rs"]
pub mod transcript;

/// Storage of a participant whose values are not all native.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Split {
    pub(crate) map: StorageMap,
    /// Bits of R in the binary commitment; absent for pure foreign storage.
    pub(crate) mask: Option<Group>,
    /// Physical cell of R: after every native value.
    pub(crate) mask_cell: usize,
}
impl Split {
    /// Physical cell of the value at `index`, which must be native. Native
    /// values are committed in value order, so this is the map's own cell.
    fn native_cell(&self, index: usize) -> Result<usize, String> {
        match self.map.entries().get(index) {
            Some(Storage::Native(cell)) => Ok(*cell),
            _ => Err("native row reads a foreign value".into()),
        }
    }
}

/// A split participant's frontend claim over `[private inputs | pads]`.
pub struct SplitClaim<E> {
    /// Mixed storage: the layer rows on this field's native cells, unbatched.
    /// Pure foreign storage: empty, since `claim` already batches them.
    rows: (Vec<PolygeroLinearTerm<E>>, Vec<E>),
    /// Mixed storage: the input equation. Pure foreign storage: every row.
    pub claim: LinearClaim<E>,
}

impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    pub(super) fn split(&self) -> Result<&Split, String> {
        self.storage
            .as_ref()
            .ok_or_else(|| "participant has only native storage".into())
    }
    /// Reduce the frontend's constraints to the claim its storage discharges.
    /// Both roles call this after the frontend's last message.
    pub(super) fn split_claim(
        &self,
        circuit: &Circuit<F>,
        public: &[F::E],
        constraints: Constraints<F::E>,
        t: &mut TranscriptRef<'_>,
        f: &F,
    ) -> Result<SplitClaim<F::E>, String> {
        let split = self.split()?;
        if split.mask.is_none() {
            let claim = super::batching::batch(circuit, public, constraints, t, f)?;
            return Ok(SplitClaim {
                rows: (Vec::new(), Vec::new()),
                claim,
            });
        }
        let private = self.inputs.committed();
        let pads = self.geometry.sc_geom.pad_layout(private);
        if public.len() != circuit.raw.npublic_input
            || constraints.input_weights.len() != circuit.raw.ninput
            || constraints.layers.len() != pads.layers.len()
        {
            return Err("split frontend constraint shape".into());
        }
        let (mut a, b) = super::constraint_compiler::compile_layers(&constraints, &pads)?;
        for term in &mut a {
            term.w = split.native_cell(term.w)?;
        }
        // Input equation: <w_in, inputs> = constant + sum k*pad.
        let mut weights = vec![f.zero(); split.map.entries().len()];
        weights[..private].clone_from_slice(&constraints.input_weights[public.len()..]);
        for (pad, k) in constraints.input_claim.terms {
            let j = super::constraint_compiler::pad_coordinate(pad, &pads)?;
            f.sub(&mut weights[j], &k);
        }
        let target = f.subf(
            &constraints.input_claim.constant,
            &blas::dot(&constraints.input_weights[..public.len()], public, f),
        );
        Ok(SplitClaim {
            rows: (a, b),
            claim: LinearClaim { weights, target },
        })
    }
    fn check_claim(&self, claim: &SplitClaim<F::E>, eta: &F::E, f: &F) -> Result<&Split, String> {
        let split = self.split()?;
        if split.mask.is_none()
            || f.is_zero(eta)
            || claim.claim.weights.len() != split.map.entries().len()
        {
            return Err("split claim shape, storage or zero challenge".into());
        }
        Ok(split)
    }
    /// This field's statement: the layer rows, then the native row
    /// `eta*<w_N, v_N> - R + mu - eta*t = 0`.
    pub fn split_statement(
        &self,
        claim: &SplitClaim<F::E>,
        eta: &F::E,
        mu: &F::E,
        f: &F,
    ) -> Result<LinearStatement<F::E>, String> {
        let split = self.check_claim(claim, eta, f)?;
        let (mut a, mut b) = claim.rows.clone();
        let c = b.len();
        for (i, (s, w)) in split
            .map
            .entries()
            .iter()
            .zip(&claim.claim.weights)
            .enumerate()
        {
            if matches!(s, Storage::Native(_)) {
                a.push(PolygeroLinearTerm {
                    c,
                    w: split.native_cell(i)?,
                    k: f.mulf(eta, w),
                });
            }
        }
        a.push(PolygeroLinearTerm {
            c,
            w: split.mask_cell,
            k: f.mone(),
        });
        b.push(f.subf(mu, &f.mulf(eta, &claim.claim.target)));
        Ok(LinearStatement {
            a,
            b,
            // The frontend and split messages already precede joint batching
            // on the shared transcript. This identifier names the source only.
            digest: Digest { data: self.id },
        })
    }
    /// Foreign claim `<eta*w_F, v_F> + R_bits = mu (mod p)` for the adapter.
    pub fn foreign_claim(
        &self,
        claim: &SplitClaim<F::E>,
        eta: &F::E,
        mu: &F::E,
        f: &F,
    ) -> Result<ModularClaim<F::E>, String> {
        let split = self.check_claim(claim, eta, f)?;
        let mask = split.mask.ok_or("pure foreign storage has no split mask")?;
        let mut terms: Vec<_> = split
            .map
            .entries()
            .iter()
            .zip(&claim.claim.weights)
            .filter_map(|(s, w)| match s {
                Storage::Foreign(g) => Some((*g, f.mulf(eta, w))),
                Storage::Native(_) => None,
            })
            .collect();
        terms.push((mask, f.one()));
        Ok(ModularClaim {
            terms,
            target: mu.clone(),
        })
    }
    /// The whole claim of a pure-foreign participant, whose target is public.
    pub fn pure_claim(&self, claim: &SplitClaim<F::E>) -> Result<ModularClaim<F::E>, String> {
        let split = self.split()?;
        if split.mask.is_some() || claim.claim.weights.len() != split.map.entries().len() {
            return Err("pure claim needs pure foreign storage covering the claim".into());
        }
        let terms = split
            .map
            .entries()
            .iter()
            .zip(&claim.claim.weights)
            .map(|(s, w)| match s {
                Storage::Foreign(g) => Ok((*g, w.clone())),
                Storage::Native(_) => Err("pure claim reads a native value".to_string()),
            })
            .collect::<Result<_, _>>()?;
        Ok(ModularClaim {
            terms,
            target: claim.claim.target.clone(),
        })
    }
}

/// A split participant's reduction, before its split challenge.
pub struct PendingSplit<E> {
    pub claim: SplitClaim<E>,
    pub(crate) values: Vec<E>,
    pub(crate) mask: Option<E>,
}
impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    /// The split message `mu = eta*<w_F, v_F> + R`.
    pub fn split_message(
        &self,
        pending: &PendingSplit<F::E>,
        eta: &F::E,
        f: &F,
    ) -> Result<F::E, String> {
        let split = self.check_claim(&pending.claim, eta, f)?;
        let mask = pending
            .mask
            .as_ref()
            .ok_or("pure foreign storage has no split mask")?;
        let mut sum = f.zero();
        for ((s, w), v) in split
            .map
            .entries()
            .iter()
            .zip(&pending.claim.claim.weights)
            .zip(&pending.values)
        {
            if matches!(s, Storage::Foreign(_)) {
                f.add(&mut sum, &f.mulf(w, v));
            }
        }
        Ok(f.addf(&f.mulf(eta, &sum), mask))
    }
    /// Values of the foreign claim's terms, in term order, ending with R.
    pub fn foreign_values(&self, pending: &PendingSplit<F::E>) -> Result<Vec<F::E>, String> {
        let split = self.split()?;
        let mut out: Vec<_> = split
            .map
            .entries()
            .iter()
            .zip(&pending.values)
            .filter(|(s, _)| matches!(s, Storage::Foreign(_)))
            .map(|(_, v)| v.clone())
            .collect();
        out.extend(pending.mask.clone());
        Ok(out)
    }
}

/// Validate a storage map for `circuit` and derive its split layout.
pub(crate) fn layout(
    map: StorageMap,
    mask: Option<Group>,
    private: usize,
    values: usize,
) -> Result<Split, String> {
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
    Ok(Split {
        map,
        mask,
        mask_cell,
    })
}

/// Number of values `[private inputs | pads]` of a split participant for
/// `circuit`; a storage map must cover exactly this many.
pub fn value_count<F: crate::core::algebra::SerializableField>(
    circuit: &Circuit<F>,
) -> Result<usize, String> {
    let private = circuit
        .raw
        .ninput
        .checked_sub(circuit.raw.npublic_input)
        .ok_or("public prefix")?;
    private
        .checked_add(crate::runtime::v2::sumcheck::circuit_geometry(&[circuit])?.pad_count()?)
        .ok_or_else(|| "split value count overflow".into())
}

#[cfg(test)]
#[path = "../tests/split.rs"]
mod tests;
