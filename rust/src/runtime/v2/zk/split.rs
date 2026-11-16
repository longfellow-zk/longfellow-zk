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
//! - Pure foreign: the participant commits nothing. Fresh weights, drawn and used by the pure split
//!   step (`SplitClaim::batch`), batch every layer row and the input equation into one foreign
//!   claim with a public target (`batching`).
use super::{
    batching::LinearClaim,
    joint::{CircuitParticipant, FrontendPart},
    storage::{ModularClaim, Split, Storage},
};
use crate::{
    core::{
        algebra::{BareField, SerializableField},
        proto::v2::Circuit,
    },
    runtime::{
        algebra::{blas, packing::PackingField, ZkField},
        v2::{
            polygero::{LinearStatement, PolygeroLinearTerm},
            sumcheck::{circuit_geometry, symbolic::Constraints},
            transcript::{Bound, Challenge, SessionStamp},
        },
    },
};

pub mod transcript;
use transcript::Eta;

/// A split participant's frontend claim over `[private inputs | pads]`.
pub(crate) struct SplitClaim<E> {
    /// The layer rows, unbatched: on this field's native cells with mixed
    /// storage, on its values with pure foreign storage.
    rows: (Vec<PolygeroLinearTerm<E>>, Vec<E>),
    /// The input equation `<w, v> = t` over the values.
    pub(crate) claim: LinearClaim<E>,
}

impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    pub(super) fn split(&self) -> Result<&Split, String> {
        self.storage
            .as_ref()
            .ok_or_else(|| "participant has only native storage".into())
    }
    /// Reduce the frontend's constraints to the claim its storage discharges.
    /// Both roles call this after the frontend's last message, on the
    /// frontend's own part: its circuit and public inputs.
    pub(super) fn split_claim(
        t: &mut Bound<'_, FrontendPart<'_, W, F>>,
        constraints: Constraints<F::E>,
        f: &F,
    ) -> Result<SplitClaim<F::E>, String> {
        let part = t.part();
        let (p, circuit, public) = (part.participant, part.circuits[0], &part.public[..]);
        let split = p.split()?;
        if split.mask.is_none() {
            // Pure foreign storage: `batch` draws the row weights next and
            // combines these rows with them.
            let (rows, claim) = super::batching::rows(circuit, public, constraints, f)?;
            return Ok(SplitClaim { rows, claim });
        }
        let private = p.inputs.committed();
        let pads = p.geometry.sumcheck().pad_layout(private);
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
    /// This field's statement on `session`: the layer rows, then the native
    /// row `eta*<w_N, v_N> - R + mu - eta*t = 0`.
    /// It consumes the claim: its layer rows become the statement's rows.
    fn split_statement(
        &self,
        claim: SplitClaim<F::E>,
        eta: &F::E,
        mu: &F::E,
        session: SessionStamp,
        f: &F,
    ) -> Result<LinearStatement<F::E>, String> {
        let split = self.check_claim(&claim, eta, f)?;
        let SplitClaim {
            rows: (mut a, mut b),
            claim,
        } = claim;
        let c = b.len();
        for (i, (s, w)) in split.map.entries().iter().zip(&claim.weights).enumerate() {
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
        b.push(f.subf(mu, &f.mulf(eta, &claim.target)));
        Ok(LinearStatement { a, b, session })
    }
    /// Foreign claim `<eta*w_F, v_F> + R_bits = mu (mod p)` for the adapter.
    fn foreign_claim(
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
    /// The whole claim of a pure-foreign participant, whose target is public:
    /// the batched claim `claim` over its foreign values.
    #[cfg(test)]
    fn pure_claim(&self, claim: LinearClaim<F::E>) -> Result<ModularClaim<F::E>, String> {
        let split = self.split()?;
        if split.mask.is_some() || claim.weights.len() != split.map.entries().len() {
            return Err("pure claim needs pure foreign storage covering the claim".into());
        }
        let terms = split
            .map
            .entries()
            .iter()
            .zip(&claim.weights)
            .map(|(s, w)| match s {
                Storage::Foreign(g) => Ok((*g, w.clone())),
                Storage::Native(_) => Err("pure claim reads a native value".to_string()),
            })
            .collect::<Result<_, _>>()?;
        Ok(ModularClaim {
            terms,
            target: claim.target,
        })
    }
}
#[cfg(test)]
impl<E> SplitClaim<E> {
    /// The number of pure-foreign row weights: one per layer row, one for the
    /// input equation.
    fn row_weight_count(&self) -> usize {
        self.rows.1.len() + 1
    }
    /// Pure foreign storage only: draw the row weights rho_0..rho_L at the
    /// current boundary, right after the frontend's last message, and batch
    /// every row and the input equation with them into one foreign claim
    /// with a public target. The weights are internal to this step
    /// (transcript I8). Mixed storage takes `eta` instead (`open`,
    /// `receive`).
    pub(crate) fn batch<const W: usize, F>(
        self,
        t: &mut Bound<'_, FrontendPart<'_, W, F>>,
        f: &F,
    ) -> Result<ModularClaim<E>, String>
    where
        F: ZkField<W> + PackingField + BareField<E = E>,
    {
        let p = t.part().participant;
        if p.split()?.mask.is_some() {
            return Err("row weights batch only pure foreign storage".into());
        }
        let weights = transcript::row_weights(&mut t.transcript(), self.row_weight_count(), f);
        let claim = super::batching::batch((self.rows, self.claim), &weights, f)?;
        p.pure_claim(claim)
    }
}

/// A split participant's reduction, before its split challenge. Only the
/// prover holds one: it carries the private values and R.
#[cfg(any(test, feature = "prover"))]
pub(crate) struct PendingSplit<E> {
    pub(crate) claim: SplitClaim<E>,
    pub(crate) values: Vec<E>,
    pub(crate) mask: Option<E>,
}
/// The two outputs of a mixed split: this field's statement (the layer rows
/// and the native row) and the foreign claim for the adapter.
#[must_use]
pub(crate) struct SplitOutput<E> {
    pub(crate) statement: LinearStatement<E>,
    pub(crate) foreign: ModularClaim<E>,
}

#[cfg(any(test, feature = "prover"))]
impl<E> PendingSplit<E> {
    /// Accept `eta`, send the split message `mu` on the frontend's session,
    /// and return `mu` with both outputs, all built from this `eta` and `mu`.
    pub(crate) fn open<const W: usize, F>(
        self,
        t: &mut Bound<'_, FrontendPart<'_, W, F>>,
        eta: Challenge<Eta<E>>,
        f: &F,
    ) -> Result<(E, SplitOutput<E>), String>
    where
        F: ZkField<W> + PackingField + BareField<E = E>,
    {
        let Eta(scale) = t.accept(eta).map_err(|e| e.to_string())?;
        let p = t.part().participant;
        let mu = p.split_message(&self, &scale, f)?;
        transcript::send_mu(&mut t.transcript(), &mu, f);
        let foreign = p.foreign_claim(&self.claim, &scale, &mu, f)?;
        let statement = p.split_statement(self.claim, &scale, &mu, t.session(), f)?;
        Ok((mu, SplitOutput { statement, foreign }))
    }
}
#[cfg(any(test, feature = "verifier"))]
impl<E> SplitClaim<E> {
    /// Accept `eta`, absorb the proof's split message `mu` on the frontend's
    /// session, and return both outputs, built from this `eta` and `mu`.
    pub(crate) fn receive<const W: usize, F>(
        self,
        t: &mut Bound<'_, FrontendPart<'_, W, F>>,
        eta: Challenge<Eta<E>>,
        mu: &E,
        f: &F,
    ) -> Result<SplitOutput<E>, String>
    where
        F: ZkField<W> + PackingField + BareField<E = E>,
    {
        let Eta(scale) = t.accept(eta).map_err(|e| e.to_string())?;
        let p = t.part().participant;
        transcript::send_mu(&mut t.transcript(), mu, f);
        let foreign = p.foreign_claim(&self, &scale, mu, f)?;
        let statement = p.split_statement(self, &scale, mu, t.session(), f)?;
        Ok(SplitOutput { statement, foreign })
    }
}
impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    /// The split message `mu = eta*<w_F, v_F> + R`.
    #[cfg(any(test, feature = "prover"))]
    fn split_message(
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
    #[cfg(any(test, feature = "prover"))]
    pub(crate) fn foreign_values(&self, pending: &PendingSplit<F::E>) -> Result<Vec<F::E>, String> {
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

/// Number of values `[private inputs | pads]` of a split participant for
/// `circuit`; a storage map must cover exactly this many.
pub fn value_count<F: SerializableField>(circuit: &Circuit<F>) -> Result<usize, String> {
    let private = circuit
        .raw
        .ninput
        .checked_sub(circuit.raw.npublic_input)
        .ok_or("public prefix")?;
    private
        .checked_add(circuit_geometry(&[circuit])?.pad_count())
        .ok_or_else(|| "split value count overflow".into())
}

#[cfg(test)]
mod tests;
