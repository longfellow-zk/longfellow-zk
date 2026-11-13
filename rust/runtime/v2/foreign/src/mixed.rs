// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Mixed storage: a frontend whose values are partly native, partly foreign.
//!
//! Its own commitment holds `[native private inputs | mask R | native pads]`,
//! each part in vector order; the binary commitment holds the foreign values and the bits of R. The
//! batched claim `<w, v> = t` is split with a fresh nonzero challenge `eta` and one
//! masked message `mu`:
//!
//! - native row: `eta * <w_N, v_N> - R + mu - eta * t = 0`, authenticated by this field's Polygero
//!   participant;
//! - foreign claim: `<eta * w_F, v_F> + R_bits = mu (mod p)`, handed to the adapter. R is uniform
//!   and used only here, so `mu` hides `<w_F, v_F>`.
use super::{
    adapter::ModularClaim,
    frontend::{self, LinearClaim},
    storage::{Group, Storage, StorageMap},
};
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{EvaluationDomain, PackingField, ZkField},
        v2::{
            polygero::{LinearStatement, PolygeroConfig, PolygeroLinearTerm},
            proto::{sumcheck::SumcheckProof, Digest},
            transcript::TranscriptRef,
            zk::{joint::SelectedField, CircuitGeometry, ZkContext},
        },
    },
};

pub struct MixedParticipant<const W: usize, F: ZkField<W> + PackingField> {
    geometry: CircuitGeometry,
    storage: StorageMap,
    mask: Group,
    cells: usize,
    /// Physical cell of R: right after the native private inputs.
    mask_cell: usize,
    id: [u8; 32],
    #[cfg_attr(not(any(test, feature = "prover")), allow(dead_code))]
    config: PolygeroConfig,
    _f: std::marker::PhantomData<F>,
}
impl<const W: usize, F: ZkField<W> + PackingField> MixedParticipant<W, F> {
    /// `storage` covers the frontend's value vector; `mask` holds the bits of
    /// R in the binary commitment (normally in its reserved suffix).
    pub fn new<D: EvaluationDomain<W, F>>(
        circuit: &Circuit<F>,
        storage: StorageMap,
        mask: Group,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, String> {
        if ctx.field().is_binary() {
            return Err("mixed storage requires a non-binary frontend field".into());
        }
        if storage.entries().len() != frontend::value_count(circuit)? {
            return Err("storage map does not cover the frontend values".into());
        }
        if storage
            .entries()
            .iter()
            .any(|s| matches!(s, Storage::Foreign(_)) && s.prime_group().is_none())
        {
            return Err("mixed storage expects prime-field values".into());
        }
        let cells = storage
            .native_cells()
            .checked_add(1)
            .ok_or("mixed layout overflow")?;
        let private = circuit.raw.ninput - circuit.raw.npublic_input;
        let mask_cell = storage.entries()[..private]
            .iter()
            .filter(|s| matches!(s, Storage::Native(_)))
            .count();
        let selected = SelectedField::new(cells, config, ctx.domain, ctx.field().packing_id())?;
        Ok(Self {
            geometry: CircuitGeometry {
                sc_geom: crate::runtime::v2::sumcheck::circuit_geometry(&[circuit])?,
                com_geom: selected.geometry(),
                packing_degree: 1,
            },
            storage,
            mask,
            cells,
            mask_cell,
            id: circuit.id,
            config,
            _f: std::marker::PhantomData,
        })
    }
    pub fn geometry(&self) -> CircuitGeometry {
        self.geometry.clone()
    }
    pub fn participant<'a, D: EvaluationDomain<W, F>>(
        &'a self,
        ctx: &ZkContext<'a, W, F, D>,
    ) -> Result<SelectedField<'a, W, F, D, &'a Self>, String> {
        Ok(SelectedField::new(
            self.cells,
            self.config,
            ctx.domain,
            ctx.field().packing_id(),
        )?
        .with_layout(self))
    }
    /// Physical cell of the native value numbered `cell` by the storage map.
    fn physical(&self, cell: usize) -> usize {
        if cell < self.mask_cell {
            cell
        } else {
            cell + 1
        }
    }
    fn check(&self, circuit: &Circuit<F>, claim: Option<&LinearClaim<F::E>>) -> Result<(), String> {
        if circuit.id != self.id
            || claim.is_some_and(|c| c.weights.len() != self.storage.entries().len())
        {
            return Err("mixed frontend statement mismatch".into());
        }
        Ok(())
    }

    /// Native statement `eta*<w_N, v_N> - R + mu - eta*t = 0` on this field's cells.
    pub fn native_statement(
        &self,
        claim: &LinearClaim<F::E>,
        eta: &F::E,
        mu: &F::E,
        f: &F,
    ) -> Result<LinearStatement<F::E>, String> {
        if f.is_zero(eta) || claim.weights.len() != self.storage.entries().len() {
            return Err("mixed claim shape or zero challenge".into());
        }
        let mut a = Vec::new();
        for (s, w) in self.storage.entries().iter().zip(&claim.weights) {
            if let Storage::Native(cell) = s {
                a.push(PolygeroLinearTerm {
                    c: 0,
                    w: self.physical(*cell),
                    k: f.mulf(eta, w),
                });
            }
        }
        a.push(PolygeroLinearTerm {
            c: 0,
            w: self.mask_cell,
            k: f.mone(),
        });
        Ok(LinearStatement {
            a,
            b: vec![f.subf(mu, &f.mulf(eta, &claim.target))],
            // The frontend and split messages already precede joint batching
            // on the shared transcript. This identifier names the source only.
            digest: Digest { data: self.id },
        })
    }
    /// Foreign claim `<eta*w_F, v_F> + R_bits = mu (mod p)` for the adapter.
    pub fn foreign_claim(
        &self,
        claim: &LinearClaim<F::E>,
        eta: &F::E,
        mu: &F::E,
        f: &F,
    ) -> Result<ModularClaim<F::E>, String> {
        if f.is_zero(eta) || claim.weights.len() != self.storage.entries().len() {
            return Err("mixed claim shape or zero challenge".into());
        }
        let mut terms: Vec<_> = self
            .storage
            .entries()
            .iter()
            .zip(&claim.weights)
            .filter_map(|(s, w)| match s {
                Storage::Foreign(_) => s.prime_group().map(|g| (g, f.mulf(eta, w))),
                Storage::Native(_) => None,
            })
            .collect();
        terms.push((self.mask, f.one()));
        Ok(ModularClaim {
            terms,
            target: mu.clone(),
        })
    }
}

cfg_prover! {
use crate::runtime::random::RandomEngine;
/// Prover state between commitment and reduction.
pub struct MixedState<const W: usize, F: ZkField<W>> {
    prepared: frontend::Prepared<W, F>,
    mask: F::E,
    id: [u8; 32],
}
/// The frontend reduction and the values the split needs.
pub struct MixedReduction<const W: usize, F: ZkField<W>> {
    pub proof: SumcheckProof<W, F>,
    pub claim: LinearClaim<F::E>,
    values: Vec<F::E>,
    mask: F::E,
}
impl<const W: usize, F: ZkField<W> + PackingField> MixedParticipant<W, F> {
    /// Sample pads and return the native witness
    /// `[native private inputs | R | native pads]`.
    pub fn prepare(
        &self,
        circuit: &Circuit<F>,
        private: Vec<F::E>,
        mask: F::E,
        rng: &mut impl RandomEngine,
        f: &F,
    ) -> Result<(MixedState<W, F>, Vec<F::E>), String> {
        self.check(circuit, None)?;
        let prepared = frontend::prepare(circuit, private, rng, f)?;
        let mut witness: Vec<_> = self
            .storage
            .entries()
            .iter()
            .zip(&prepared.values)
            .filter(|(s, _)| matches!(s, Storage::Native(_)))
            .map(|(_, v)| v.clone())
            .collect();
        witness.insert(self.mask_cell, mask.clone());
        Ok((
            MixedState {
                prepared,
                mask,
                id: self.id,
            },
            witness,
        ))
    }
    pub fn prove(
        &self,
        circuit: &Circuit<F>,
        public: &[F::E],
        state: MixedState<W, F>,
        t: &mut TranscriptRef<'_>,
        f: &F,
    ) -> Result<MixedReduction<W, F>, String> {
        if state.id != self.id {
            return Err("mixed state ownership".into());
        }
        self.check(circuit, None)?;
        let values = state.prepared.values.clone();
        let (proof, claim) = frontend::prove(circuit, public, state.prepared, t, f)?;
        Ok(MixedReduction {
            proof,
            claim,
            values,
            mask: state.mask,
        })
    }
}
impl<const W: usize, F: ZkField<W>> MixedReduction<W, F> {
    /// The split message `mu = eta*<w_F, v_F> + R`.
    pub fn masked_value(&self, storage: &MixedParticipant<W, F>, eta: &F::E, f: &F) -> F::E
    where
        F: PackingField,
    {
        let mut sum = f.zero();
        for ((s, w), v) in storage
            .storage
            .entries()
            .iter()
            .zip(&self.claim.weights)
            .zip(&self.values)
        {
            if matches!(s, Storage::Foreign(_)) {
                f.add(&mut sum, &f.mulf(w, v));
            }
        }
        f.addf(&f.mulf(eta, &sum), &self.mask)
    }
    /// Values of the foreign claim's terms, in term order, ending with R.
    pub fn foreign_values(&self, storage: &MixedParticipant<W, F>) -> Vec<F::E>
    where
        F: PackingField,
    {
        let mut out: Vec<_> = storage
            .storage
            .entries()
            .iter()
            .zip(&self.values)
            .filter(|(s, _)| matches!(s, Storage::Foreign(_)))
            .map(|(_, v)| v.clone())
            .collect();
        out.push(self.mask.clone());
        out
    }
}
}

cfg_verifier! {
impl<const W: usize, F: ZkField<W> + PackingField> MixedParticipant<W, F> {
    pub fn reduce(
        &self,
        circuit: &Circuit<F>,
        public: &[F::E],
        proof: &SumcheckProof<W, F>,
        t: &mut TranscriptRef<'_>,
        f: &F,
    ) -> Result<LinearClaim<F::E>, String> {
        self.check(circuit, None)?;
        frontend::reduce(circuit, public, proof, t, f)
    }
}
}

impl<const W: usize, F: ZkField<W> + PackingField> crate::runtime::v2::zk::joint::AbsorbLayout
    for MixedParticipant<W, F>
{
    fn absorb_layout(&self, t: &mut TranscriptRef<'_>) {
        super::transcript::absorb_storage(t, &self.id, &self.storage, self.mask);
    }
}
