// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Storage splits: claims over values stored outside a participant's own
//! commitment.
//!
//! A participant's value vector is `[private inputs | pads]`. Its storage
//! map assigns each value a native cell or foreign bits in the binary
//! commitment. Each storage mode is its own participant type:
//!
//! - All native (`joint::CircuitParticipant`): the ordinary circuit reduction applies.
//! - Mixed (`MixedSplit`): the participant commits `[native private inputs | pads | R]`, and every
//!   pad is native. The layer rows read only pads, so they go to this field's Polygero participant
//!   unchanged. The input equation `<w, v> = t` is split with a fresh nonzero challenge `eta` and
//!   one masked message `mu = eta*<w_F, v_F> + R` into:
//!   - a native row `eta*<w_N, v_N> - R + mu - eta*t = 0`, beside the layer rows;
//!   - a foreign claim `<eta*w_F, v_F> + R_bits = mu (mod p)` for the adapter.
//!
//!   R is uniform and used only here, so `mu` hides `<w_F, v_F>`.
//! - Pure foreign (`pure::PureSplit`, tests only until a driver uses it): the participant commits
//!   nothing. Fresh weights, drawn and used by the pure split step (`PureClaim::batch`), batch
//!   every layer row and the input equation into one foreign claim with a public target
//!   (`batching`).
use super::{
    batching::{rows, LinearClaim},
    context::prepare_parameter,
    joint::{check_registered, Frontend, FrontendPart, Participant, SelectedField, StorageLayout},
    packing_commitment::{PackingCommitment, PackingLayout},
    storage::{Group, MixedStorage, ModularClaim, Storage, StorageMap},
    InputLayout,
};
use crate::{
    core::{
        algebra::{BareField, SerializableField},
        proto::v2::Circuit,
    },
    runtime::{
        algebra::{
            packing::{PackingExtension, PackingField},
            range_interpolation::EvaluationDomain,
            ZkField,
        },
        v2::{
            polygero::{LinearStatement, PolygeroLinearTerm, PolygeroParam},
            proto::{
                polygero::PolygeroConfig, sumcheck::SumcheckProofGeometry, zk::CircuitProofGeometry,
            },
            sumcheck::{circuit_geometry, symbolic::Constraints},
            transcript::{Bound, SessionStamp},
        },
    },
};

#[cfg(test)]
pub(crate) mod pure;
pub(crate) mod transcript;
use transcript::Eta;

/// The shape of a split participant of one circuit: its input layout, its
/// sumcheck geometry, and the counts of its private inputs and of its values
/// `[private inputs | pads]`.
struct SplitShape {
    inputs: InputLayout,
    sumcheck: SumcheckProofGeometry,
    private: usize,
    values: usize,
}
impl SplitShape {
    /// The shape of a split participant of `circuit` over `domain`'s field,
    /// which must be a registered degree-one prime field.
    fn new<F: ZkField + PackingField, D: EvaluationDomain<F>>(
        circuit: &Circuit<F>,
        domain: &D,
    ) -> Result<Self, String> {
        check_registered(domain.field())?;
        if domain.field().is_binary() || domain.field().packing_extension().degree() != 1 {
            return Err("split storage requires a degree-one prime frontend".into());
        }
        let sumcheck = circuit_geometry(&[circuit])?;
        let inputs = InputLayout::new(&[circuit], 0)?;
        let private = inputs.committed();
        let values = private
            .checked_add(sumcheck.pad_count())
            .ok_or("split layout overflow")?;
        Ok(Self {
            inputs,
            sumcheck,
            private,
            values,
        })
    }
    /// The participant's frontend, committing `layout` in `nw` cells.
    fn frontend<F: ZkField + PackingField, D: EvaluationDomain<F>>(
        self,
        circuit: &Circuit<F>,
        layout: PackingLayout,
        nw: usize,
        #[cfg_attr(not(any(test, feature = "prover")), allow(unused_variables))]
        config: PolygeroConfig,
        domain: &D,
    ) -> Result<Frontend<F>, String> {
        let extension = domain.field().packing_extension();
        Ok(Frontend {
            geometry: CircuitProofGeometry::new(self.sumcheck, 1, nw).map_err(|e| e.to_string())?,
            #[cfg(any(test, feature = "prover"))]
            config,
            backend: PackingCommitment::new(domain.field().clone(), layout, extension)?,
            id: circuit.id,
            additional_ids: Vec::new(),
            inputs: self.inputs,
        })
    }
}

/// A participant with mixed storage: a single degree-one prime circuit whose
/// values `[private inputs | pads]` are stored as its `MixedStorage` says. It
/// commits `[native private inputs | pads | R]`; R's bits are the storage's
/// mask group in the binary commitment, which the composition allocates and
/// whose bits the adapter mode's driver writes.
pub(crate) struct MixedSplit<F: ZkField + PackingField> {
    pub(super) frontend: Frontend<F>,
    /// The Polygero parameter of the committed cells.
    param: PolygeroParam,
    pub(super) storage: MixedStorage,
}
impl<F: ZkField + PackingField> MixedSplit<F> {
    /// The mixed split participant of `circuit` whose values are stored as
    /// `map` says, with R's bits at `mask`.
    pub(crate) fn new<D: EvaluationDomain<F>>(
        circuit: &Circuit<F>,
        map: StorageMap,
        mask: Group,
        config: PolygeroConfig,
        domain: &D,
    ) -> Result<Self, String> {
        let shape = SplitShape::new(circuit, domain)?;
        let storage = MixedStorage::new(map, mask, shape.private, shape.values)?;
        // The native values are committed in value order (native private
        // inputs, then pads), then R.
        let pads = shape.sumcheck.pad_count();
        let layout = PackingLayout::new(storage.map.native_cells() - pads, pads, 1)?;
        let param = prepare_parameter(layout.witness_count + 1, config, domain)?;
        SelectedField::from_parameter(param.clone(), domain)?;
        let nw = param.geometry().nw;
        Ok(Self {
            frontend: shape.frontend(circuit, layout, nw, config, domain)?,
            param,
            storage,
        })
    }
    pub(crate) fn geometry(&self) -> CircuitProofGeometry {
        self.frontend.geometry.clone()
    }
    /// The field of this participant's circuit and commitment, the field of
    /// the domain it was built with.
    pub(crate) fn field(&self) -> &F {
        self.frontend.field()
    }
    /// This participant as a field of the joint commitment, over `domain`,
    /// the domain it was built with.
    pub(crate) fn participant<'a, D: EvaluationDomain<F>>(
        &'a self,
        domain: &'a D,
    ) -> Result<SelectedField<'a, F, D>, String> {
        SelectedField::from_parameter(self.param.clone(), domain)
    }
}
impl<F: ZkField + PackingField> MixedSplit<F> {
    /// The storage map, for the composed prover's cheat that takes the
    /// foreign values from the host's bits (`transcript::cheat`).
    #[cfg(test)]
    pub(crate) fn map_for_test(&self) -> &StorageMap {
        &self.storage.map
    }
}
impl<F: ZkField + PackingField> Participant<F> for MixedSplit<F> {
    fn frontend(&self) -> &Frontend<F> {
        &self.frontend
    }
    fn storage(&self) -> StorageLayout<'_> {
        StorageLayout::Mixed(&self.storage)
    }
    #[cfg(test)]
    fn param_for_test(&self) -> Option<&PolygeroParam> {
        Some(&self.param)
    }
}

/// A mixed split participant's frontend claim over `[private inputs |
/// pads]`.
pub(crate) struct SplitClaim<E> {
    /// The layer rows, unbatched, on this field's native cells.
    rows: (Vec<PolygeroLinearTerm<E>>, Vec<E>),
    /// The input equation `<w, v> = t` over the values.
    pub(crate) claim: LinearClaim<E>,
}

impl<F: ZkField + PackingField> MixedSplit<F> {
    /// Reduce the frontend's constraints to the claim its storage discharges:
    /// the frontend's rows over its values (`batching::rows`), with the layer
    /// rows moved from value indices to this field's native cells. Every pad
    /// is native, so every layer row has a native cell. Both roles call this
    /// after the frontend's last message, on the frontend's own part: its
    /// circuit and public inputs.
    pub(super) fn split_claim(
        t: &mut Bound<'_, FrontendPart<'_, F, Self>>,
        constraints: Constraints<F::E>,
    ) -> Result<SplitClaim<F::E>, String> {
        let part = t.part();
        let p = part.participant;
        let ((mut a, b), claim) = rows(
            part.circuits()[0],
            &part.public,
            constraints,
            p.frontend.geometry.sumcheck(),
            part.field(),
        )?;
        for term in &mut a {
            term.w = p.storage.native_cell(term.w)?;
        }
        Ok(SplitClaim {
            rows: (a, b),
            claim,
        })
    }
    /// Check that `claim` covers this participant's values.
    fn check_claim(&self, claim: &SplitClaim<F::E>) -> Result<(), String> {
        if claim.claim.weights.len() != self.storage.map.entries().len() {
            return Err("split claim shape".into());
        }
        Ok(())
    }
    /// This field's statement on `session`: the layer rows, then the native
    /// row `eta*<w_N, v_N> - R + mu - eta*t = 0`.
    /// It consumes the claim: its layer rows become the statement's rows.
    fn split_statement(
        &self,
        claim: SplitClaim<F::E>,
        Eta(eta): &Eta<F::E>,
        mu: &F::E,
        session: SessionStamp,
    ) -> Result<LinearStatement<F::E>, String> {
        self.check_claim(&claim)?;
        let (split, f) = (&self.storage, self.field());
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
        Eta(eta): &Eta<F::E>,
        mu: &F::E,
    ) -> Result<ModularClaim<F::E>, String> {
        self.check_claim(claim)?;
        let (split, f) = (&self.storage, self.field());
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
        terms.push((split.mask, f.one()));
        Ok(ModularClaim {
            terms,
            target: mu.clone(),
        })
    }
}

/// A mixed split participant's reduction, before its split challenge. Only
/// the prover holds one: it carries the private values and R.
#[cfg(any(test, feature = "prover"))]
pub(crate) struct PendingSplit<E> {
    pub(crate) claim: SplitClaim<E>,
    pub(crate) values: Vec<E>,
    pub(crate) mask: E,
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
    /// Draw `eta`, send the split message `mu` on the frontend's session,
    /// and return `mu` with both outputs, all built from this `eta` and `mu`.
    pub(crate) fn open<F>(
        self,
        t: &mut Bound<'_, FrontendPart<'_, F, MixedSplit<F>>>,
    ) -> Result<(E, SplitOutput<E>), String>
    where
        F: ZkField + PackingField + BareField<E = E>,
    {
        let (p, f) = (t.part().participant, t.part().field());
        let eta = transcript::eta(&mut t.transcript(), f);
        let mu = p.split_message(&self, &eta)?;
        transcript::send_mu(&mut t.transcript(), &mu, f);
        let foreign = p.foreign_claim(&self.claim, &eta, &mu)?;
        let statement = p.split_statement(self.claim, &eta, &mu, t.session())?;
        Ok((mu, SplitOutput { statement, foreign }))
    }
}
#[cfg(any(test, feature = "verifier"))]
impl<E> SplitClaim<E> {
    /// Draw `eta`, absorb the proof's split message `mu` on the frontend's
    /// session, and return both outputs, built from this `eta` and `mu`.
    pub(crate) fn receive<F>(
        self,
        t: &mut Bound<'_, FrontendPart<'_, F, MixedSplit<F>>>,
        mu: &E,
    ) -> Result<SplitOutput<E>, String>
    where
        F: ZkField + PackingField + BareField<E = E>,
    {
        let (p, f) = (t.part().participant, t.part().field());
        let eta = transcript::eta(&mut t.transcript(), f);
        transcript::send_mu(&mut t.transcript(), mu, f);
        let foreign = p.foreign_claim(&self, &eta, mu)?;
        let statement = p.split_statement(self, &eta, mu, t.session())?;
        Ok(SplitOutput { statement, foreign })
    }
}
#[cfg(any(test, feature = "prover"))]
impl<F: ZkField + PackingField> MixedSplit<F> {
    /// The split message `mu = eta*<w_F, v_F> + R`.
    fn split_message(
        &self,
        pending: &PendingSplit<F::E>,
        Eta(eta): &Eta<F::E>,
    ) -> Result<F::E, String> {
        self.check_claim(&pending.claim)?;
        let f = self.field();
        let mut sum = f.zero();
        for ((s, w), v) in self
            .storage
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
        Ok(f.addf(&f.mulf(eta, &sum), &pending.mask))
    }
    /// Values of the foreign claim's terms, in term order, ending with R.
    pub(crate) fn foreign_values(&self, pending: &PendingSplit<F::E>) -> Vec<F::E> {
        let mut out: Vec<_> = self
            .storage
            .map
            .entries()
            .iter()
            .zip(&pending.values)
            .filter(|(s, _)| matches!(s, Storage::Foreign(_)))
            .map(|(_, v)| v.clone())
            .collect();
        out.push(pending.mask.clone());
        out
    }
}

/// Number of values `[private inputs | pads]` of a split participant for
/// `circuit`; a storage map must cover exactly this many.
#[cfg_attr(not(any(test, feature = "mdoc")), allow(dead_code))]
pub(crate) fn value_count<F: SerializableField>(circuit: &Circuit<F>) -> Result<usize, String> {
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
