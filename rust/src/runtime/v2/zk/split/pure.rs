// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Pure-foreign storage, tests only until a driver uses it.
//!
//! Every value `[private inputs | pads]` of the participant is a bit group of
//! the binary commitment, so it commits nothing and has no Polygero
//! parameter, masks or rows. After its frontend, fresh row weights, drawn and
//! used by the pure split step (`PureClaim::batch`), batch every layer row
//! and the input equation into one foreign claim with a public target
//! (`batching`). No composition runs this schedule (zk I11, foreign I2).
use super::{
    super::{
        batching::{self, LinearClaim},
        joint::{Frontend, FrontendPart, Participant, StorageLayout},
        packing_commitment::PackingLayout,
        prover::{prove_values, Identity},
        storage::{ModularClaim, Storage, StorageMap},
        verifier::reduce_values,
        CircuitInput,
    },
    transcript, SplitShape,
};
use crate::{
    core::{algebra::BareField, proto::v2::Circuit},
    runtime::{
        algebra::{
            packing::{PackingExtension, PackingField},
            range_interpolation::EvaluationDomain,
            ZkField,
        },
        random::PrivateRandom,
        v2::{
            polygero::{PolygeroLinearTerm, PolygeroParam},
            proto::{polygero::PolygeroConfig, sumcheck::SumcheckProof, zk::CircuitProofGeometry},
            sumcheck::{self, SumcheckPads},
            transcript::Bound,
        },
    },
};

/// A participant with pure-foreign storage: a single degree-one prime
/// circuit all of whose values are bit groups of the binary commitment.
pub(crate) struct PureSplit<const W: usize, F: ZkField<W> + PackingField> {
    frontend: Frontend<W, F>,
    map: StorageMap,
}
impl<const W: usize, F: ZkField<W> + PackingField> PureSplit<W, F> {
    /// The pure-foreign participant of `circuit` whose values are stored as
    /// `map` says; every value must be foreign.
    pub(crate) fn new<D: EvaluationDomain<W, F>>(
        circuit: &Circuit<F>,
        map: StorageMap,
        config: PolygeroConfig,
        domain: &D,
    ) -> Result<Self, String> {
        let shape = SplitShape::new(circuit, domain)?;
        map.check_pure(shape.values)?;
        let layout = PackingLayout::new(0, 0, 1)?;
        Ok(Self {
            frontend: shape.frontend(circuit, layout, 0, config, domain)?,
            map,
        })
    }
    pub(crate) fn geometry(&self) -> CircuitProofGeometry {
        self.frontend.geometry.clone()
    }
    /// Sample the pads. The participant commits nothing, so it has no
    /// witness for the joint commitment.
    pub(crate) fn prepare(
        &self,
        private: Vec<CircuitInput<F>>,
        rng: &mut impl PrivateRandom,
    ) -> Result<PureState<W, F>, String> {
        if private.len() != self.frontend.inputs.committed() {
            return Err("split witness shape".into());
        }
        let f = self.frontend.field();
        let parameters = &self.frontend.backend.parameters;
        let mut values = parameters.extension().into_input_elements(f, private);
        let (pads, suffix) = sumcheck::sample_pads(self.frontend.geometry.sumcheck(), rng, f);
        values.extend(suffix);
        Ok(PureState {
            pads,
            values,
            participant: self.frontend.identity(self.map.clone()),
        })
    }
    /// The whole claim of this participant, whose target is public: the
    /// batched claim `claim` over its foreign values.
    fn claim(&self, claim: LinearClaim<F::E>) -> Result<ModularClaim<F::E>, String> {
        if claim.weights.len() != self.map.entries().len() {
            return Err("pure claim does not cover the participant's values".into());
        }
        // `new` checked that every value is foreign.
        let terms = self
            .map
            .entries()
            .iter()
            .zip(&claim.weights)
            .filter_map(|(s, w)| match s {
                Storage::Foreign(g) => Some((*g, w.clone())),
                Storage::Native(_) => None,
            })
            .collect();
        Ok(ModularClaim {
            terms,
            target: claim.target,
        })
    }
}
impl<const W: usize, F: ZkField<W> + PackingField> Participant<W, F> for PureSplit<W, F> {
    fn frontend(&self) -> &Frontend<W, F> {
        &self.frontend
    }
    fn storage(&self) -> StorageLayout<'_> {
        StorageLayout::Pure(&self.map)
    }
    fn param_for_test(&self) -> Option<&PolygeroParam> {
        None
    }
}

/// Prover state of a pure-foreign participant before its frontend.
pub(crate) struct PureState<const W: usize, F: ZkField<W>> {
    pads: SumcheckPads<F>,
    /// `[private inputs | pads]`, in value order.
    values: Vec<F::E>,
    participant: Identity<StorageMap>,
}

/// A pure-foreign participant's frontend claim over `[private inputs |
/// pads]`: the layer rows and the input equation, unbatched.
pub(crate) struct PureClaim<E> {
    rows: (Vec<PolygeroLinearTerm<E>>, Vec<E>),
    /// The input equation `<w, v> = t` over the values.
    pub(crate) claim: LinearClaim<E>,
}
/// The prover's pure-foreign reduction, with the values of the claim.
pub(crate) struct PurePending<E> {
    pub(crate) claim: PureClaim<E>,
    pub(crate) values: Vec<E>,
}

/// The frontend's rows from its reduced constraints, on its values.
fn frontend_claim<const W: usize, F: ZkField<W> + PackingField>(
    part: &FrontendPart<'_, W, F, PureSplit<W, F>>,
    constraints: sumcheck::symbolic::Constraints<F::E>,
) -> Result<PureClaim<F::E>, String> {
    let (rows, claim) = batching::rows(
        part.circuits()[0],
        &part.public,
        constraints,
        part.frontend().geometry.sumcheck(),
        part.field(),
    )?;
    Ok(PureClaim { rows, claim })
}

/// Run the pure-foreign frontend of `t`'s part and reduce its constraints to
/// its unbatched rows.
pub(crate) fn prove<const W: usize, F: ZkField<W> + PackingField>(
    t: &mut Bound<'_, FrontendPart<'_, W, F, PureSplit<W, F>>>,
    state: PureState<W, F>,
) -> Result<(SumcheckProof<F>, PurePending<F::E>), String> {
    let p = t.part().participant;
    if !p.frontend.prepared(&state.participant, &p.map) {
        return Err("split state belongs to another participant".into());
    }
    let (proof, constraints) = prove_values(t, &state.values, state.pads)?;
    let claim = frontend_claim(t.part(), constraints)?;
    Ok((
        proof,
        PurePending {
            claim,
            values: state.values,
        },
    ))
}

/// Check the pure-foreign frontend proof of `t`'s part and reduce its
/// constraints to its unbatched rows.
pub(crate) fn reduce<const W: usize, F: ZkField<W> + PackingField>(
    t: &mut Bound<'_, FrontendPart<'_, W, F, PureSplit<W, F>>>,
    proof: &SumcheckProof<F>,
) -> Result<PureClaim<F::E>, String> {
    let constraints = reduce_values(t, proof)?;
    frontend_claim(t.part(), constraints)
}

impl<E> PureClaim<E> {
    /// The number of row weights: one per layer row, one for the input
    /// equation.
    pub(crate) fn row_weight_count(&self) -> usize {
        self.rows.1.len() + 1
    }
    /// Draw the row weights rho_0..rho_L at the current boundary, right after
    /// the frontend's last message, and batch every row and the input
    /// equation with them into one foreign claim with a public target. The
    /// weights are internal to this step (transcript I8).
    pub(crate) fn batch<const W: usize, F>(
        self,
        t: &mut Bound<'_, FrontendPart<'_, W, F, PureSplit<W, F>>>,
    ) -> Result<ModularClaim<E>, String>
    where
        F: ZkField<W> + PackingField + BareField<E = E>,
    {
        let (p, f) = (t.part().participant, t.part().field());
        let weights = transcript::row_weights(&mut t.transcript(), self.row_weight_count(), f);
        let claim = batching::batch((self.rows, self.claim), &weights, f)?;
        p.claim(claim)
    }
}
