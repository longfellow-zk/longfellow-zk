// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The composition driver: a binary host participant and one mixed split
//! participant whose foreign values are bits of the host's witness.
//!
//! The host's input array is
//! `[public | format private | R | adapter pads | virtual leaves]`. The
//! format circuit reads only its own prefix. Each role then runs, on one
//! transcript:
//!
//! 1. the joint commitment of both participants;
//! 2. the split participant's frontend and its split (`eta`, `mu`);
//! 3. the adapter mode's rounds, which define the virtual leaves;
//! 4. the host's frontend over the format circuit and the mode's fragment;
//! 5. the joint opening of both statements.
//!
//! Scope: the driver composes exactly one GF(2^128) host and one degree-one
//! prime participant with mixed storage (`MixedSplit`). Pure-foreign storage
//! (`PureSplit`) is a type of its own, which this driver does not take. Other
//! shapes need a new driver.
use super::{adapter::AdapterMode, reserved::ReservedSuffix};
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{
            gf2_128::Gf2_128Field, packing::PackingField, range_interpolation::EvaluationDomain,
            ZkField,
        },
        v2::{
            proto::{composed::ComposedGeometry, polygero::PolygeroConfig},
            transcript::{Header, SetupMessage, Statement},
            zk::{
                joint::{CircuitParticipant, FrontendPart, JointParam, SelectedField},
                split::MixedSplit,
                storage::{Group, Storage, StorageMap},
                write_joint_geometry, CircuitInput,
            },
        },
    },
};

cfg_prover! { mod prover; }
cfg_verifier! { mod verifier; }

type Host = Gf2_128Field;

/// The joint field list of a composition: the host, then the split participant.
type Fields<'s, F, DH, DS> = (SelectedField<'s, Host, DH>, (SelectedField<'s, F, DS>, ()));

/// A composition's fixed layout, derived from its two circuits and the split
/// participant's storage map.
///
/// The host is a GF(2^128) participant; the split participant is a
/// degree-one prime participant whose storage is mixed: some values native,
/// the others bit groups of the host's private inputs (`MixedSplit`).
pub(crate) struct Composition<'a, F: ZkField + PackingField, DH, DS, M>
where
    DH: EvaluationDomain<Host>,
    DS: EvaluationDomain<F>,
{
    host_circuit: &'a Circuit<Host>,
    split_circuit: &'a Circuit<F>,
    /// The interpolation domains of the host and of the split participant.
    domains: (&'a DH, &'a DS),
    host: CircuitParticipant<Host>,
    split: MixedSplit<F>,
    /// R and the mode's pads after the host circuit's inputs, filled by the
    /// prover.
    #[cfg_attr(not(any(test, feature = "prover")), allow(dead_code))]
    suffix: ReservedSuffix,
    /// R's bits in the host witness, written by the prover.
    #[cfg_attr(not(any(test, feature = "prover")), allow(dead_code))]
    mask: Group,
    mode: M,
}
impl<'a, F, DH, DS, M> Composition<'a, F, DH, DS, M>
where
    F: ZkField + PackingField,
    DH: EvaluationDomain<Host>,
    DS: EvaluationDomain<F>,
    M: AdapterMode<F>,
{
    /// `storage` covers the split circuit's values `[private inputs | pads]`.
    /// Its foreign values must be private inputs of the host circuit. The
    /// split mask R and the mode's pads follow the host circuit's inputs.
    /// `joint` is the one Polygero profile both fields commit under.
    pub(crate) fn new(
        host_circuit: &'a Circuit<Host>,
        split_circuit: &'a Circuit<F>,
        storage: StorageMap,
        joint: PolygeroConfig,
        domains: (&'a DH, &'a DS),
    ) -> Result<Self, String> {
        let (npublic, ninput) = (host_circuit.raw.npublic_input, host_circuit.raw.ninput);
        let mut widths = Vec::new();
        for s in storage.entries() {
            if let Storage::Foreign(g) = s {
                if g.start() < npublic || g.end() > ninput {
                    return Err("foreign values must be private host inputs".into());
                }
                widths.push(g.width());
            }
        }
        let mut suffix = ReservedSuffix::new(ninput);
        let mask = suffix.group(M::MASK_BITS)?;
        widths.push(mask.width());
        let mode = M::new(widths, npublic, &mut suffix)?;
        let host = CircuitParticipant::new(
            &[host_circuit, mode.fragment()],
            mode.virtual_inputs(),
            joint,
            domains.0,
        )?;
        let split = MixedSplit::new(split_circuit, storage, mask, joint, domains.1)?;
        Ok(Self {
            host_circuit,
            split_circuit,
            domains,
            host,
            split,
            suffix,
            mask,
            mode,
        })
    }
    fn param(&self) -> Result<JointParam<Fields<'_, F, DH, DS>>, String> {
        JointParam::new((
            self.host.participant(self.domains.0)?,
            (self.split.participant(self.domains.1)?, ()),
        ))
    }
    pub(crate) fn geometry(&self) -> Result<ComposedGeometry, String> {
        let param = self.param()?;
        ComposedGeometry::new(self.host.geometry(), self.split.geometry(), param.config())
            .map_err(|e| e.to_string())
    }
    /// The composition's statement on these public inputs: the application's
    /// `identity` message, both frontends and the geometry the proof is
    /// parsed against.
    pub(crate) fn statement<'s, I: SetupMessage>(
        &'s self,
        identity: I,
        host_public: &'s [CircuitInput<Host>],
        split_public: &'s [CircuitInput<F>],
    ) -> Result<ComposedStatement<'s, F, DH, DS, M, I>, String> {
        Ok(ComposedStatement {
            identity,
            composition: self,
            host: FrontendPart::new(
                &self.host,
                &[self.host_circuit, self.mode.fragment()],
                host_public,
            )?,
            split: FrontendPart::new(&self.split, &[self.split_circuit], split_public)?,
            geometry: self.geometry()?,
        })
    }
    /// The bits after the host circuit's inputs: R, then the mode's pads.
    #[cfg(all(test, feature = "mdoc"))]
    pub(crate) fn reserved(&self) -> &ReservedSuffix {
        &self.suffix
    }
    #[cfg(test)]
    pub(crate) fn mode(&self) -> &M {
        &self.mode
    }
}

/// A composition's statement: the application's identity message, then
/// the composition's statement messages: a `Circuit` per circuit in
/// participant order (the host circuit, the adapter fragment, the split
/// circuit), a `CommitmentLayout` per field (host, then split), the mode's
/// `AdapterLayout`, the `JointGeometry`, and the `PublicInputs` of each
/// field (host, then split). Proving and verifying take a session opened
/// with it and read the frontends from it (transcript I2).
pub(crate) struct ComposedStatement<'s, F: ZkField + PackingField, DH, DS, M, I>
where
    DH: EvaluationDomain<Host>,
    DS: EvaluationDomain<F>,
{
    identity: I,
    composition: &'s Composition<'s, F, DH, DS, M>,
    host: FrontendPart<'s, Host>,
    split: FrontendPart<'s, F, MixedSplit<F>>,
    geometry: ComposedGeometry,
}
impl<F, DH, DS, M, I> ComposedStatement<'_, F, DH, DS, M, I>
where
    F: ZkField + PackingField,
    DH: EvaluationDomain<Host>,
    DS: EvaluationDomain<F>,
{
    /// The geometry the statement writes, which the proof is parsed against.
    /// The prover seals against it.
    #[cfg(any(test, feature = "prover"))]
    pub(crate) fn geometry(&self) -> &ComposedGeometry {
        &self.geometry
    }
}
impl<F, DH, DS, M, I> Statement for ComposedStatement<'_, F, DH, DS, M, I>
where
    F: ZkField + PackingField,
    DH: EvaluationDomain<Host>,
    DS: EvaluationDomain<F>,
    M: AdapterMode<F>,
    I: SetupMessage,
{
    type Identity = I;
    fn identity(&self) -> &I {
        &self.identity
    }
    fn write(&self, h: &mut Header<'_>) {
        self.host.write_circuits(h);
        self.split.write_circuits(h);
        self.host.write_layout(h);
        self.split.write_layout(h);
        self.composition.mode.write_layout(h);
        write_joint_geometry(h, self.geometry.config());
        self.host.write_public(h);
        self.split.write_public(h);
    }
}
#[cfg(test)]
mod tests;
