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
//! prime participant with mixed storage. `CircuitParticipant` also supports
//! pure-foreign storage, but this driver always supplies the split mask R and
//! so rejects it. Other shapes need a new driver.
use super::adapter::AdapterMode;
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{
            gf2_128::Gf2_128Field, packing::PackingField, range_interpolation::EvaluationDomain,
            ZkField,
        },
        v2::{
            proto::{composed::ComposedGeometry, polygero::PolygeroConfig},
            transcript::Header,
            zk::{
                joint::{CircuitParticipant, FrontendPart, JointParam, SelectedField},
                storage::{Group, ReservedSuffix, Storage, StorageMap},
                write_joint_geometry, CircuitInput, ZkContext,
            },
        },
    },
};

cfg_prover! { mod prover; }
cfg_verifier! { mod verifier; }

/// Width of the binary host's field.
const H: usize = 2;
type Host = Gf2_128Field;

/// The joint field list of a composition: the host, then the split participant.
type Fields<'s, const W: usize, F, DH, DS> = (
    SelectedField<'s, H, Host, DH>,
    (SelectedField<'s, W, F, DS>, ()),
);

/// A composition's fixed layout, derived from its two circuits and the split
/// participant's storage map.
///
/// The host is a GF(2^128) participant; the split participant is a
/// degree-one prime participant whose storage is mixed: some values native,
/// the others bit groups of the host's private inputs. Pure-foreign storage
/// is rejected, since the driver always supplies the split mask R.
pub struct Composition<'a, const W: usize, F: ZkField<W> + PackingField, DH, DS, M>
where
    DH: EvaluationDomain<H, Host>,
    DS: EvaluationDomain<W, F>,
{
    host_circuit: &'a Circuit<Host>,
    split_circuit: &'a Circuit<F>,
    host_ctx: ZkContext<'a, H, Host, DH>,
    split_ctx: ZkContext<'a, W, F, DS>,
    host: CircuitParticipant<H, Host>,
    split: CircuitParticipant<W, F>,
    suffix: ReservedSuffix,
    /// R's bits in the host witness, written by the prover.
    #[cfg_attr(not(any(test, feature = "prover")), allow(dead_code))]
    mask: Group,
    mode: M,
}
impl<'a, const W: usize, F, DH, DS, M> Composition<'a, W, F, DH, DS, M>
where
    F: ZkField<W> + PackingField,
    DH: EvaluationDomain<H, Host>,
    DS: EvaluationDomain<W, F>,
    M: AdapterMode<F>,
{
    /// `storage` covers the split circuit's values `[private inputs | pads]`.
    /// Its foreign values must be private inputs of the host circuit. The
    /// split mask R and the mode's pads follow the host circuit's inputs.
    pub fn new(
        host_circuit: &'a Circuit<Host>,
        split_circuit: &'a Circuit<F>,
        storage: StorageMap,
        config: (PolygeroConfig, PolygeroConfig),
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
        let (host_ctx, split_ctx) = (ZkContext::new(domains.0), ZkContext::new(domains.1));
        let host = CircuitParticipant::new(
            &[host_circuit, mode.fragment()],
            mode.virtual_inputs(),
            config.0,
            &host_ctx,
        )?;
        let split = CircuitParticipant::with_storage(
            split_circuit,
            storage,
            Some(mask),
            config.1,
            &split_ctx,
        )?;
        Ok(Self {
            host_circuit,
            split_circuit,
            host_ctx,
            split_ctx,
            host,
            split,
            suffix,
            mask,
            mode,
        })
    }
    fn param(&self) -> Result<JointParam<Fields<'_, W, F, DH, DS>>, String> {
        JointParam::new((
            self.host.participant(&self.host_ctx)?,
            (self.split.participant(&self.split_ctx)?, ()),
        ))
    }
    pub fn geometry(&self) -> Result<ComposedGeometry, String> {
        let param = self.param()?;
        Ok(ComposedGeometry {
            host: self.host.geometry(),
            split: self.split.geometry(),
            config: param.config(),
        })
    }
    /// The composition's statement part on these public inputs: both
    /// frontends and the geometry the proof is parsed against.
    pub fn statement<'s>(
        &'s self,
        host_public: &'s [CircuitInput<Host>],
        split_public: &'s [CircuitInput<F>],
    ) -> Result<ComposedStatement<'s, W, F, DH, DS, M>, String> {
        Ok(ComposedStatement {
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
    pub fn reserved(&self) -> &ReservedSuffix {
        &self.suffix
    }
    pub fn mode(&self) -> &M {
        &self.mode
    }
}

/// A composition's statement part: its two frontends on their public inputs
/// and its geometry. `write` emits the composition's statement messages:
/// a `Circuit` per circuit in participant order (the host circuit, the
/// adapter fragment, the split circuit), a `CommitmentLayout` per field
/// (host, then split), the mode's `AdapterLayout`, the `JointGeometry`, and
/// the `PublicInputs` of each field (host, then split). Proving and
/// verifying read the frontends from here (transcript I2).
pub struct ComposedStatement<'s, const W: usize, F: ZkField<W> + PackingField, DH, DS, M>
where
    DH: EvaluationDomain<H, Host>,
    DS: EvaluationDomain<W, F>,
{
    composition: &'s Composition<'s, W, F, DH, DS, M>,
    host: FrontendPart<'s, H, Host>,
    split: FrontendPart<'s, W, F>,
    geometry: ComposedGeometry,
}
impl<const W: usize, F, DH, DS, M> ComposedStatement<'_, W, F, DH, DS, M>
where
    F: ZkField<W> + PackingField,
    DH: EvaluationDomain<H, Host>,
    DS: EvaluationDomain<W, F>,
    M: AdapterMode<F>,
{
    pub fn write(&self, h: &mut Header<'_>) {
        self.host.write_circuits(h);
        self.split.write_circuits(h);
        self.host.write_layout(h);
        self.split.write_layout(h);
        self.composition.mode.write_layout(h);
        let g = &self.geometry;
        write_joint_geometry(
            h,
            g.config,
            &[g.host.com_geom.nw as u64, g.split.com_geom.nw as u64],
        );
        self.host.write_public(h);
        self.split.write_public(h);
    }
    /// The geometry the statement writes, which the proof is parsed against.
    pub fn geometry(&self) -> &ComposedGeometry {
        &self.geometry
    }
}

#[cfg(test)]
mod tests;
