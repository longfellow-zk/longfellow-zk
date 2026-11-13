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
use super::adapter::AdapterMode;
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{gf2_128::Gf2_128Field, EvaluationDomain, PackingField, ZkField},
        v2::{
            polygero::PolygeroConfig,
            proto::composed::ComposedGeometry,
            zk::{
                joint::{CircuitParticipant, JointParam, SelectedField},
                storage::{Group, ReservedSuffix, Storage, StorageMap},
                ZkContext,
            },
        },
    },
};

cfg_prover! { #[path="compose_prover.rs"] mod prover; }
cfg_verifier! { #[path="compose_verifier.rs"] mod verifier; }

/// Width of the binary host's field.
const H: usize = 2;
type Host = Gf2_128Field;

/// The joint field list of a composition: the host, then the split participant.
type Fields<'s, const W: usize, F, DH, DS> = (
    SelectedField<'s, H, Host, DH, &'s CircuitParticipant<H, Host>>,
    (
        SelectedField<'s, W, F, DS, &'s CircuitParticipant<W, F>>,
        (),
    ),
);

/// A composition's fixed layout, derived from its two circuits and the split
/// participant's storage map.
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
            if let Storage::Foreign(_) = s {
                let g = s
                    .prime_group()
                    .ok_or("composition expects prime-field foreign values")?;
                if g.start < npublic || g.end() > ninput {
                    return Err("foreign values must be private host inputs".into());
                }
                widths.push(g.width);
            }
        }
        let mut suffix = ReservedSuffix::new(ninput);
        let mask = suffix.group(M::MASK_BITS);
        widths.push(mask.width);
        let mode = M::new(widths, npublic, &mut suffix)?;
        let (host_ctx, split_ctx) = (ZkContext::new(domains.0), ZkContext::new(domains.1));
        let host = CircuitParticipant::with_virtual_inputs(
            host_circuit,
            &[mode.fragment()],
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
            joint_context: param.context(),
            config: param.config(),
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
