// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 circuit and packing layouts bound before the selected joint commitment.
//! Sumcheck, packing and witness selection own their respective rounds.
use super::{
    joint::{AbsorbLayout, CircuitParticipant},
    packing_commitment::PackingCommitment,
};
use crate::runtime::{
    algebra::{PackingExtension, PackingField, ZkField},
    v2::transcript::TranscriptRef,
};

impl<F: PackingField, X: PackingExtension<Ambient = F>> PackingCommitment<F, X> {
    pub(crate) fn absorb(&self, t: &mut TranscriptRef<'_>, id: &[u8; 32])
    where F: crate::core::algebra::SerializableField {
        if self.layout.degree == 1 {
            return;
        }
        t.absorb(|w| {
            w.write_bytes(b"longfellow/v2/packing-commitment/v1");
            w.write_bytes(id);
        });
        t.absorb(|w| w.write_bytes(&self.parameters.descriptor()));
        for n in [self.layout.private_inputs, self.layout.pad_cells] {
            t.absorb(|w| w.write_bytes(&(n as u64).to_le_bytes()));
        }
    }
}

impl<const W: usize, F: ZkField<W> + PackingField> AbsorbLayout for CircuitParticipant<W, F> {
    /// Bind packing and composed-circuit layout before receiving the shared
    /// root. Degree-one layouts add only composition metadata here; sumcheck
    /// binds the main circuit statement before its challenges.
    fn absorb_layout(&self, t: &mut TranscriptRef<'_>) {
        self.backend.absorb(t, &self.id);
        t.absorb(|w| {
            w.write_bytes(b"layered-sumcheck/commitment-layout/v1");
            w.write_bytes(&(self.additional_ids.len() as u64).to_le_bytes());
        });
        for id in &self.additional_ids {
            t.absorb(|w| w.write_bytes(id));
        }
        t.absorb(|w| {
            w.write_bytes(&(self.geometry.sc_geom.logw_layers.len() as u64).to_le_bytes())
        });
        for &width in &self.geometry.sc_geom.logw_layers {
            t.absorb(|w| w.write_bytes(&(width as u64).to_le_bytes()));
        }
    }
}
