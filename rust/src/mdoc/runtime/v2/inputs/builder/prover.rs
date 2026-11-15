// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{AssignmentBuilder, BinaryAssignmentBuilder};
use crate::{
    circuits::{
        ecdsa2::{Derived, Given},
        sha256msg,
    },
    core::algebra::Nat,
    mdoc::{proto::layout, v2::MdocProverErrorCode},
    runtime::algebra::p256::P256Element,
};
impl AssignmentBuilder<'_> {
    pub(in crate::mdoc::runtime::v2::inputs) fn push_ecdsa_signature(
        &mut self,
        given: &Given<P256Element>,
        r_range: &core::ops::Range<usize>,
        ers_range: &core::ops::Range<usize>,
    ) -> Result<(), MdocProverErrorCode> {
        layout::check_at(self.buffer.len(), r_range, "signature R")
            .map_err(|_| MdocProverErrorCode::WitnessCreationFailure)?;
        // Key coordinates and digest bits already occupy the shared prefix.
        given.for_each_signature(|elt| self.push_elt(elt));
        layout::check_at(
            self.buffer.len(),
            &(ers_range.end..ers_range.end),
            "end of signature ERS",
        )
        .map_err(|_| MdocProverErrorCode::WitnessCreationFailure)?;
        Ok(())
    }

    pub(in crate::mdoc::runtime::v2::inputs) fn push_ecdsa_derived(
        &mut self,
        derived: &Derived<P256Element>,
    ) {
        derived.for_each(|elt| self.push_elt(elt));
    }
}

impl BinaryAssignmentBuilder {
    fn push_v32(&mut self, val: u32) {
        self.push_bits_len(u64::from(val), 32);
    }

    pub(in crate::mdoc::runtime::v2::inputs) fn push_nat256<N: Nat<4>>(&mut self, nat: &N) {
        for limb in nat.to_limbs() {
            self.push_bits_len(limb, 64);
        }
    }

    pub(in crate::mdoc::runtime::v2::inputs) fn push_sha256msg_derived(
        &mut self,
        derived: &sha256msg::Derived<u32>,
    ) {
        derived.for_each(|&val| self.push_v32(val));
    }
}
