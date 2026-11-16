// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The decoding of a sumcheck proof, which every proof role runs.
use super::{
    super::read_field, invalid, LayerProof, RoundPoly, SumcheckProof, SumcheckProofGeometry,
};
use crate::core::algebra::SerializableField;

impl<F: SerializableField> SumcheckProof<F> {
    /// A component reader, called only by the complete readers (proto I2).
    pub(crate) fn read(
        bytes: &mut &[u8],
        geometry: &SumcheckProofGeometry,
        f: &F,
    ) -> std::io::Result<Self> {
        if f.serialized_size_bytes() == 0 {
            return Err(invalid("zero field encoding width"));
        }
        let size = geometry
            .serialized_elements()
            .checked_mul(f.serialized_size_bytes())
            .ok_or_else(|| invalid("sumcheck byte size overflow"))?;
        if bytes.len() < size {
            return Err(invalid("truncated sumcheck proof"));
        }
        let mut layers = Vec::with_capacity(geometry.logw_layers.len());
        for &logw in &geometry.logw_layers {
            let mut rounds = Vec::with_capacity(logw);
            for _ in 0..logw {
                rounds.push(RoundPoly {
                    coefficients: [read_field(bytes, f)?, read_field(bytes, f)?],
                });
            }
            layers.push(LayerProof {
                rounds,
                cross: read_field(bytes, f)?,
                claims: [read_field(bytes, f)?, read_field(bytes, f)?],
            });
        }
        Ok(Self { layers })
    }
}
