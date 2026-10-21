// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

//! Single-hand messages, codec, and committed-pad positions.
use crate::util::{read_elt_field, write_elt_field};
use core_algebra::{ElementOf, SerializableField};
pub use core_proto::{sane_logw, MAX_LOGW};

#[derive(Debug, PartialEq, Eq)]
pub struct RoundPoly<const W: usize, F: SerializableField> {
    pub evaluations: [F::E; 2],
}
impl<const W: usize, F: SerializableField> Clone for RoundPoly<W, F> {
    fn clone(&self) -> Self {
        Self {
            evaluations: self.evaluations.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LayerProof<const W: usize, F: SerializableField> {
    pub rounds: Vec<RoundPoly<W, F>>,
    /// W(u) and (M W)(u), with their respective pads subtracted.
    pub claims: [ElementOf<F>; 2],
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumcheckProof<const W: usize, F: SerializableField> {
    pub layers: Vec<LayerProof<W, F>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumcheckProofGeometry {
    pub logw_layers: Vec<usize>,
}
#[derive(Clone, Debug)]
pub struct LayerPadLayout {
    pub rounds: Vec<[usize; 2]>,
    pub claims: [usize; 3],
}
#[derive(Clone, Debug)]
pub struct CircuitPadLayout {
    pub layers: Vec<LayerPadLayout>,
    pub size: usize,
}

/// Two pads per round, two endpoint pads, and their committed product.
pub const fn pad_count(logw: usize) -> usize {
    2 * logw + 3
}
fn invalid(message: &str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, message)
}
impl SumcheckProofGeometry {
    pub fn from_circuit<F: SerializableField>(circuit: &core_proto::circuit::Circuit<F>) -> Self {
        Self {
            logw_layers: circuit
                .raw
                .layers
                .iter()
                .map(core_proto::Layer::logw)
                .collect(),
        }
    }
    /// Two evaluations per round and two endpoint claims are transmitted.
    pub fn serialized_elements(&self) -> std::io::Result<usize> {
        self.logw_layers.iter().try_fold(0usize, |total, &logw| {
            if !sane_logw(logw) {
                return Err(invalid("sumcheck logw exceeds MAX_LOGW"));
            }
            total
                .checked_add(2 * logw + 2)
                .ok_or_else(|| invalid("sumcheck size overflow"))
        })
    }
    /// Endpoint pad positions, without allocating per-round layouts.
    pub fn claim_indices(&self, base: usize) -> impl Iterator<Item = [usize; 3]> + '_ {
        self.logw_layers.iter().scan(base, |next, &logw| {
            assert!(sane_logw(logw));
            let claims = *next + pad_count(logw) - 3;
            *next = claims + 3;
            Some([claims, claims + 1, claims + 2])
        })
    }
    pub fn pad_layout(&self, base: usize) -> CircuitPadLayout {
        let layers: Vec<_> = self
            .logw_layers
            .iter()
            .zip(self.claim_indices(base))
            .map(|(&logw, claims)| {
                let start = claims[0] - 2 * logw;
                let rounds = (0..logw)
                    .map(|round| [start + 2 * round, start + 2 * round + 1])
                    .collect();
                LayerPadLayout { rounds, claims }
            })
            .collect();
        let size = layers.last().map_or(0, |layer| layer.claims[2] + 1 - base);
        CircuitPadLayout { layers, size }
    }
}
impl<const W: usize, F: SerializableField> SumcheckProof<W, F> {
    pub fn geometry(&self) -> SumcheckProofGeometry {
        SumcheckProofGeometry {
            logw_layers: self.layers.iter().map(|layer| layer.rounds.len()).collect(),
        }
    }
    pub fn validate(&self, geometry: &SumcheckProofGeometry) -> std::io::Result<()> {
        if self.layers.len() != geometry.logw_layers.len()
            || !self
                .layers
                .iter()
                .zip(&geometry.logw_layers)
                .all(|(layer, &logw)| layer.rounds.len() == logw)
        {
            return Err(invalid("sumcheck shape mismatch"));
        }
        geometry.serialized_elements()?;
        Ok(())
    }
    pub fn read(
        bytes: &mut &[u8],
        geometry: &SumcheckProofGeometry,
        f: &F,
    ) -> std::io::Result<Self> {
        let size = geometry
            .serialized_elements()?
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
                    evaluations: [read_elt_field(bytes, f)?, read_elt_field(bytes, f)?],
                });
            }
            layers.push(LayerProof {
                rounds,
                claims: [read_elt_field(bytes, f)?, read_elt_field(bytes, f)?],
            });
        }
        Ok(Self { layers })
    }
    pub fn write_to_buf(
        &self,
        bytes: &mut Vec<u8>,
        geometry: &SumcheckProofGeometry,
        f: &F,
    ) -> std::io::Result<()> {
        self.validate(geometry)?;
        for layer in &self.layers {
            for round in &layer.rounds {
                for elt in &round.evaluations {
                    write_elt_field(bytes, elt, f);
                }
            }
            for claim in &layer.claims {
                write_elt_field(bytes, claim, f);
            }
        }
        Ok(())
    }
    pub fn write(&self, geometry: &SumcheckProofGeometry, f: &F) -> std::io::Result<Vec<u8>> {
        let mut bytes = Vec::new();
        self.write_to_buf(&mut bytes, geometry, f)?;
        Ok(bytes)
    }
}
