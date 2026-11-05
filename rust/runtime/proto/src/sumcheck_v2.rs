// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Longfellow v2 sumcheck proof types and wire encoding.

//! Single-hand messages, codec, and committed-pad positions.
use crate::{
    core::algebra::{ElementOf, SerializableField},
    runtime::proto::util::{read_elt_field, write_elt_field},
};

/// Maximum rounds in one serialized v2 layer. This wire-format limit is
/// independent of the host's index width and of Fiat–Shamir sampling counts.
/// The codec stores O(logw) messages; circuit execution checks its own capacity.
pub const MAX_LOGW: usize = 40;

/// Whether a round count fits the v2 proof format, independently of the host.
pub const fn sane_logw(logw: usize) -> bool {
    logw <= MAX_LOGW
}

/// Two masked coefficients of p(x) = c0 + c1*x + c2*x^2.
/// The incoming claim determines c2 = claim - c0; only c0 and c1 are transmitted.
#[derive(Debug, PartialEq, Eq)]
pub struct RoundPoly<const W: usize, F: SerializableField> {
    pub coefficients: [F::E; 2],
}
impl<const W: usize, F: SerializableField> Clone for RoundPoly<W, F> {
    fn clone(&self) -> Self {
        Self {
            coefficients: self.coefficients.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LayerProof<const W: usize, F: SerializableField> {
    pub rounds: Vec<RoundPoly<W, F>>,
    /// `sum_l m_l[l] W[l]` and
    /// `sum_{g,l,r} a[g] QUAD[g,l,r] m_l[l] W[r]`,
    /// with their respective pads subtracted. Here `g` ranges over outputs,
    /// and `l,r` range over input wires, with m_l[l] = product_j u[j]^l_j;
    /// assertion quads use their replacement coefficients.
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
}

/// Two pads per round, two final-claim pads, and their committed product.
pub const fn pad_count(logw: usize) -> usize {
    assert!(sane_logw(logw), "sumcheck logw exceeds MAX_LOGW");
    2 * logw + 3
}
fn invalid(message: &str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, message)
}
impl SumcheckProofGeometry {
    pub fn from_circuit<F: SerializableField>(
        circuit: &crate::core::proto::v2::Circuit<F>,
    ) -> Self {
        Self {
            logw_layers: circuit
                .raw
                .layers
                .iter()
                .map(crate::core::proto::v2::Layer::logw)
                .collect(),
        }
    }
    /// Two coefficients per round and two final claims per layer are transmitted.
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
    /// Positions of the two final-claim pads and their product in each layer.
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
        CircuitPadLayout { layers }
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
                    coefficients: [read_elt_field(bytes, f)?, read_elt_field(bytes, f)?],
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
                for elt in &round.coefficients {
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
