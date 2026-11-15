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
use super::read_field;
use crate::{
    core::algebra::{ElementOf, SerializableField},
    runtime::v2::proto::util::write_elt_field,
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
    /// Masked cross coefficient, fixed before the terminal mask scale is sampled.
    pub cross: F::E,
    /// Two factors for the complete virtual layer: `sum_l m_l[l] W[l]` and
    /// `sum_{g,l,r} a[g] QUAD[g,l,r] m_l[l] W[r] + L(u)`,
    /// with the terminal challenge times their respective pads added. Here `g` ranges over
    /// outputs, and `l,r` range over input wires, with m_l[l] = product_j u[j]^l_j;
    /// assertion terms use their replacement coefficients. L(u) is the public
    /// linear-coefficient contraction at u, removed when combining the claims.
    pub claims: [ElementOf<F>; 2],
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumcheckProof<const W: usize, F: SerializableField> {
    pub layers: Vec<LayerProof<W, F>>,
}
/// The round count of each layer, outputs to inputs. Every value is valid:
/// each count is at most `MAX_LOGW` and the pad and element counts fit
/// `usize` (proto I8).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumcheckProofGeometry {
    logw_layers: Vec<usize>,
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
#[derive(Clone, Debug)]
pub(crate) struct LayerPadLayout {
    pub(crate) rounds: Vec<[usize; 2]>,
    pub(crate) claims: [usize; 2],
    pub(crate) product: usize,
    pub(crate) cross: usize,
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
#[derive(Clone, Debug)]
pub(crate) struct CircuitPadLayout {
    pub(crate) layers: Vec<LayerPadLayout>,
}

/// Two pads per round, two terminal pads, p_AB, and an independent cross pad.
pub const fn pad_count(logw: usize) -> usize {
    assert!(sane_logw(logw), "sumcheck logw exceeds MAX_LOGW");
    2 * logw + 4
}
fn invalid(message: &str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, message)
}
impl SumcheckProofGeometry {
    /// The geometry of layers with these round counts, if every count is at
    /// most `MAX_LOGW` and the pad count fits `usize`.
    pub fn new(logw_layers: Vec<usize>) -> std::io::Result<Self> {
        logw_layers.iter().try_fold(0usize, |total, &logw| {
            if !sane_logw(logw) {
                return Err(invalid("sumcheck logw exceeds MAX_LOGW"));
            }
            total
                .checked_add(pad_count(logw))
                .ok_or_else(|| invalid("sumcheck size overflow"))
        })?;
        Ok(Self { logw_layers })
    }

    /// The round count of each layer, outputs to inputs.
    pub fn layers(&self) -> &[usize] {
        &self.logw_layers
    }

    /// Committed pads: `2 logw + 4` per layer (`pad_count`).
    pub fn pad_count(&self) -> usize {
        self.logw_layers.iter().map(|&logw| pad_count(logw)).sum()
    }

    /// Two coefficients per round, one cross coefficient, and two final claims per layer.
    pub fn serialized_elements(&self) -> usize {
        self.logw_layers.iter().map(|&logw| 2 * logw + 3).sum()
    }
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn pad_layout(&self, base: usize) -> CircuitPadLayout {
        base.checked_add(self.pad_count())
            .expect("sumcheck pad layout overflow");
        let layers: Vec<_> = self
            .logw_layers
            .iter()
            .scan(base, |next, &logw| {
                let count = pad_count(logw);
                let start = *next;
                *next += count;
                let terminal = *next - 4;
                let rounds = (0..logw)
                    .map(|round| [start + 2 * round, start + 2 * round + 1])
                    .collect();
                Some(LayerPadLayout {
                    rounds,
                    claims: [terminal, terminal + 1],
                    product: terminal + 2,
                    cross: terminal + 3,
                })
            })
            .collect();
        CircuitPadLayout { layers }
    }
}
impl<const W: usize, F: SerializableField> SumcheckProof<W, F> {
    /// The geometry of this proof's shape, if it is a valid one.
    pub fn geometry(&self) -> std::io::Result<SumcheckProofGeometry> {
        SumcheckProofGeometry::new(self.layers.iter().map(|layer| layer.rounds.len()).collect())
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
        Ok(())
    }
    pub fn read(
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
            write_elt_field(bytes, &layer.cross, f);
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
