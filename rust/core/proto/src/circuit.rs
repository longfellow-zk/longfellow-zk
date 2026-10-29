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

use std::fmt;

use sha2::{Digest, Sha256};

pub use crate::core::algebra::SerializableField;

pub type DigestBytes = [u8; 32];

pub use crate::core::proto::layer::{canonical_term, compare_term, Layer, Term, TermDelta};

pub struct RawCircuit<F: SerializableField, L = Layer<F>> {
    pub ninput: usize,
    pub npublic_input: usize,
    pub noutput: usize,
    pub logv: usize,
    pub subfield_boundary: usize,
    pub constants: Vec<F::E>,
    pub layers: Vec<L>,
}

pub struct Circuit<F: SerializableField, L = Layer<F>> {
    pub raw: RawCircuit<F, L>,
    pub id: DigestBytes,
}
impl<F: SerializableField> Circuit<F> {
    /// Rows are quadratic, linear, constant; columns are zero, one, other.
    pub fn term_breakdown(&self, f: &F) -> [[usize; 3]; 3]
    where F: crate::core::algebra::AlgebraicField {
        let mut counts = [[0; 3]; 3];
        let one = f.one();
        for layer in &self.raw.layers {
            for (degree, stream) in layer.streams().enumerate() {
                if let Some(c) = stream.coefficients() {
                    counts[degree][0] += c.assertions.num_terms();
                    counts[degree][1] += c.units.num_terms();
                    counts[degree][2] += c.negatives.num_terms();
                    stream.for_each_delta_index(|_| counts[degree][2] += 1);
                } else {
                    stream.for_each_general_term(&self.raw.constants, |t| {
                        let class = if f.is_zero(&t.k) {
                            0
                        } else if t.k == one {
                            1
                        } else {
                            2
                        };
                        counts[degree][class] += 1;
                    });
                }
            }
        }
        counts
    }

    /// Decoded circuit allocation capacity; witnesses and prover scratch are separate.
    pub fn heap_bytes(&self) -> usize {
        self.raw.constants.capacity() * std::mem::size_of::<F::E>()
            + self.raw.layers.capacity() * std::mem::size_of::<Layer<F>>()
            + self.raw.layers.iter().map(Layer::heap_bytes).sum::<usize>()
    }
}

impl<F: SerializableField, L> Circuit<F, L> {
    /// V1 file metadata remains readable; V2 commits ambient-field cells only.
    pub fn validate_v2(&self) -> Result<(), String> {
        if self.raw.subfield_boundary != 0 {
            return Err("V2 requires subfield_boundary = 0".into());
        }
        Ok(())
    }
}

fn update8(hasher: &mut Sha256, val: usize) {
    hasher.update((val as u64).to_le_bytes());
}

pub fn compute_id<F: SerializableField>(f: &F, raw: &RawCircuit<F>) -> DigestBytes {
    let mut hasher = Sha256::new();
    if f.is_binary() {
        hasher.update(2u64.to_le_bytes());
        hasher.update(((f.serialized_size_bytes() * 8) as u64).to_le_bytes());
    } else {
        hasher.update(1u64.to_le_bytes());
        hasher.update(f.serialized_mone());
    }

    update8(&mut hasher, raw.noutput);
    update8(&mut hasher, raw.logv);
    update8(&mut hasher, 1); // ncopies
    update8(&mut hasher, 0); // logc
    update8(&mut hasher, raw.layers.len());
    update8(&mut hasher, raw.ninput);
    update8(&mut hasher, raw.npublic_input);
    update8(&mut hasher, raw.subfield_boundary);

    let const_bytes: Vec<Vec<u8>> = raw.constants.iter().map(|c| f.to_bytes(c)).collect();
    let mut buf = [0u8; 8192];
    let mut buf_len = 0;

    for layer in &raw.layers {
        let l_nums = [layer.nw as u64, layer.logw as u64, layer.num_terms() as u64];
        for &val in &l_nums {
            if buf_len + 8 > buf.len() {
                hasher.update(&buf[..buf_len]);
                buf_len = 0;
            }
            buf[buf_len..buf_len + 8].copy_from_slice(&val.to_le_bytes());
            buf_len += 8;
        }

        let mut prev_g = 0u32;
        let mut prev_h0 = 0u32;
        let mut prev_h1 = 0u32;

        layer.for_each_delta_index(|d_idx| {
            let d = &layer.deltas[d_idx as usize];
            let g = prev_g.wrapping_add(d.g);
            let h0 = prev_h0.wrapping_add(d.h[0]);
            let h1 = prev_h1.wrapping_add(d.h[1]);

            let cb = &const_bytes[d.k_index as usize];
            if buf_len + 24 + cb.len() > buf.len() {
                hasher.update(&buf[..buf_len]);
                buf_len = 0;
            }

            buf[buf_len..buf_len + 8].copy_from_slice(&u64::from(g).to_le_bytes());
            buf[buf_len + 8..buf_len + 16].copy_from_slice(&u64::from(h0).to_le_bytes());
            buf[buf_len + 16..buf_len + 24].copy_from_slice(&u64::from(h1).to_le_bytes());
            buf_len += 24;

            if cb.len() > buf.len() {
                if buf_len > 0 {
                    hasher.update(&buf[..buf_len]);
                    buf_len = 0;
                }
                hasher.update(cb);
            } else {
                buf[buf_len..buf_len + cb.len()].copy_from_slice(cb);
                buf_len += cb.len();
            }

            prev_g = g;
            prev_h0 = h0;
            prev_h1 = h1;
        });
    }

    if buf_len > 0 {
        hasher.update(&buf[..buf_len]);
    }

    let result = hasher.finalize();
    let mut digest = [0u8; 32];
    digest.copy_from_slice(&result);
    digest
}

impl<F: SerializableField> fmt::Debug for RawCircuit<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawCircuit")
            .field("ninput", &self.ninput)
            .field("npublic_input", &self.npublic_input)
            .field("noutput", &self.noutput)
            .field("logv", &self.logv)
            .field("constants_len", &self.constants.len())
            .field("layers", &self.layers)
            .field("subfield_boundary", &self.subfield_boundary)
            .finish()
    }
}

impl<F: SerializableField> fmt::Debug for Circuit<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Circuit")
            .field("raw", &self.raw)
            .field("id", &self.id)
            .finish()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldID {
    None = 0,
    P256 = 1,
    P384 = 2,
    P521 = 3,
    Gf2_128 = 4,
    Gf2_16 = 5,
    Fp128 = 6,
    Fp64 = 7,
    Goldi = 8,
    Fp64_2 = 9,
    Secp = 10,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CircuitGeometry {
    pub ninput: usize,
    pub npublic_input: usize,
    pub noutput: usize,
    pub nwires: usize,
    pub nterms: usize,
    pub nlayers: usize,
    pub nassertions: usize,
}
