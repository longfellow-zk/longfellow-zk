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

//! Experimental composition of bit-input GKR, ring switching and Polygero.
//! Circuit inputs are logical bits. Full-field auxiliaries belong to the caller
//! and enter only explicit affine claims; they never become circuit inputs.
pub use crate::runtime::proto::packed_zk::{
    PackedLayout as PackedCommitmentLayout, PackedZkProof as Proof,
};
use crate::{
    core::proto::circuit::Circuit,
    runtime::{
        algebra::{
            gf2_128::{Gf2_128 as E, Gf2_128Field as F},
            AlgebraicField, EvaluationDomain,
        },
        polygero::{PolygeroConfig, PolygeroLinearTerm, PolygeroParam},
        proto::{
            packed_zk::{PackedLayout, PackedZkProof},
            sumcheck_v2::CircuitPadLayout,
            zk_v2::ZkProofGeometry,
        },
        random::{RandomEngine, Transcript},
        ring_switch::{AffineClaim, BitLinearClaim, PackedLinearClaim, RING_MASK_CELLS},
        sumcheck_v2::{self, symbolic::Constraints, TranscriptSumcheck},
        zk_v2::ZkContext,
    },
};

/// A public bit-linear equation whose affine terms refer only to caller cells.
/// Multiple equations are combined using independent challenges after GKR.
#[derive(Clone, Debug)]
pub struct AuxiliaryBitClaim {
    pub weights: Vec<E>,
    pub rhs: AffineClaim,
}
pub struct PackedCircuit {
    circuit: Circuit<F>,
    config: PolygeroConfig,
    layout: PackedLayout,
    contract: [u8; 32],
    basis: crate::runtime::ring_switch::field::PolynomialBasis128,
    boolean_window: Option<usize>,
}
impl PackedCircuit {
    /// The caller authenticates the bit-domain contract together with the circuit.
    pub fn new(
        circuit: Circuit<F>,
        config: PolygeroConfig,
        auxiliary: usize,
        contract: [u8; 32],
    ) -> Result<Self, String> {
        let (layout, _, _) = PackedLayout::new(&circuit, auxiliary)?;
        if circuit.raw.layers.is_empty() {
            return Err("packed circuit needs a layer".into());
        }
        Ok(Self {
            circuit,
            config,
            layout,
            contract,
            basis: crate::runtime::ring_switch::field::PolynomialBasis128::new(&F::new()),
            boolean_window: None,
        })
    }
    /// Select an explicit numerical kernel; the verifier and transcript are unchanged.
    pub fn with_boolean_window(mut self, window: usize) -> Result<Self, String> {
        if !(1..=4).contains(&window) {
            return Err("Boolean window must be 1 through 4".into());
        }
        self.boolean_window = Some(window);
        Ok(self)
    }
    pub fn layout(&self) -> &PackedLayout {
        &self.layout
    }
    pub fn public_input_count(&self) -> usize {
        self.circuit.raw.npublic_input
    }
    fn prepare<D: EvaluationDomain<2, F>>(
        &self,
        ctx: &ZkContext<'_, 2, F, D>,
    ) -> Result<(ZkProofGeometry, PolygeroParam), String> {
        let (_, sc_geom, products) =
            PackedLayout::new(&self.circuit, self.layout.caller_auxiliary)?;
        let param = PolygeroParam::try_new(
            self.layout.witness_count,
            &products,
            self.config,
            ctx.domain,
            ctx.f,
        )
        .map_err(|e| e.to_string())?;
        Ok((
            ZkProofGeometry {
                sc_geom,
                com_geom: param.geometry(),
            },
            param,
        ))
    }
    fn bind_commitment(&self, t: &mut Transcript) {
        t.write_bytes(b"longfellow/packed-zk128/flat/v1");
        t.write_bytes(&self.circuit.id);
        t.write_bytes(&self.contract);
        t.write_bytes(&(self.layout.private_bits as u64).to_le_bytes());
        t.write_bytes(&(self.layout.caller_auxiliary as u64).to_le_bytes());
    }
    fn validate(&self, public: &[E], extra: &[AuxiliaryBitClaim]) -> Result<(), String> {
        if public.len() != self.public_input_count() {
            return Err("packed public input count mismatch".into());
        }
        if public.iter().any(|x| x.to_u128() > 1) {
            return Err("packed public input is not a bit".into());
        }
        for e in extra {
            if e.weights.len() != self.layout.private_bits
                || e.rhs
                    .terms
                    .iter()
                    .any(|&(i, _)| i >= self.layout.caller_auxiliary)
            {
                return Err("packed auxiliary claim shape mismatch".into());
            }
        }
        Ok(())
    }
    fn bind_statement(&self, public: &[E], extra: &[AuxiliaryBitClaim], t: &mut Transcript, f: &F) {
        t.write_sumcheck_statement(&self.circuit, public, f);
        t.write_bytes(b"packed/caller-claims");
        t.write_bytes(&(extra.len() as u64).to_le_bytes());
        for e in extra {
            t.write_elt_field_slice(&e.weights, f);
            t.write_elt_field(&e.rhs.constant, f);
            t.write_bytes(&(e.rhs.terms.len() as u64).to_le_bytes());
            for &(i, k) in &e.rhs.terms {
                t.write_bytes(&(i as u64).to_le_bytes());
                t.write_elt_field(&k, f);
            }
        }
    }
    fn claim(
        &self,
        c: &Constraints<E>,
        public: &[E],
        extra: &[AuxiliaryBitClaim],
        pads: &CircuitPadLayout,
        t: &mut Transcript,
        f: &F,
    ) -> Result<BitLinearClaim, String> {
        let mut rhs = AffineClaim {
            constant: c.input_claim.constant,
            terms: Vec::new(),
        };
        for (a, x) in c.input_weights.iter().zip(public) {
            f.add(&mut rhs.constant, &f.mulf(a, x))
        }
        for &(p, k) in &c.input_claim.terms {
            let w = super::constraint_compiler::pad_coordinate(p, pads)?;
            rhs.terms
                .push((w - self.layout.packed_words - RING_MASK_CELLS, k));
        }
        let mut weights = c.input_weights[public.len()..].to_vec();
        t.write_bytes(b"packed/caller-combination");
        for e in extra {
            let lambda = E::from(t.u128());
            for (a, k) in weights.iter_mut().zip(&e.weights) {
                f.add(a, &f.mulf(&lambda, k))
            }
            f.add(&mut rhs.constant, &f.mulf(&lambda, &e.rhs.constant));
            rhs.terms
                .extend(e.rhs.terms.iter().map(|&(i, k)| (i, f.mulf(&lambda, &k))));
        }
        Ok(BitLinearClaim {
            weights,
            rhs,
            auxiliary_count: self.layout.witness_count - self.layout.packed_words - RING_MASK_CELLS,
        })
    }
    fn compile(
        &self,
        c: &Constraints<E>,
        _public: &[E],
        pads: &CircuitPadLayout,
        ring: &PackedLinearClaim,
        f: &F,
    ) -> Result<(Vec<PolygeroLinearTerm<E>>, Vec<E>), String> {
        let (mut a, mut b) = super::constraint_compiler::compile_layers(c, pads, f)?;
        let row = b.len();
        b.push(f.addf(&ring.rhs.constant, &ring.offset));
        for (w, &k) in ring.weights.iter().enumerate() {
            a.push(PolygeroLinearTerm { c: row, w, k })
        }
        for &(i, k) in &ring.rhs.terms {
            let w = if i < self.layout.caller_auxiliary {
                self.layout.packed_words + i
            } else {
                self.layout.packed_words + i + RING_MASK_CELLS
            };
            a.push(PolygeroLinearTerm { c: row, w, k });
        }
        for (i, &k) in ring.mask_weights.iter().enumerate() {
            a.push(PolygeroLinearTerm {
                c: row,
                w: self.layout.ring_start + i,
                k,
            })
        }
        a.push(PolygeroLinearTerm {
            c: row,
            w: self.layout.ring_start + RING_MASK_CELLS - 1,
            k: ring.checksum_weight,
        });
        Ok((a, b))
    }
}

cfg_prover! {
    #[path = "packed_prover.rs"]
    mod prover;
    pub use prover::PackedCommitment;
}
cfg_verifier! {
    #[path = "packed_verifier.rs"]
    mod verifier;
    pub use verifier::PackedVerifier;
}

#[cfg(test)]
#[path = "../tests/packed.rs"]
mod tests;
