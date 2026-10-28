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

//! Bind the public statement and masked messages, then sample sumcheck challenges.
//!
//! The statement binds the trusted circuit ID and public inputs. `begin` then
//! samples weights for the circuit outputs. Each layer samples its assertion
//! coefficients before any rounds; each round absorbs both masked coefficients
//! before sampling z. `end_layer` absorbs the final-claim pair before sampling
//! alpha, which combines those two claims for the next layer.

use crate::{
    core::{
        algebra::SerializableField,
        proto::{circuit::Circuit, Layer},
    },
    runtime::{
        algebra::{ElementOf, RuntimeField, SupportsSampling},
        random::{RandomEngine, Transcript},
        sumcheck_v2::{monomial, RoundPoly},
    },
};

/// Bind the public sumcheck statement before sampling protocol challenges.
pub(crate) trait TranscriptSumcheck {
    /// Absorb the trusted circuit ID, its public inputs, the zero-output claim,
    /// and protocol padding. The caller supplies exactly npublic_input values.
    fn write_sumcheck_statement<const W: usize, F: RuntimeField<W> + SerializableField>(
        &mut self,
        circuit: &Circuit<F>,
        public_inputs: &[ElementOf<F>],
        f: &F,
    );
}

impl TranscriptSumcheck for Transcript {
    fn write_sumcheck_statement<const W: usize, F: RuntimeField<W> + SerializableField>(
        &mut self,
        circuit: &Circuit<F>,
        public_inputs: &[ElementOf<F>],
        f: &F,
    ) {
        assert_eq!(
            public_inputs.len(),
            circuit.raw.npublic_input,
            "Public inputs length mismatch: expected {}, got {}",
            circuit.raw.npublic_input,
            public_inputs.len()
        );
        self.write_bytes(&circuit.id);

        // The circuit ID binds the number of individually encoded public inputs.
        for input in public_inputs {
            self.write_elt_field(input, f);
        }

        // The circuit statement requires all outputs to be zero.
        self.write_elt_field(&f.zero(), f);

        // Transcript padding for correlation intractability: one zero byte per term.
        let nterms = circuit
            .raw
            .layers
            .iter()
            .map(crate::core::proto::Layer::num_terms)
            .sum::<usize>();
        self.write0(nterms);
    }
}

/// Start the sumcheck transcript domain and return the initial output weights a.
/// Sample the logv coordinates of u and form a[g] = product_j u[j]^g_j.
/// A scalar output has logv=0 and weight one, so it consumes no field challenges.
pub(super) fn begin<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    circuit: &Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> Vec<F::E> {
    assert!(crate::runtime::sumcheck_v2::sane_logw(circuit.raw.logv));
    transcript.write_bytes(b"longfellow-sumcheck-v2-projective");
    let point_g = transcript.elt_field_slice(circuit.raw.logv, f);
    monomial::weights(circuit.raw.logv, circuit.raw.noutput, &point_g, f)
}

/// Sample one replacement coefficient for every zero-coefficient quad, in
/// circuit traversal order. The prover reuses this sequence in both quad bindings.
/// Each coefficient replaces the full a[g]*QUAD[g,l,r] factor for its assertion.
pub(super) fn assertion_weights<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    layer: &Layer<F>,
    constants: &[F::E],
    layer_index: usize,
    transcript: &mut Transcript,
    f: &F,
) -> Vec<F::E> {
    transcript.write_bytes(b"single-hand-assertions");
    transcript.write_bytes(&(layer_index as u64).to_le_bytes());
    let mut assertions = Vec::new();
    layer.for_each_term(constants, |term| {
        if f.is_zero(&term.k) {
            assertions.push(transcript.elt_field(f));
        }
    });
    assertions
}

/// Absorb m = [c0-s0,c1-s1] before sampling the round challenge z.
/// With the pads already committed, fixing both messages determines the
/// quadratic p(x): its third coefficient is c2 = claim - c0.
pub(super) fn round_challenge<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    m: &RoundPoly<W, F>,
    transcript: &mut Transcript,
    f: &F,
) -> ElementOf<F> {
    for coefficient in &m.coefficients {
        transcript.write_elt_field(coefficient, f);
    }
    transcript.elt_field(f)
}

/// Bind the masked final claims before sampling alpha for A + alpha*B.
/// Both roles use this step so the layer boundary has one transcript encoding.
pub(super) fn end_layer<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    claims: &[F::E; 2],
    transcript: &mut Transcript,
    f: &F,
) -> F::E {
    transcript.write_elt_field_slice(claims, f);
    transcript.write_bytes(b"single-hand-combine");
    transcript.elt_field(f)
}
