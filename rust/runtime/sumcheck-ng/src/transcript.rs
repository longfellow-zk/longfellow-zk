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

use crate::proof::RoundPoly;
use core_algebra::SerializableField;
use core_proto::circuit::Circuit;
use runtime_algebra::{field::RuntimeField, ElementOf, SupportsSampling};
use runtime_random::{RandomEngine, Transcript};

use crate::MAX_LOGW;

/// Extension trait that adds sumcheck-specific helpers to the cryptographic Transcript.
pub trait TranscriptSumcheck {
    /// Writes the sumcheck statement and public parameters to the transcript.
    fn write_sumcheck_statement<const W: usize, F: RuntimeField<W> + SerializableField>(
        &mut self,
        circuit: &Circuit<F>,
        public_inputs: &[ElementOf<F>],
        f: &F,
    );
    /// Writes a round polynomial to the transcript and samples a challenge.
    fn round<const W: usize, F: SerializableField + SupportsSampling<W>>(
        &mut self,
        poly: &RoundPoly<W, F>,
        f: &F,
    ) -> ElementOf<F>;
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

        // Public inputs.  This is a quirk in the spec, we should
        // write PUB_INPUTS as an array with a different tag instead
        // of individual field elements.  This is not a soundness problem
        // because npublic_input is part of the circuit id, which we
        // have already hashed.
        for inp in public_inputs.iter().take(circuit.raw.npublic_input) {
            self.write_elt_field(inp, f);
        }

        // Outputs pro-forma:
        self.write_elt_field(&f.zero(), f);

        // Enough zeroes for correlation intractability, one byte per term.
        let nterms = circuit
            .raw
            .layers
            .iter()
            .map(core_proto::Layer::num_terms)
            .sum::<usize>();
        self.write0(nterms);
    }

    fn round<const W: usize, F: SerializableField + SupportsSampling<W>>(
        &mut self,
        poly: &RoundPoly<W, F>,
        f: &F,
    ) -> ElementOf<F> {
        for value in &poly.evaluations {
            self.write_elt_field(value, f);
        }
        self.elt_field(f)
    }
}

pub fn begin<const W: usize, F: RuntimeField<W> + SupportsSampling<W> + SerializableField>(
    circuit: &Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> Vec<F::E> {
    transcript.write_bytes(b"longfellow-sumcheck-single-hand-v1");
    // Retain the v1 protocol's discarded copy-query samples.
    for _ in 0..MAX_LOGW {
        transcript.elt_field(f);
    }
    let point = transcript.elt_field_slice(MAX_LOGW, f);
    crate::eq::weights(circuit.raw.logv, circuit.raw.noutput, &point, f)
}

pub fn assertion_weights<const W: usize, F: SupportsSampling<W>>(
    outputs: &[bool],
    layer: usize,
    transcript: &mut Transcript,
    f: &F,
) -> Vec<F::E> {
    transcript.write_bytes(b"single-hand-assertions");
    transcript.write_bytes(&(layer as u64).to_le_bytes());
    outputs
        .iter()
        .map(|&assertion| {
            if assertion {
                transcript.elt_field(f)
            } else {
                f.zero()
            }
        })
        .collect()
}

pub fn combine<const W: usize, F: SupportsSampling<W> + SerializableField>(
    endpoints: &[F::E; 2],
    transcript: &mut Transcript,
    f: &F,
) -> F::E {
    transcript.write_elt_field_slice(endpoints, f);
    transcript.write_bytes(b"single-hand-combine");
    transcript.elt_field(f)
}
