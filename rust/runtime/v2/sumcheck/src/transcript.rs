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
//! The caller binds every trusted circuit ID and the shared public inputs.
//! The shared schedule treats zero outputs as assertions where they enter,
//! including scalar outputs. Each layer samples all its assertion
//! coefficients before any rounds; each round absorbs both masked coefficients
//! before sampling z. Bind the cross coefficient before sampling nonzero r,
//! then `end_layer` absorbs the two masked virtual-circuit factors before sampling
//! alpha, which combines them into one next-layer claim.

use super::{circuit::CircuitSource, fragments::SplitFragment};
use crate::{
    core::{algebra::SerializableField, proto::v2::Circuit},
    runtime::{
        algebra::{blas, ElementOf, RuntimeField, SupportsSampling},
        v2::{
            proto::RoundLabel,
            sumcheck::RoundPoly,
            transcript::{Reading, TranscriptRef},
        },
    },
};

/// Bind the public sumcheck statement before sampling protocol challenges.
pub(crate) trait TranscriptSumcheck {
    /// Absorb the trusted circuit ID, its public inputs, and the zero-output
    /// claim. The caller supplies exactly npublic_input values.
    fn write_sumcheck_statement<const W: usize, F: RuntimeField<W> + SerializableField>(
        &mut self,
        circuit: &Circuit<F>,
        public_inputs: &[ElementOf<F>],
        f: &F,
    );
}

impl TranscriptSumcheck for TranscriptRef<'_> {
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
        self.absorb(|w| {
            w.write_bytes(&circuit.id);
            // The circuit ID binds the number of individually encoded public inputs.
            for input in public_inputs {
                w.write_elt_field(input, f);
            }
            // The circuit statement requires all outputs to be zero.
            w.write_elt_field(&f.zero(), f);
        });
    }
}

/// Absorb m = [c0-s0,c1-s1] before sampling the round challenge z.
/// With the pads already committed, fixing both messages determines the
/// quadratic p(x): its third coefficient is c2 = claim - c0.
pub(super) fn round_challenge<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    m: &RoundPoly<W, F>,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) -> ElementOf<F> {
    transcript.round(RoundLabel::Sumcheck, |mut w| {
        for c in &m.coefficients {
            w.write_elt_field(c, f);
        }
        let mut r = w.begin_squeeze();
        let value = r.elt_field(f);
        r.end_round(value)
    })
}

/// Bind the masked final claims before sampling alpha for A + alpha*B.
/// Both roles use this step so the layer boundary has one transcript encoding.
/// Input-level zero assertions extend this same answer after alpha is read.
pub(super) fn end_layer<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    claims: &[F::E; 2],
    transcript: &mut TranscriptRef<'_>,
    f: &F,
    after_alpha: impl FnOnce(&mut crate::runtime::v2::transcript::Reading<'_>),
) -> F::E {
    transcript.round(RoundLabel::Combine, |mut w| {
        w.write_elt_field_slice(claims, f);
        let mut r = w.begin_squeeze();
        let value = r.elt_field(f);
        after_alpha(&mut r);
        r.end_round(value)
    })
}

/// Fix d before sampling the nonzero mask scale r. The resulting equation
/// C+r*(d+p_D)+r^2*p_AB=(A+r*p_A)*(B+r*p_B) is affine in committed
/// cells once the masked factors are messages. Excluding zero keeps both masked.
pub(super) fn terminal_challenge<F: SerializableField + SupportsSampling>(
    cross: &F::E,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) -> F::E {
    transcript.round(RoundLabel::Terminal, |mut w| {
        w.write_elt_field(cross, f);
        let mut r = w.begin_squeeze();
        let value = loop {
            let x = r.elt_field(f);
            if !f.is_zero(&x) {
                break x;
            }
        };
        r.end_round(value)
    })
}

impl super::fragments::Schedule {
    pub(super) fn absorb<F: SerializableField>(
        &self,
        circuits: &[impl CircuitSource<F>],
        t: &mut TranscriptRef<'_>,
    ) {
        t.absorb(|w| {
            w.write_bytes(b"layered-sumcheck/circuits/v1");
            w.write_bytes(&(circuits.len() as u64).to_le_bytes());
        });
        for c in circuits {
            t.absorb(|w| {
                match c.source_id() {
                    Some(id) => w.write_bytes(id),
                    None => w.write_bytes(b"layered-sumcheck/derived-circuit/v1"),
                }
                w.write_bytes(&(c.raw().layers.len() as u64).to_le_bytes());
            });
        }
    }
    /// Circuit outputs are zero assertions at the layer where they enter.
    /// Draw their coefficients and all explicit assertion coefficients from
    /// this one answer, after the preceding layer's claims have been bound.
    pub(super) fn start_layer<
        const W: usize,
        F: RuntimeField<W> + SerializableField + SupportsSampling,
    >(
        &self,
        weights: &mut Vec<F::E>,
        active: &mut [SplitFragment<'_, F::E>],
        stage: usize,
        t: &mut TranscriptRef<'_>,
        f: &F,
    ) {
        let layout = &self.layers[stage];
        assert_eq!(weights.len(), layout.nv - layout.output_assertions);
        t.round(RoundLabel::Assertions, |mut w| {
            w.write_bytes(&(stage as u64).to_le_bytes());
            let mut r = w.begin_squeeze();
            weights.extend((0..layout.output_assertions).map(|_| r.elt_field(f)));
            assertion_weights(active, &mut r, f);
            r.end_round(())
        });
    }
    /// Zero-layer circuits assert directly on the common input array. For a
    /// layered proof these coefficients extend the last combine answer, after
    /// both masked claims. No extra boundary or future coefficient is needed.
    pub(super) fn input_assertions<
        const W: usize,
        F: RuntimeField<W> + SerializableField + SupportsSampling,
    >(
        &self,
        circuits: &[impl CircuitSource<F>],
        r: &mut Reading<'_>,
        f: &F,
    ) -> Vec<F::E> {
        let mut weights = Vec::new();
        for c in circuits {
            if c.raw().layers.is_empty() {
                if weights.is_empty() {
                    weights.resize(self.ninput, f.zero());
                }
                for a in &mut weights {
                    f.add(a, &r.elt_field(f));
                }
            }
        }
        weights
    }
    /// A proof with no layers still needs one fresh assertion block on its
    /// inputs. Otherwise the input assertions already share the last combine.
    pub(super) fn finish_inputs<
        const W: usize,
        F: RuntimeField<W> + SerializableField + SupportsSampling,
    >(
        &self,
        circuits: &[impl CircuitSource<F>],
        weights: &mut Vec<F::E>,
        input_assertions: Vec<F::E>,
        t: &mut TranscriptRef<'_>,
        f: &F,
    ) {
        if self.layers.is_empty() {
            *weights = t.round(RoundLabel::Assertions, |mut w| {
                w.write_bytes(&0u64.to_le_bytes());
                let mut r = w.begin_squeeze();
                let a = self.input_assertions(circuits, &mut r, f);
                r.end_round(a)
            });
        } else if !input_assertions.is_empty() {
            blas::add(weights, &input_assertions, f);
        }
        assert_eq!(weights.len(), self.ninput);
    }
}

/// Read quadratic markers across all fragments, then linear markers, matching
/// a physically concatenated quad stream. The layer's entering outputs have
/// already been read from this same answer. Local slices serve only the sparse
/// contractions; neither a fragment nor a marker class starts another round.
pub(super) fn assertion_weights<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    active: &mut [SplitFragment<'_, F::E>],
    r: &mut Reading<'_>,
    f: &F,
) {
    for kind in 0..2 {
        for a in active.iter_mut() {
            a.assertions
                .extend((0..a.layer.assertion_counts()[kind]).map(|_| r.elt_field(f)));
        }
    }
}
