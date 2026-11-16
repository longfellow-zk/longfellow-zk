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

//! Send the masked sumcheck messages and draw the sumcheck challenges.
//!
//! The statement already holds every circuit ID, layer width and public
//! input (transcript I1, I3), so a sumcheck absorbs only its own messages.
//! Each entry point draws its own top weights (`Schedule::draw_top`) before
//! its first message, from the boundary that the message preceding the
//! frontend closed. The shared schedule
//! treats zero outputs as assertions where they enter, including scalar
//! outputs. Each layer has all its assertion coefficients before any rounds;
//! each round sends both masked coefficients (`SumcheckRound`) before
//! drawing z. The cross coefficient (`SumcheckCross`) precedes the nonzero
//! r, then `end_layer` sends the two masked virtual-circuit factors
//! (`SumcheckClaims`) before drawing alpha, which combines them into one
//! next-layer claim. The same answer then supplies the next stage's
//! coefficients, or the input assertions after the last stage; no stage
//! after the top opens a boundary of its own.

use super::fragments::{ActiveFragment, Schedule};
use crate::{
    core::{
        algebra::{ElementOf, RegisteredField, SerializableField},
        proto::v2::Circuit,
    },
    runtime::{
        algebra::{blas, RuntimeField, SupportsSampling},
        v2::{
            proto::{sumcheck::RoundPoly, tags::Tag},
            transcript::{Encoder, Message, ProverMessage, Reading, TranscriptRef},
        },
    },
};

/// `SumcheckRound` (48): Elements(F, 2), the masked coefficients c0 - s0 and
/// c1 - s1 of one round.
pub(super) struct RoundMessage<'a, F: RegisteredField> {
    pub(super) f: &'a F,
    pub(super) coefficients: &'a [F::E; 2],
}
impl<F: RegisteredField> Message for RoundMessage<'_, F> {
    const TAG: Tag = Tag::SumcheckRound;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.f, self.coefficients);
    }
}
impl<F: RegisteredField> ProverMessage for RoundMessage<'_, F> {}

/// `SumcheckCross` (49): Elements(F, 1), the masked cross coefficient.
pub(super) struct CrossMessage<'a, F: RegisteredField> {
    pub(super) f: &'a F,
    pub(super) cross: &'a F::E,
}
impl<F: RegisteredField> Message for CrossMessage<'_, F> {
    const TAG: Tag = Tag::SumcheckCross;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.f, std::slice::from_ref(self.cross));
    }
}
impl<F: RegisteredField> ProverMessage for CrossMessage<'_, F> {}

/// `SumcheckClaims` (50): Elements(F, 2), the two masked final claims.
pub(super) struct ClaimsMessage<'a, F: RegisteredField> {
    pub(super) f: &'a F,
    pub(super) claims: &'a [F::E; 2],
}
impl<F: RegisteredField> Message for ClaimsMessage<'_, F> {
    const TAG: Tag = Tag::SumcheckClaims;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.f, self.claims);
    }
}
impl<F: RegisteredField> ProverMessage for ClaimsMessage<'_, F> {}

/// Send m = [c0-s0,c1-s1] before drawing the round challenge z.
/// With the pads already committed, fixing both messages determines the
/// quadratic p(x): its third coefficient is c2 = claim - c0.
pub(super) fn round_challenge<F: RuntimeField + RegisteredField + SupportsSampling>(
    m: &RoundPoly<F>,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) -> ElementOf<F> {
    transcript.send(&RoundMessage {
        f,
        coefficients: &m.coefficients,
    });
    transcript.draw(|r| r.elt_field(f))
}

/// Send the masked final claims before drawing alpha for A + alpha*B.
/// Both roles use this step so the layer boundary has one transcript encoding.
/// Input-level zero assertions extend this same answer after alpha is read.
pub(super) fn end_layer<F: RuntimeField + RegisteredField + SupportsSampling>(
    claims: &[F::E; 2],
    transcript: &mut TranscriptRef<'_>,
    f: &F,
    after_alpha: impl FnOnce(&mut Reading<'_>),
) -> F::E {
    transcript.send(&ClaimsMessage { f, claims });
    transcript.draw(|r| {
        let value = r.elt_field(f);
        after_alpha(r);
        value
    })
}

/// Fix d before drawing the nonzero mask scale r. The resulting equation
/// C+r*(d+p_D)+r^2*p_AB=(A+r*p_A)*(B+r*p_B) is affine in committed
/// cells once the masked factors are messages. Excluding zero keeps both masked.
pub(super) fn terminal_challenge<F: RegisteredField + SupportsSampling>(
    cross: &F::E,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) -> F::E {
    transcript.send(&CrossMessage { f, cross });
    transcript.draw(|r| r.nonzero(f))
}

/// The coefficients a stage draws as it enters: one per circuit output that
/// enters at this stage, then each fragment's assertion coefficients. A
/// frontend with no layers instead draws its input assertions as `outputs`.
pub(super) struct StageWeights<E> {
    pub outputs: Vec<E>,
    pub assertions: Vec<Vec<E>>,
}
impl<E> Default for StageWeights<E> {
    fn default() -> Self {
        Self {
            outputs: Vec::new(),
            assertions: Vec::new(),
        }
    }
}

impl Schedule {
    /// Draw the sumcheck's first weights: the entering outputs and assertion
    /// coefficients of its top stage, or the input assertions of a frontend
    /// with no layers. Each entry point draws them itself, before its first
    /// message (transcript I8). The statement holds the circuit list, so this
    /// sends nothing: the draw ends the node of the message that precedes the
    /// frontend, or reads further from its stream (transcript I7).
    pub(super) fn draw_top<F: RuntimeField + SerializableField + SupportsSampling>(
        &self,
        circuits: &[&Circuit<F>],
        t: &mut TranscriptRef<'_>,
        f: &F,
    ) -> StageWeights<F::E> {
        t.draw(|r| {
            if self.layers.is_empty() {
                StageWeights {
                    outputs: self.input_assertions(circuits, r, f),
                    assertions: Vec::new(),
                }
            } else {
                self.draw_stage(0, r, f)
            }
        })
    }
    /// Draw a stage's entering-output coefficients, then its explicit
    /// assertion coefficients: quadratic markers across all fragments, then
    /// linear markers, matching a physically concatenated quad stream. Stage
    /// zero reads them from its own boundary; every later stage reads them
    /// from the preceding stage's combine answer, after alpha.
    pub(super) fn draw_stage<F: RuntimeField + SerializableField + SupportsSampling>(
        &self,
        stage: usize,
        r: &mut Reading<'_>,
        f: &F,
    ) -> StageWeights<F::E> {
        let layout = &self.layers[stage];
        let outputs = (0..layout.output_assertions)
            .map(|_| r.elt_field(f))
            .collect();
        let counts: Vec<_> = layout
            .fragments
            .iter()
            .map(|s| self.assertion_counts(s))
            .collect();
        let mut assertions: Vec<Vec<_>> = counts
            .iter()
            .map(|n| Vec::with_capacity(n.iter().sum()))
            .collect();
        for kind in 0..2 {
            for (a, n) in assertions.iter_mut().zip(&counts) {
                a.extend((0..n[kind]).map(|_| r.elt_field(f)));
            }
        }
        StageWeights {
            outputs,
            assertions,
        }
    }
    /// Circuit outputs are zero assertions at the stage where they enter:
    /// extend the carried weights with their coefficients and give each
    /// fragment its assertion coefficients.
    pub(super) fn enter<E>(
        &self,
        stage: usize,
        drawn: StageWeights<E>,
        weights: &mut Vec<E>,
        active: &mut [ActiveFragment<'_, E>],
    ) {
        let layout = &self.layers[stage];
        assert_eq!(weights.len(), layout.nv - layout.output_assertions);
        weights.extend(drawn.outputs);
        assert_eq!(drawn.assertions.len(), active.len());
        for (a, w) in active.iter_mut().zip(drawn.assertions) {
            a.assertions = w;
        }
    }
    /// Extend stage `stage`'s combine answer after alpha: the next stage's
    /// weights, or the input assertions after the last stage.
    pub(super) fn after_combine<F: RuntimeField + SerializableField + SupportsSampling>(
        &self,
        stage: usize,
        circuits: &[&Circuit<F>],
        r: &mut Reading<'_>,
        f: &F,
        next: &mut StageWeights<F::E>,
        input_assertions: &mut Vec<F::E>,
    ) {
        if stage + 1 == self.layers.len() {
            *input_assertions = self.input_assertions(circuits, r, f);
        } else {
            *next = self.draw_stage(stage + 1, r, f);
        }
    }
    /// Zero-layer circuits assert directly on the common input array. For a
    /// layered proof these coefficients extend the last combine answer, after
    /// both masked claims; with no layers they are the top weights.
    pub(super) fn input_assertions<F: RuntimeField + SerializableField + SupportsSampling>(
        &self,
        circuits: &[&Circuit<F>],
        r: &mut Reading<'_>,
        f: &F,
    ) -> Vec<F::E> {
        let mut weights = Vec::new();
        for c in circuits {
            if c.raw.layers.is_empty() {
                if weights.is_empty() {
                    weights.resize(self.ninput, f.zero());
                }
                // A zero-layer component asserts only on its own input prefix.
                for a in &mut weights[..c.raw.ninput] {
                    f.add(a, &r.elt_field(f));
                }
            }
        }
        weights
    }
    /// Add the last combine's input assertions to the final input weights.
    /// With no layers the top weights already are the input weights.
    pub(super) fn finish_inputs<F: RuntimeField + SerializableField>(
        &self,
        weights: &mut [F::E],
        input_assertions: Vec<F::E>,
        f: &F,
    ) {
        if !input_assertions.is_empty() {
            blas::add(weights, &input_assertions, f);
        }
        assert_eq!(weights.len(), self.ninput);
    }
}
