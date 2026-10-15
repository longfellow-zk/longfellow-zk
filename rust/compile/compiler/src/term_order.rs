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

//! Compile-time traversal policy for the ordinary LFC2 delta/segment encoding.
//!
//! Separate constant, linear, square, and product terms, then visit outputs in
//! descending order, h1 descending, h0 ascending, coefficient bytes ascending.
//! Separating these shapes keeps fixed-One coordinates and square diagonals from
//! interrupting translated product runs. Output-major order keeps each gate's
//! terms together within a shape. No wire renaming, templates or runtime sorting
//! are involved; equal input pairs and equal g need not be globally contiguous.

use std::cmp::Reverse;

use compile_algebra::field::CompileField;
use core_proto::Term;

fn kind<F: CompileField>(term: &Term<F>, ones: &[bool]) -> u8 {
    match (ones[term.h0 as usize], ones[term.h1 as usize]) {
        (true, true) => 0,
        (true, false) | (false, true) => 1,
        (false, false) if term.h0 == term.h1 => 2,
        (false, false) => 3,
    }
}

/// Reorders terms only, returning conservative constant values for the next layer.
/// A None output stays unknown if any contributing term is unknown or is a
/// zero-coefficient assertion marker. No witness values participate in layout.
pub(crate) fn order_layer<F: CompileField>(
    f: &F,
    terms: &mut [Term<F>],
    known_inputs: &[Option<F::E>],
    noutput: usize,
) -> Vec<Option<F::E>> {
    let mut known_outputs = vec![Some(f.zero()); noutput];
    for t in terms.iter() {
        let output = &mut known_outputs[t.g as usize];
        if let Some(value) = output {
            match (&known_inputs[t.h0 as usize], &known_inputs[t.h1 as usize]) {
                (Some(a), Some(b)) if !f.is_zero(&t.k) => {
                    f.add(value, &f.mulf(&t.k, &f.mulf(a, b)));
                }
                _ => *output = None,
            }
        }
    }
    let one = f.one();
    let ones: Vec<_> = known_inputs
        .iter()
        .map(|v| v.as_ref() == Some(&one))
        .collect();
    terms.sort_unstable_by(|a, b| {
        (kind(a, &ones), Reverse(a.g), Reverse(a.h1), a.h0)
            .cmp(&(kind(b, &ones), Reverse(b.g), Reverse(b.h1), b.h0))
            .then_with(|| f.to_bytes(&a.k).cmp(&f.to_bytes(&b.k)))
    });
    known_outputs
}

#[cfg(test)]
mod tests {
    use super::*;
    use compile_algebra::p256::P256Field;
    use core_algebra::{AlgebraicField, SupportsU64Conversions};
    use core_proto::compare_term;

    #[test]
    fn shape_then_output_order_preserves_every_term_and_is_deterministic() {
        let f = P256Field::new();
        // At this internal layer One is wire 7; wire 0 is not a constant.
        let mut known = vec![None; 9];
        known[7] = Some(f.one());
        let coordinates = [
            (1, 2, 4),
            (0, 0, 0),
            (0, 7, 7),
            (2, 3, 7),
            (2, 2, 4),
            (2, 1, 4),
            (2, 1, 3),
            (1, 5, 5),
        ];
        let mut original: Vec<_> = coordinates
            .into_iter()
            .map(|(g, h0, h1)| Term {
                g,
                h0,
                h1,
                k: f.one(),
            })
            .collect();
        let mut sorted = original.clone();
        order_layer(&f, &mut sorted, &known, 3);
        assert_eq!(
            sorted.iter().map(|t| (t.g, t.h0, t.h1)).collect::<Vec<_>>(),
            [
                (0, 7, 7),
                (2, 3, 7),
                (1, 5, 5),
                (0, 0, 0),
                (2, 1, 4),
                (2, 2, 4),
                (2, 1, 3),
                (1, 2, 4),
            ]
        );
        let mut reversed = original.clone();
        reversed.reverse();
        order_layer(&f, &mut reversed, &known, 3);
        assert_eq!(reversed, sorted);
        original.sort_by(|a, b| compare_term(&f, a, b));
        sorted.sort_by(|a, b| compare_term(&f, a, b));
        assert_eq!(original, sorted);
    }

    #[test]
    fn propagates_one_copies_and_constant_expressions_but_not_assertion_markers() {
        let f = P256Field::new();
        let mut terms = vec![
            Term {
                g: 0,
                h0: 0,
                h1: 0,
                k: f.one(),
            },
            Term {
                g: 1,
                h0: 0,
                h1: 0,
                k: f.u64_to_element(2),
            },
            Term {
                g: 1,
                h0: 0,
                h1: 0,
                k: f.mone(),
            },
            Term {
                g: 2,
                h0: 0,
                h1: 0,
                k: f.zero(),
            },
            Term {
                g: 3,
                h0: 0,
                h1: 1,
                k: f.one(),
            },
        ];
        let known = order_layer(&f, &mut terms, &[Some(f.one()), None], 4);
        assert_eq!(known, [Some(f.one()), Some(f.one()), None, None]);
        let mut copies = vec![
            Term {
                g: 0,
                h0: 1,
                h1: 1,
                k: f.one(),
            },
            Term {
                g: 1,
                h0: 0,
                h1: 1,
                k: f.one(),
            },
        ];
        assert_eq!(
            order_layer(&f, &mut copies, &known, 2),
            [Some(f.one()), Some(f.one())]
        );
    }
}
