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

use compile_algebra::p256::P256Field;
use core_algebra::AlgebraicField;
use core_proto::{compare_term, Term};

#[test]
fn lexicographic_order_is_translation_invariant_and_groups_input_pairs() {
    let f = P256Field::new();
    // Morton changes the order of (0, 3) and (2, 2) after translation by (1, 1).
    // g is only a tie-breaker within an input pair, not the primary sort key.
    let coordinates = [(2, 2, 0), (0, 3, 8), (0, 3, 1), (1, 4, 2)];
    for offset in [0, 1, 3, 7, 16, 31] {
        let mut terms: Vec<_> = coordinates
            .iter()
            .map(|&(h0, h1, g)| Term {
                h0: h0 + offset,
                h1: h1 + offset,
                g: g + offset,
                k: f.one(),
            })
            .collect();
        terms.sort_by(|a, b| compare_term(&f, a, b));
        let local: Vec<_> = terms
            .iter()
            .map(|t| (t.h0 - offset, t.h1 - offset, t.g - offset))
            .collect();
        assert_eq!(local, [(0, 3, 1), (0, 3, 8), (1, 4, 2), (2, 2, 0)]);
    }
}
