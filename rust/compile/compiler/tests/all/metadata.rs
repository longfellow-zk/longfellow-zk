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

use crate::compile::{
    algebra::p256::P256Field,
    logic::{Logic, LogicIO},
};

#[test]
#[should_panic(expected = "source public-input boundary must be at least 1")]
fn test_rejects_no_public_inputs() {
    compile_with_metadata(0, 0);
}

#[test]
#[should_panic(expected = "npublic_input (2) exceeds ninput (1)")]
fn test_rejects_too_many_public_inputs() {
    compile_with_metadata(3, 0);
}

#[test]
#[should_panic(expected = "subfield_boundary (2) exceeds ninput (1)")]
fn test_rejects_subfield_boundary_past_inputs() {
    compile_with_metadata(1, 3);
}

fn compile_with_metadata(npublic_input: usize, subfield_boundary: usize) {
    let f = P256Field::new();
    super::compile(&f, |logic| {
        let x = logic.input(1);
        let square = logic.mul(&x, &x);
        let assertion = logic.assert0("square", &square);
        (assertion, npublic_input, subfield_boundary)
    });
}
