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

use super::*;
use crate::{
    core::proto::{
        circuit::{compute_id, RawCircuit},
        Layer, TermDelta,
    },
    runtime::algebra::{gf2_128::Gf2_128Field, AlgebraicField},
};

#[test]
fn evaluation_failures_do_not_disclose_witness_values() {
    use crate::core::algebra::SupportsU128Conversions;
    let f = Gf2_128Field::new();
    let raw = RawCircuit {
        ninput: 3,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        subfield_boundary: 0,
        constants: vec![f.zero()],
        layers: vec![Layer::new_compressed(
            3,
            2,
            vec![vec![TermDelta {
                g: 0,
                h: [1, 2],
                k_index: 0,
            }]],
            vec![0],
        )],
    };
    let circuit = Circuit {
        id: compute_id(&f, &raw),
        raw,
    };
    for secret in [17, 0x12345678, 0xabcdef01] {
        let inputs = vec![
            f.one(),
            f.u128_to_element(secret),
            f.u128_to_element(secret + 1),
        ];
        let message = sumcheck_v2::eval_circuit(inputs, &circuit, &f).unwrap_err();
        assert_eq!(message, "Witness does not satisfy circuit constraints at layer 0: gate multiplication constraint not satisfied: wire_l=1, wire_r=2");
    }
}
