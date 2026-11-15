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
use crate::{
    circuits::{
        bitvec::Bitvec,
        boolean::{Bitw, Boolean},
        routing::Routing,
    },
    compile::{
        algebra::{p256::P256Field, CompileField},
        logic::{AssertionScope, EvalLogic},
    },
    core::algebra::SupportsNatConversions,
};

fn int_to_bits(val: usize, bits: usize) -> Vec<bool> {
    (0..bits).map(|i| ((val >> i) & 1) == 1).collect()
}

fn run_eval_test_bitvec_generic<const W: usize, F: CompileField + SupportsNatConversions<W>>(
    f: &F,
    logn: usize,
    n: usize,
    k: usize,
    shift: usize,
    unroll: usize,
) {
    let tracker = AssertionScope::new();
    let iologic = EvalLogic::new(f, &tracker);
    let boolean = Boolean::new(&iologic);
    let routing = Routing::new(&iologic);

    // amount bits
    let amount_bits_bool = int_to_bits(shift, logn);
    let amount_bits: Vec<Bitw<_>> = amount_bits_bool
        .into_iter()
        .map(|b| if b { boolean.trueb() } else { boolean.falseb() })
        .collect();
    let amount_bitvec = Bitvec::<_, 16>::new({
        let mut bits = amount_bits;
        bits.resize_with(16, || boolean.falseb());
        bits
    });

    // inputs
    let a_vals: Vec<u8> = (0..n).map(|i| (i + 42) as u8).collect();
    let a_wires: Vec<Bitvec<_, 8>> = a_vals
        .iter()
        .map(|&val| {
            let mut bits = Vec::new();
            for i in 0..8 {
                bits.push(if ((val >> i) & 1) == 1 {
                    boolean.trueb()
                } else {
                    boolean.falseb()
                });
            }
            Bitvec::new(bits)
        })
        .collect();

    let default_val = 123u8;
    let default_wire = Bitvec::new({
        let mut bits = Vec::new();
        for i in 0..8 {
            bits.push(if ((default_val >> i) & 1) == 1 {
                boolean.trueb()
            } else {
                boolean.falseb()
            });
        }
        bits
    });

    let res = routing.shift_bitvec(unroll, &amount_bitvec, k, &a_wires, &default_wire);

    let real_shift = shift % (1 << logn);
    for i in 0..k {
        let expected = if i + real_shift < n {
            a_vals[i + real_shift]
        } else {
            default_val
        };

        let mut got_val = 0u8;
        for j in 0..8 {
            let bit_val = boolean.as_eltw(res[i].bit(j));
            if bit_val.value == f.one() {
                got_val |= 1 << j;
            }
        }
        assert_eq!(got_val, expected);
    }
}

#[test]
fn test_routing_evaluation() {
    let f = P256Field::new();
    // Run small test suite similar to OCaml test_small
    for logn in 1..=4 {
        for n in 1..=8 {
            for k in 1..=8 {
                for shift in 0..=8 {
                    for unroll in 1..=4 {
                        run_eval_test_bitvec_generic::<4, _>(&f, logn, n, k, shift, unroll);
                    }
                }
            }
        }
    }
}
