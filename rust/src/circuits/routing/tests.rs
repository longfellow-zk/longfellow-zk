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
        bitvec::{Bitvec, BitvecLogic},
        boolean::{Bitw, Boolean},
        routing::Routing,
    },
    compile::{
        algebra::{p256::P256Field, CompileField},
        logic::{AssertionScope, EvalLogic, Logic},
    },
    core::algebra::{AlgebraicField, SupportsNatConversions, SupportsU64Conversions},
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

fn amount_bitvec<L: Logic>(boolean: &Boolean<'_, L>, amount: usize) -> Bitvec<L, 8> {
    Bitvec::new(
        int_to_bits(amount, 8)
            .into_iter()
            .map(|b| if b { boolean.trueb() } else { boolean.falseb() })
            .collect(),
    )
}

/// The reference result: `a` shifted left by `amount`, zero-filled.
fn shifted(a: &[u8], amount: usize, k: usize) -> Vec<u8> {
    (0..k)
        .map(|i| a.get(i + amount).copied().unwrap_or(0))
        .collect()
}

const GROUPINGS: [&[usize]; 7] = [
    &[4],
    &[1, 3],
    &[2, 2],
    &[3, 1],
    &[1, 1, 1, 1],
    &[2, 1],
    &[1],
];

#[test]
#[should_panic(expected = "shift groups must be nonempty and have positive widths")]
fn grouped_shift_rejects_empty_schedule() {
    let f = P256Field::new();
    let tracker = AssertionScope::new();
    let logic = EvalLogic::new(&f, &tracker);
    let bv = BitvecLogic::new(&logic);
    let routing = Routing::new(&logic);
    routing.shift_bitvec_grouped(&[], &bv.of_u8(1), 1, &[bv.of_u8(42)]);
}

#[test]
fn test_shift_bitvec_grouped() {
    let f = P256Field::new();
    let tracker = AssertionScope::new();
    let iologic = EvalLogic::new(&f, &tracker);
    let boolean = Boolean::new(&iologic);
    let bv = BitvecLogic::new(&iologic);
    let routing = Routing::new(&iologic);
    for groups in GROUPINGS {
        let total: usize = groups.iter().sum();
        for n in 1..=1 << total {
            let a_vals: Vec<u8> = (0..n).map(|i| (i * 37 + 5) as u8).collect();
            let a: Vec<_> = a_vals.iter().map(|&v| bv.of_u8(v)).collect();
            for k in 1..=n + 2 {
                // Amounts beyond `1 << total` exercise the high-bit check.
                for amount in 0..=(1 << total) + 3 {
                    let res = routing.shift_bitvec_grouped(
                        groups,
                        &amount_bitvec(&boolean, amount),
                        k,
                        &a,
                    );
                    let got: Vec<u8> = res
                        .iter()
                        .map(|r| {
                            (0..8)
                                .filter(|&j| boolean.as_eltw(r.bit(j)).value == f.one())
                                .fold(0u8, |acc, j| acc | 1 << j)
                        })
                        .collect();
                    assert_eq!(
                        got,
                        shifted(&a_vals, amount, k),
                        "groups={groups:?} n={n} k={k} amount={amount}"
                    );
                }
            }
        }
    }
}

#[test]
fn test_shift_eltw_grouped() {
    let f = P256Field::new();
    let tracker = AssertionScope::new();
    let iologic = EvalLogic::new(&f, &tracker);
    let boolean = Boolean::new(&iologic);
    let routing = Routing::new(&iologic);
    for groups in GROUPINGS {
        let total: usize = groups.iter().sum();
        for n in 1..=1 << total {
            let a_vals: Vec<u8> = (0..n).map(|i| (i * 37 + 5) as u8).collect();
            let a: Vec<_> = a_vals
                .iter()
                .map(|&v| iologic.konst(&f.u64_to_element(v.into())))
                .collect();
            for k in 1..=n + 2 {
                for amount in 0..=(1 << total) + 3 {
                    let res =
                        routing.shift_eltw_grouped(groups, &amount_bitvec(&boolean, amount), k, &a);
                    let want: Vec<_> = shifted(&a_vals, amount, k)
                        .into_iter()
                        .map(|v| f.u64_to_element(v.into()))
                        .collect();
                    let got: Vec<_> = res.into_iter().map(|r| r.value).collect();
                    assert_eq!(got, want, "groups={groups:?} n={n} k={k} amount={amount}");
                }
            }
        }
    }
}
