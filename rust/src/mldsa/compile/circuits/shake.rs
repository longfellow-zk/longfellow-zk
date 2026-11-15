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

//! SHAKE256 using Boolean state bits in characteristic two and signed
//! XOR-basis state bits in odd characteristic.

use crate::{
    circuits::{
        bitvec::{BitvecLogic, V8},
        boolean::Boolean,
        keccak::{ROTC, ROUNDC},
    },
    compile::{
        algebra::CompileField,
        logic::{Eltw, Logic, LogicIO},
    },
    core::algebra::{AlgebraicField, SerializableField},
    mldsa::proto::*,
};

type XorLane<L> = Vec<Eltw<L>>;
type XorState<L> = [[XorLane<L>; 5]; 5];

#[cfg(test)]
mod tests;

pub(crate) struct XorDerived<L: Logic> {
    intermediate_states: Vec<XorState<L>>,
    input_start: usize,
}

pub(crate) struct Shake256Witness<L: Logic> {
    pub permutations: Vec<XorDerived<L>>,
    pub keccak: BinaryKeccak,
}
impl<L: LogicIO> Shake256Witness<L> {
    pub(crate) fn links(&self, _: &L) -> Vec<(Vec<usize>, Vec<usize>)> {
        if !self.keccak.external_permutations {
            return vec![];
        }
        self.permutations
            .iter()
            .map(|p| {
                // Each allocated state is 5 * 5 * 64 contiguous input wires.
                let boundary = p.input_start + 1600;
                (
                    (p.input_start..boundary).collect(),
                    (boundary..boundary + 1600).collect(),
                )
            })
            .collect()
    }
}

pub(crate) fn allocate_witness_with_keccak<L: LogicIO>(
    bitvec: &BitvecLogic<L>,
    position: &mut usize,
    input_len: usize,
    output_len: usize,
    keccak: BinaryKeccak,
) -> Shake256Witness<L> {
    allocate_witness_with_rate(
        bitvec,
        position,
        input_len,
        output_len,
        keccak,
        SHAKE256_RATE,
    )
}
pub(crate) fn allocate_witness_with_rate<L: LogicIO>(
    bitvec: &BitvecLogic<L>,
    position: &mut usize,
    input_len: usize,
    output_len: usize,
    keccak: BinaryKeccak,
    rate: usize,
) -> Shake256Witness<L> {
    let logic = bitvec.logic();
    keccak.validate();
    let count = if logic.field().is_binary() {
        keccak.checkpoint_count()
    } else {
        STATE_ROUNDS.len()
    };
    Shake256Witness {
        keccak,
        permutations: (0..input_len / rate + 1 + output_len.div_ceil(rate).saturating_sub(1))
            .map(|_| {
                let input_start = *position - 1;
                let mut intermediate_states = Vec::with_capacity(count);
                for _ in 0..count {
                    let state = std::array::from_fn(|_| {
                        std::array::from_fn(|_| {
                            (0..64)
                                .map(|_| {
                                    let value = logic.next(position);
                                    // Coordinate equalities inductively force these values to
                                    // be bits. Packed equalities need explicit Booleanity.
                                    if logic.field().is_binary() {
                                        return value;
                                    }
                                    let is_xor_bit = logic.assert0(
                                        "is_xor_bit",
                                        &logic.sub(
                                            &logic.mul(&value, &value),
                                            &if logic.field().is_binary() {
                                                value.clone()
                                            } else {
                                                logic.one()
                                            },
                                        ),
                                    );
                                    logic.with_assertions(is_xor_bit, &value)
                                })
                                .collect()
                        })
                    });
                    intermediate_states.push(state);
                }
                XorDerived {
                    intermediate_states,
                    input_start,
                }
            })
            .collect(),
    }
}

pub(crate) struct Shake256<'a, L: Logic> {
    logic: &'a L,
    bitvec: BitvecLogic<'a, L>,
    boolean: Boolean<'a, L>,
    keccak: BinaryKeccak,
    rate: usize,
}

impl<'a, L: Logic> Shake256<'a, L> {
    pub(crate) fn shake128(logic: &'a L, keccak: BinaryKeccak) -> Self {
        let mut out = Self::with_keccak(logic, keccak);
        out.rate = 168;
        out
    }

    pub(crate) fn with_keccak(logic: &'a L, keccak: BinaryKeccak) -> Self {
        keccak.validate();
        Self {
            logic,
            bitvec: BitvecLogic::new(logic),
            boolean: Boolean::new(logic),
            keccak,
            rate: SHAKE256_RATE,
        }
    }
    fn xor_lane(&self, a: &XorLane<L>, b: &XorLane<L>) -> XorLane<L> {
        a.iter()
            .zip(b)
            .map(|(x, y)| {
                if self.logic.field().is_binary() {
                    self.logic.add(x, y)
                } else {
                    self.logic.mul(x, y)
                }
            })
            .collect()
    }

    fn rotl(&self, amount: usize, a: &XorLane<L>) -> XorLane<L> {
        (0..64)
            .map(|i| a[(i + 64 - amount % 64) % 64].clone())
            .collect()
    }

    fn theta(&self, a: &XorState<L>) -> XorState<L> {
        if self.logic.field().is_binary() && self.keccak.theta_mode != 0 {
            let columns: [XorLane<L>; 5] = std::array::from_fn(|x| {
                (0..64)
                    .map(|bit| {
                        let sum = self
                            .logic
                            .sum(&(0..5).map(|y| a[x][y][bit].clone()).collect::<Vec<_>>());
                        if self.keccak.theta_mode & 1 != 0 {
                            self.logic.precious(&sum)
                        } else {
                            sum
                        }
                    })
                    .collect()
            });
            return std::array::from_fn(|x| {
                let column_delta =
                    self.xor_lane(&columns[(x + 4) % 5], &self.rotl(1, &columns[(x + 1) % 5]));
                let correction: Vec<_> = column_delta
                    .into_iter()
                    .map(|sum| {
                        if self.keccak.theta_mode & 2 != 0 {
                            self.logic.precious(&sum)
                        } else {
                            sum
                        }
                    })
                    .collect();
                std::array::from_fn(|y| self.xor_lane(&a[x][y], &correction))
            });
        }
        let mut c0: [XorLane<L>; 5] = std::array::from_fn(|_| Vec::new());
        let mut c1: [XorLane<L>; 5] = std::array::from_fn(|_| Vec::new());
        for x in 0..5 {
            let a01 = self.xor_lane(&a[x][0], &a[x][1]);
            let a23 = self.xor_lane(&a[x][2], &a[x][3]);
            c0[x] = self.xor_lane(&a01, &a23);
            c1[x] = a[x][4].clone();
        }

        let mut next = a.clone();
        for x in 0..5 {
            let d0 = self.xor_lane(&c0[(x + 4) % 5], &self.rotl(1, &c0[(x + 1) % 5]));
            let d1 = self.xor_lane(&c1[(x + 4) % 5], &self.rotl(1, &c1[(x + 1) % 5]));
            for lane in &mut next[x] {
                *lane = self.xor_lane(lane, &d1);
                *lane = self.xor_lane(lane, &d0);
            }
        }
        next
    }

    fn rho_pi(&self, a: &XorState<L>) -> XorState<L> {
        let mut next: XorState<L> = std::array::from_fn(|_| std::array::from_fn(|_| Vec::new()));
        for x in 0..5 {
            for y in 0..5 {
                next[y][(2 * x + 3 * y) % 5] = self.rotl(ROTC[x][y], &a[x][y]);
            }
        }
        next
    }

    fn chi(&self, a: &XorState<L>) -> XorState<L> {
        let f = self.logic.field();
        if f.is_binary() {
            return std::array::from_fn(|x| {
                std::array::from_fn(|y| {
                    (0..64)
                        .map(|bit| {
                            if self.keccak.expanded_chi {
                                return self.logic.sum(&[
                                    a[x][y][bit].clone(),
                                    a[(x + 2) % 5][y][bit].clone(),
                                    self.logic
                                        .mul(&a[(x + 1) % 5][y][bit], &a[(x + 2) % 5][y][bit]),
                                ]);
                            }
                            self.logic.add(
                                &a[x][y][bit],
                                &self.logic.mul(
                                    &self.logic.add(&self.logic.one(), &a[(x + 1) % 5][y][bit]),
                                    &a[(x + 2) % 5][y][bit],
                                ),
                            )
                        })
                        .collect()
                })
            });
        }
        let two = f.addf(&f.one(), &f.one());
        let half = f.invert(&two);
        std::array::from_fn(|x| {
            std::array::from_fn(|y| {
                (0..64)
                    .map(|bit| {
                        let xx = &a[x][y][bit];
                        let xy = &a[(x + 1) % 5][y][bit];
                        let xz = &a[(x + 2) % 5][y][bit];
                        let w = self.logic.mul(xx, xy);
                        let num = self.logic.sum(&[
                            xx.clone(),
                            self.logic.neg(&w),
                            self.logic.mul(&self.logic.add(xx, &w), xz),
                        ]);
                        self.logic.mulk(&half, &num)
                    })
                    .collect()
            })
        })
    }

    fn round_without_iota(&self, a: &XorState<L>) -> XorState<L> {
        let theta = self.theta(a);
        let rho_pi = self.rho_pi(&theta);
        let precious = std::array::from_fn(|x| {
            std::array::from_fn(|y| {
                rho_pi[x][y]
                    .iter()
                    .map(|bit| self.logic.precious(bit))
                    .collect()
            })
        });
        let mut result = self.chi(&precious);
        if self.logic.field().is_binary() && self.keccak.materialize_chi {
            for bit in result.iter_mut().flatten().flatten() {
                *bit = self.logic.precious(bit);
            }
        }
        result
    }

    fn iota(&self, round: usize, a: &XorState<L>) -> XorState<L> {
        let mut next = a.clone();
        let rc = ROUNDC[round];
        for (bit, value) in next[0][0].iter_mut().enumerate() {
            if (rc >> bit) & 1 != 0 {
                *value = if self.logic.field().is_binary() {
                    self.logic.add(&self.logic.one(), value)
                } else {
                    self.logic.neg(value)
                };
            }
        }
        next
    }

    fn assert_eq_xor_state(&self, expected: &XorState<L>, actual: &XorState<L>) -> L::Assertions {
        let f = self.logic.field();
        if f.is_binary() {
            let expected_bits: Vec<_> = expected.iter().flatten().flatten().collect();
            let actual_bits: Vec<_> = actual.iter().flatten().flatten().collect();
            if !self.keccak.packed_checkpoints {
                return self
                    .logic
                    .assert_mapi("binary_state", 0..expected_bits.len(), |i| {
                        self.logic
                            .assert_eq("bit", expected_bits[i], actual_bits[i])
                    });
            }
            let width = f.pseudo_dimension();
            return self.logic.assert_mapi(
                "binary_state",
                0..expected_bits.len().div_ceil(width),
                |group| {
                    let start = group * width;
                    let end = (start + width).min(expected_bits.len());
                    let terms: Vec<_> = (start..end)
                        .map(|i| {
                            self.logic.mulk(
                                &f.pseudo_basis(i - start),
                                &self.logic.sub(expected_bits[i], actual_bits[i]),
                            )
                        })
                        .collect();
                    self.logic.assert0("packed_bits", &self.logic.sum(&terms))
                },
            );
        }
        let two = f.addf(&f.one(), &f.one());
        let half = f.invert(&two);
        let expected_bits: Vec<_> = expected.iter().flatten().flatten().collect();
        let actual_bits: Vec<_> = actual.iter().flatten().flatten().collect();
        // Each XOR-basis difference divided by two is in {-1, 0, 1}. Thus equality of a
        // 22-bit binary-weighted chunk is equality of the represented integers, whose absolute
        // difference is below q. This matches the C++ SHA3 circuit's 22-bit packed assertions.
        self.logic.assert_mapi(
            "assert_eq_xor_state",
            0..expected_bits.len().div_ceil(22),
            |group| {
                let start = 22 * group;
                let end = (start + 22).min(expected_bits.len());
                let mut weight = half.clone();
                let mut terms = Vec::with_capacity(2 * (end - start));
                for i in start..end {
                    terms.push(self.logic.mulk(&weight, expected_bits[i]));
                    terms.push(self.logic.mulk(&f.neg(&weight), actual_bits[i]));
                    weight = f.mulf(&weight, &two);
                }
                self.logic.assert0("xor_lane", &self.logic.sum(&terms))
            },
        )
    }

    fn permute(
        &self,
        state: &XorState<L>,
        witness: &XorDerived<L>,
    ) -> (XorState<L>, L::Assertions) {
        if self.keccak.external_permutations {
            assert!(self.logic.field().is_binary());
            assert_eq!(witness.intermediate_states.len(), 2);
            return (
                witness.intermediate_states[1].clone(),
                self.assert_eq_xor_state(state, &witness.intermediate_states[0]),
            );
        }
        let binary = self.logic.field().is_binary();
        assert_eq!(
            witness.intermediate_states.len(),
            if binary {
                self.keccak.checkpoint_count()
            } else {
                STATE_ROUNDS.len()
            }
        );
        let mut slice_index = 0;
        let mut curr = state.clone();
        let assertion = self
            .logic
            .assert_mapi("keccak_f_1600_xor", 0..KECCAK_ROUNDS, |round| {
                let expected = self.round_without_iota(&curr);
                if if binary {
                    self.keccak.checkpoint(round)
                } else {
                    STATE_ROUNDS.contains(&round)
                } {
                    let slice = &witness.intermediate_states[slice_index];
                    slice_index += 1;
                    let expected_with_iota = self.iota(round, &expected);
                    let assertion = self.assert_eq_xor_state(&expected_with_iota, slice);
                    curr = slice.clone();
                    assertion
                } else {
                    curr = self.iota(round, &expected);
                    self.logic.ok()
                }
            });
        (curr, assertion)
    }

    fn absorb_block(&self, state: &mut XorState<L>, block: &[V8<L>]) {
        assert_eq!(block.len(), self.rate);
        let f = self.logic.field();
        let mtwo = f.neg(&f.addf(&f.one(), &f.one()));
        for (i, byte) in block.iter().enumerate() {
            let lane = i / 8;
            let x = lane % 5;
            let y = lane / 5;
            let offset = (i % 8) * 8;
            for bit in 0..8 {
                let input = self.boolean.as_eltw(byte.bit(bit));
                if f.is_binary() {
                    state[x][y][offset + bit] = self.logic.add(&state[x][y][offset + bit], &input);
                    continue;
                }
                let input_x = self
                    .logic
                    .sum(&[self.logic.one(), self.logic.mulk(&mtwo, &input)]);
                state[x][y][offset + bit] = self.logic.mul(&state[x][y][offset + bit], &input_x);
            }
        }
    }

    fn squeeze_block(&self, state: &XorState<L>, output: &mut Vec<V8<L>>, remaining: usize) {
        let take = remaining.min(self.rate);
        let f = self.logic.field();
        if f.is_binary() {
            for i in 0..take {
                let lane = i / 8;
                output.push(self.bitvec.from_fn(|bit| {
                    self.boolean.of_eltw_with_assertion(
                        state[lane % 5][lane / 5][(i % 8) * 8 + bit].clone(),
                        self.logic.ok(),
                    )
                }));
            }
            return;
        }
        let two = f.addf(&f.one(), &f.one());
        let half = f.invert(&two);
        let mhalf = f.neg(&half);
        for i in 0..take {
            let lane = i / 8;
            let x = lane % 5;
            let y = lane / 5;
            let offset = (i % 8) * 8;
            output.push(self.bitvec.from_fn(|bit| {
                let standard = self.logic.sum(&[
                    self.logic.konst(&half),
                    self.logic.mulk(&mhalf, &state[x][y][offset + bit]),
                ]);
                self.boolean
                    .of_eltw_with_assertion(standard, self.logic.ok())
            }));
        }
    }

    pub(crate) fn assert_hash(
        &self,
        input: &[V8<L>],
        output_len: usize,
        witness: &Shake256Witness<L>,
    ) -> (Vec<V8<L>>, L::Assertions) {
        assert_eq!(self.keccak, witness.keccak);
        assert_eq!(
            witness.permutations.len(),
            input.len() / self.rate + 1 + output_len.div_ceil(self.rate).saturating_sub(1)
        );
        let mut padded = input.to_vec();
        let padding = self.rate - input.len() % self.rate;
        if padding == 1 {
            padded.push(self.bitvec.of_u64(0x9f));
        } else {
            padded.push(self.bitvec.of_u64(0x1f));
            padded.extend((0..padding - 2).map(|_| self.bitvec.of_u64(0)));
            padded.push(self.bitvec.of_u64(0x80));
        }

        let mut state: XorState<L> = std::array::from_fn(|_| {
            std::array::from_fn(|_| {
                (0..64)
                    .map(|_| {
                        if self.logic.field().is_binary() {
                            self.logic.zero()
                        } else {
                            self.logic.one()
                        }
                    })
                    .collect()
            })
        });
        let mut assertions = Vec::with_capacity(witness.permutations.len());
        let mut permutation = 0;
        for block in padded.chunks_exact(self.rate) {
            self.absorb_block(&mut state, block);
            let (next, assertion) = self.permute(&state, &witness.permutations[permutation]);
            state = next;
            assertions.push(assertion);
            permutation += 1;
        }

        let mut output = Vec::with_capacity(output_len);
        while output.len() < output_len {
            let remaining = output_len - output.len();
            self.squeeze_block(&state, &mut output, remaining);
            if output.len() < output_len {
                let (next, assertion) = self.permute(&state, &witness.permutations[permutation]);
                state = next;
                assertions.push(assertion);
                permutation += 1;
            }
        }
        debug_assert_eq!(permutation, witness.permutations.len());
        (output, self.logic.assert_all("shake256", &assertions))
    }
}
