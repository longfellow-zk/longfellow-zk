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

//! SHAKE256 sponge constraints and native witness construction for ML-DSA.

use circuits_bit_plucker::BitPlucker;
use circuits_bitvec::{BitvecLogic, V8};
use circuits_boolean::Boolean;
use compile_algebra::AlgebraicField;
use compile_logic::{Eltw, Logic, LogicIO};

use crate::sha3::{self, ConcreteDerived};

pub const SHAKE256_RATE: usize = 136;
const KECCAK_ROUNDS: usize = 24;
// Shared MLDSA-44/65 policy selected by the hand-major size/proof sweep: isolate
// round 0, then retain the regular four-round cuts. Direct XOR-basis state bits
// avoid the high-degree lookup polynomials needed to unpack packed witnesses.
const SLICE_PERIOD: usize = 4;
const FIRST_ROUND_SLICE: bool = true;

#[derive(Clone, Copy, Debug)]
struct SliceConfig {
    period: usize,
    first: bool,
    bits: usize,
}

fn slice_config() -> SliceConfig {
    #[cfg(feature = "mldsa-slicing-experiment")]
    {
        // Immutable for the life of this experiment process. Compilation and
        // native witness generation must use the same schedule. Default builds
        // do not consult the environment and use the selected fixed policy.
        static CONFIG: std::sync::OnceLock<SliceConfig> = std::sync::OnceLock::new();
        *CONFIG.get_or_init(|| {
            let period = std::env::var("MLDSA_SLICE_PERIOD")
                .map(|s| {
                    s.parse::<usize>()
                        .expect("MLDSA_SLICE_PERIOD must be an integer")
                })
                .unwrap_or(SLICE_PERIOD);
            assert!(
                (1..=6).contains(&period),
                "MLDSA_SLICE_PERIOD must be 1..=6"
            );
            let first = match std::env::var("MLDSA_FIRST_ROUND").as_deref() {
                Ok("0") => false,
                Ok("1") => true,
                Err(std::env::VarError::NotPresent) => FIRST_ROUND_SLICE,
                _ => panic!("MLDSA_FIRST_ROUND must be 0 or 1"),
            };
            let bits = std::env::var("MLDSA_PLUCKER_BITS")
                .map(|s| {
                    s.parse::<usize>()
                        .expect("MLDSA_PLUCKER_BITS must be an integer")
                })
                .unwrap_or(0);
            assert!(bits <= 6, "MLDSA_PLUCKER_BITS must be 0..=6");
            SliceConfig {
                period,
                first,
                bits,
            }
        })
    }
    #[cfg(not(feature = "mldsa-slicing-experiment"))]
    {
        SliceConfig {
            period: SLICE_PERIOD,
            first: FIRST_ROUND_SLICE,
            bits: 0,
        }
    }
}

pub fn slice_period() -> usize {
    slice_config().period
}
pub fn first_round_slice() -> bool {
    slice_config().first
}
/// Zero means direct XOR-basis witnesses; 1..=6 selects the maximum packed
/// width. Each lane's plucker widths are balanced to differ by at most one.
pub fn plucker_bits() -> usize {
    slice_config().bits
}

// Use the minimum number of witnesses for the requested maximum width, then
// balance their widths within one bit. Put the larger chunks first. Both the
// circuit and native witness encoder use this exact partition of each lane.
fn lane_chunks(bits: usize) -> Vec<(usize, usize)> {
    if bits == 0 {
        return Vec::new();
    }
    let count = 64usize.div_ceil(bits);
    let small = 64 / count;
    let large_count = 64 % count;
    let mut offset = 0;
    (0..count)
        .map(|i| {
            let width = small + usize::from(i < large_count);
            let chunk = (offset, width);
            offset += width;
            chunk
        })
        .collect()
}

const fn count_slices(period: usize, first: bool) -> usize {
    KECCAK_ROUNDS.div_ceil(period) + (first && period != 1) as usize
}

fn slice_count() -> usize {
    count_slices(slice_period(), first_round_slice())
}

const fn slice_round(round: usize, period: usize, first: bool) -> bool {
    let completed_rounds = round + 1;
    (first && round == 0)
        || completed_rounds == KECCAK_ROUNDS
        || completed_rounds.is_multiple_of(period)
}

fn is_slice_round(round: usize) -> bool {
    slice_round(round, slice_period(), first_round_slice())
}

#[cfg(test)]
mod slice_tests {
    use super::*;

    #[test]
    #[cfg(not(feature = "mldsa-slicing-experiment"))]
    fn default_build_uses_unpacked_period_four_with_first_cut() {
        assert_eq!(slice_period(), 4);
        assert!(first_round_slice());
        assert_eq!(plucker_bits(), 0);
        let cuts: Vec<_> = (0..KECCAK_ROUNDS).filter(|&r| is_slice_round(r)).collect();
        assert_eq!(cuts, [0, 3, 7, 11, 15, 19, 23]);
        assert_eq!(slice_count(), 7);
    }

    #[test]
    fn packed_lanes_are_complete_minimal_and_balanced() {
        assert!(lane_chunks(0).is_empty());
        for bits in 1..=6 {
            let chunks = lane_chunks(bits);
            assert_eq!(chunks.len(), 64usize.div_ceil(bits));
            assert_eq!(chunks[0].0, 0);
            assert_eq!(chunks.last().map(|&(o, w)| o + w), Some(64));
            assert!(chunks.windows(2).all(|w| w[0].0 + w[0].1 == w[1].0));
            let widths: Vec<_> = chunks.iter().map(|&(_, w)| w).collect();
            assert!(*widths.iter().min().unwrap() > 0);
            assert!(*widths.iter().max().unwrap() <= bits);
            assert!(widths.iter().max().unwrap() - widths.iter().min().unwrap() <= 1);
        }
        assert_eq!(
            lane_chunks(6).iter().map(|c| c.1).collect::<Vec<_>>(),
            [6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5]
        );
    }

    #[test]
    fn optional_first_cut_preserves_all_period_six_cuts() {
        for first in [false, true] {
            let actual: Vec<_> = (0..KECCAK_ROUNDS)
                .filter(|&r| slice_round(r, 6, first))
                .collect();
            let expected = if first {
                vec![0, 5, 11, 17, 23]
            } else {
                vec![5, 11, 17, 23]
            };
            assert_eq!(actual, expected);
            assert_eq!(actual.len(), count_slices(6, first));
        }
    }

    #[test]
    fn every_sweep_schedule_has_one_first_cut_and_no_oversized_chunk() {
        for period in 1..=6 {
            let cuts: Vec<_> = (0..KECCAK_ROUNDS)
                .filter(|&r| slice_round(r, period, true))
                .collect();
            assert_eq!(cuts[0], 0);
            assert_eq!(*cuts.last().unwrap(), 23);
            assert_eq!(cuts.len(), count_slices(period, true));
            assert!(cuts
                .windows(2)
                .all(|w| w[0] < w[1] && w[1] - w[0] <= period));
            assert_eq!(cuts.iter().filter(|&&r| r == 0).count(), 1);
            for r in (period - 1..24).step_by(period) {
                assert!(cuts.contains(&r));
            }
        }
    }
}

type XorLane<L> = Vec<Eltw<L>>;
type XorState<L> = [[XorLane<L>; 5]; 5];

pub struct XorDerived<L: Logic> {
    intermediate_states: Vec<XorState<L>>,
}

pub struct Shake256Witness<L: Logic> {
    pub permutations: Vec<XorDerived<L>>,
}

pub fn permutation_count(input_len: usize, output_len: usize) -> usize {
    let absorb = input_len / SHAKE256_RATE + 1;
    let squeeze = output_len.div_ceil(SHAKE256_RATE);
    absorb + squeeze.saturating_sub(1)
}

enum StatePlucker<'a, L: Logic> {
    B1(BitPlucker<'a, L, 1>),
    B2(BitPlucker<'a, L, 2>),
    B3(BitPlucker<'a, L, 3>),
    B4(BitPlucker<'a, L, 4>),
    B5(BitPlucker<'a, L, 5>),
    B6(BitPlucker<'a, L, 6>),
}
impl<'a, L: Logic> StatePlucker<'a, L> {
    fn new(logic: &'a L, bits: usize) -> Self {
        match bits {
            1 => Self::B1(BitPlucker::new(logic)),
            2 => Self::B2(BitPlucker::new(logic)),
            3 => Self::B3(BitPlucker::new(logic)),
            4 => Self::B4(BitPlucker::new(logic)),
            5 => Self::B5(BitPlucker::new(logic)),
            6 => Self::B6(BitPlucker::new(logic)),
            _ => panic!("invalid plucker width"),
        }
    }
    fn decode(&self, logic: &L, encoded: &Eltw<L>) -> Vec<Eltw<L>> {
        fn decode<L: Logic, const N: usize>(
            p: &BitPlucker<'_, L, N>,
            logic: &L,
            e: &Eltw<L>,
        ) -> Vec<Eltw<L>> {
            let b = p.pluck(e);
            let boolean = Boolean::new(logic);
            let mtwo = logic.field().neg(
                &logic
                    .field()
                    .addf(&logic.field().one(), &logic.field().one()),
            );
            (0..N)
                .map(|i| logic.add(&logic.one(), &logic.mulk(&mtwo, &boolean.as_eltw(b.bit(i)))))
                .collect()
        }
        match self {
            Self::B1(p) => decode(p, logic, encoded),
            Self::B2(p) => decode(p, logic, encoded),
            Self::B3(p) => decode(p, logic, encoded),
            Self::B4(p) => decode(p, logic, encoded),
            Self::B5(p) => decode(p, logic, encoded),
            Self::B6(p) => decode(p, logic, encoded),
        }
    }
}

pub fn allocate_witness<L: LogicIO>(
    bitvec: &BitvecLogic<L>,
    position: &mut usize,
    input_len: usize,
    output_len: usize,
) -> Shake256Witness<L> {
    let logic = bitvec.logic();
    let bits = plucker_bits();
    let chunks = lane_chunks(bits);
    let optional_decoder = (bits > 0).then(|| StatePlucker::new(logic, bits));
    let smaller = chunks
        .last()
        .and_then(|&(_, width)| (width != bits).then(|| StatePlucker::new(logic, width)));
    Shake256Witness {
        permutations: (0..permutation_count(input_len, output_len))
            .map(|_| {
                let mut intermediate_states = Vec::with_capacity(slice_count());
                for _ in 0..slice_count() {
                    let state = std::array::from_fn(|_| {
                        std::array::from_fn(|_| {
                            if let Some(full_decoder) = &optional_decoder {
                                let mut lane = Vec::with_capacity(64);
                                for &(_, width) in &chunks {
                                    let chunk_decoder = if width != bits {
                                        smaller.as_ref().unwrap()
                                    } else {
                                        full_decoder
                                    };
                                    lane.extend(chunk_decoder.decode(logic, &logic.next(position)));
                                }
                                assert_eq!(lane.len(), 64);
                                return lane;
                            }
                            (0..64)
                                .map(|_| {
                                    let value = logic.next(position);
                                    let is_xor_bit = logic.assert0(
                                        "is_xor_bit",
                                        &logic.sub(&logic.mul(&value, &value), &logic.one()),
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
                }
            })
            .collect(),
    }
}

pub struct Shake256<'a, L: Logic> {
    logic: &'a L,
    bitvec: BitvecLogic<'a, L>,
    boolean: Boolean<'a, L>,
}

impl<'a, L: Logic> Shake256<'a, L> {
    pub fn new(logic: &'a L) -> Self {
        Self {
            logic,
            bitvec: BitvecLogic::new(logic),
            boolean: Boolean::new(logic),
        }
    }

    fn xor_lane(&self, a: &XorLane<L>, b: &XorLane<L>) -> XorLane<L> {
        a.iter().zip(b).map(|(x, y)| self.logic.mul(x, y)).collect()
    }

    fn rotl(&self, amount: usize, a: &XorLane<L>) -> XorLane<L> {
        (0..64)
            .map(|i| a[(i + 64 - amount % 64) % 64].clone())
            .collect()
    }

    fn theta(&self, a: &XorState<L>) -> XorState<L> {
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
                next[y][(2 * x + 3 * y) % 5] =
                    self.rotl(crate::sha3::constants::ROTC[x][y], &a[x][y]);
            }
        }
        next
    }

    fn chi(&self, a: &XorState<L>) -> XorState<L> {
        let f = self.logic.field();
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
        self.chi(&precious)
    }

    fn iota(&self, round: usize, a: &XorState<L>) -> XorState<L> {
        let mut next = a.clone();
        let rc = crate::sha3::constants::ROUNDC[round];
        for (bit, value) in next[0][0].iter_mut().enumerate() {
            if (rc >> bit) & 1 != 0 {
                *value = self.logic.neg(value);
            }
        }
        next
    }

    fn assert_eq_xor_state(&self, expected: &XorState<L>, actual: &XorState<L>) -> L::Assertions {
        let f = self.logic.field();
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
        assert_eq!(witness.intermediate_states.len(), slice_count());
        let mut slice_index = 0;
        let mut curr = state.clone();
        let assertion = self.logic.assert_mapi("keccak_f_1600_xor", 0..24, |round| {
            let expected = self.round_without_iota(&curr);
            if is_slice_round(round) {
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
        assert_eq!(block.len(), SHAKE256_RATE);
        let f = self.logic.field();
        let mtwo = f.neg(&f.addf(&f.one(), &f.one()));
        for (i, byte) in block.iter().enumerate() {
            let lane = i / 8;
            let x = lane % 5;
            let y = lane / 5;
            let offset = (i % 8) * 8;
            for bit in 0..8 {
                let input = self.boolean.as_eltw(byte.bit(bit));
                let input_x = self
                    .logic
                    .sum(&[self.logic.one(), self.logic.mulk(&mtwo, &input)]);
                state[x][y][offset + bit] = self.logic.mul(&state[x][y][offset + bit], &input_x);
            }
        }
    }

    fn squeeze_block(&self, state: &XorState<L>, output: &mut Vec<V8<L>>, remaining: usize) {
        let take = remaining.min(SHAKE256_RATE);
        let f = self.logic.field();
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

    pub fn assert_hash(
        &self,
        input: &[V8<L>],
        output_len: usize,
        witness: &Shake256Witness<L>,
    ) -> (Vec<V8<L>>, L::Assertions) {
        assert_eq!(
            witness.permutations.len(),
            permutation_count(input.len(), output_len)
        );
        let mut padded = input.to_vec();
        let padding = SHAKE256_RATE - input.len() % SHAKE256_RATE;
        if padding == 1 {
            padded.push(self.bitvec.of_u64(0x9f));
        } else {
            padded.push(self.bitvec.of_u64(0x1f));
            padded.extend((0..padding - 2).map(|_| self.bitvec.of_u64(0)));
            padded.push(self.bitvec.of_u64(0x80));
        }

        let mut state: XorState<L> = std::array::from_fn(|_| {
            std::array::from_fn(|_| (0..64).map(|_| self.logic.one()).collect())
        });
        let mut assertions = Vec::with_capacity(witness.permutations.len());
        let mut permutation = 0;
        for block in padded.as_chunks::<SHAKE256_RATE>().0 {
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteShake256Witness {
    pub permutations: Vec<ConcreteDerived>,
}

fn permute_native(state: &mut [[u64; 5]; 5], witness: &mut ConcreteShake256Witness) {
    let trajectory = sha3::keccak_f_1600_trajectory(*state);
    witness.permutations.push(ConcreteDerived {
        intermediate_states: (0..KECCAK_ROUNDS)
            .filter(|&round| is_slice_round(round))
            .map(|round| trajectory[round + 1])
            .collect(),
    });
    *state = trajectory[24];
}

fn xof_witness(input: &[u8], output_len: usize, rate: usize) -> (Vec<u8>, ConcreteShake256Witness) {
    let mut padded = input.to_vec();
    let padding = rate - input.len() % rate;
    if padding == 1 {
        padded.push(0x9f);
    } else {
        padded.push(0x1f);
        padded.resize(padded.len() + padding - 2, 0);
        padded.push(0x80);
    }

    let mut state = [[0u64; 5]; 5];
    let mut witness = ConcreteShake256Witness {
        permutations: Vec::with_capacity(
            input.len() / rate + 1 + output_len.div_ceil(rate).saturating_sub(1),
        ),
    };
    for block in padded.chunks_exact(rate) {
        for (i, &byte) in block.iter().enumerate() {
            let lane = i / 8;
            state[lane % 5][lane / 5] ^= u64::from(byte) << (8 * (i % 8));
        }
        permute_native(&mut state, &mut witness);
    }

    let mut output = Vec::with_capacity(output_len);
    while output.len() < output_len {
        for i in 0..rate.min(output_len - output.len()) {
            let lane = i / 8;
            output.push((state[lane % 5][lane / 5] >> (8 * (i % 8))) as u8);
        }
        if output.len() < output_len {
            permute_native(&mut state, &mut witness);
        }
    }
    (output, witness)
}

pub fn shake256_witness(input: &[u8], output_len: usize) -> (Vec<u8>, ConcreteShake256Witness) {
    xof_witness(input, output_len, SHAKE256_RATE)
}

#[must_use]
pub fn shake128(input: &[u8], output_len: usize) -> Vec<u8> {
    xof_witness(input, output_len, 168).0
}

#[cfg(feature = "mldsa-runtime")]
impl ConcreteShake256Witness {
    pub fn push_wires<
        const W: usize,
        F: runtime_algebra::RuntimeField<W> + core_algebra::HasLookupPoints,
    >(
        &self,
        field: &F,
        destination: &mut Vec<F::E>,
    ) {
        let bits = plucker_bits();
        let chunks = lane_chunks(bits);
        for permutation in &self.permutations {
            for state in &permutation.intermediate_states {
                for row in state {
                    for &lane in row {
                        if bits > 0 {
                            for &(start, width) in &chunks {
                                let value = ((lane >> start) & ((1u64 << width) - 1)) as usize;
                                destination.push(field.lookup_point((1 << width) + 1, value));
                            }
                            continue;
                        }
                        for bit in 0..64 {
                            destination.push(if (lane >> bit) & 1 == 0 {
                                field.one()
                            } else {
                                field.mone()
                            });
                        }
                    }
                }
            }
        }
    }
}
