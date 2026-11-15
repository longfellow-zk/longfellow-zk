// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Exact-mode adapter: integer oracles, every alternative quotient, and the
//! fixed fragment over all source assignments. Ported from the ML-DSA adapter.
use super::{
    super::{fragment, virtual_inputs, TreeInstance},
    *,
};
use crate::{
    core::algebra::{fp24::Q, AlgebraicField},
    runtime::{
        algebra::gf2_128::{Gf2_128, Gf2_128Field},
        random::DeterministicRng,
        v2::{foreign::reserved::ReservedSuffix, sumcheck::eval_circuit},
    },
};

fn centered(weight: u32, r: usize) -> i64 {
    let a = ((u64::from(weight) << r) % u64::from(Q)) as i64;
    if a > i64::from(Q / 2) {
        a - i64::from(Q)
    } else {
        a
    }
}
/// The honest quotient of each claim, from integer arithmetic alone.
fn oracle(
    values: &[u32],
    widths: &[usize],
    weights: &[[u32; CLAIMS]],
    targets: &[u32; CLAIMS],
) -> [u64; CLAIMS] {
    std::array::from_fn(|t| {
        let (mut sum, mut offset) = (0i64, 0i64);
        for ((&value, &width), weight) in values.iter().zip(widths).zip(weights) {
            for r in 0..width {
                let a = centered(weight[t], r);
                offset += (-a).max(0);
                sum += a * i64::from(value >> r & 1);
            }
        }
        let residue = (i64::from(targets[t]) + offset) % i64::from(Q);
        assert_eq!((sum + offset - residue) % i64::from(Q), 0);
        ((sum + offset - residue) / i64::from(Q)) as u64
    })
}
fn targets(values: &[u32], weights: &[[u32; CLAIMS]]) -> [u32; CLAIMS] {
    std::array::from_fn(|t| {
        (values
            .iter()
            .zip(weights)
            .map(|(&v, w)| u64::from(v) * u64::from(w[t]))
            .sum::<u64>()
            % u64::from(Q)) as u32
    })
}
struct Setup<const N: usize> {
    plan: ExactPlan<N>,
    groups: Vec<Group>,
    otp: [BitGroup<N>; CLAIMS],
    pads: [Otp<N>; CLAIMS],
    suffix: ReservedSuffix,
}
fn setup<const N: usize>(widths: &[usize]) -> Setup<N> {
    let mut at = 0;
    let groups = widths
        .iter()
        .map(|&width| {
            at += width;
            Group::new(at - width, width).unwrap()
        })
        .collect();
    let mut suffix = ReservedSuffix::new(at);
    let otp = std::array::from_fn(|_| suffix.word::<N>().unwrap());
    let mut rng = DeterministicRng::new(5);
    Setup {
        plan: ExactPlan::new(widths.to_vec()).unwrap(),
        groups,
        otp,
        pads: std::array::from_fn(|_| Otp::sample(&mut rng)),
        suffix,
    }
}
impl<const N: usize> Setup<N> {
    /// Committed inputs: the source bits, then the quotient pads.
    fn inputs(&self, bits: &[bool], f: &Gf2_128Field) -> Vec<Gf2_128> {
        let mut w = self.suffix.witness();
        for (g, p) in self.otp.iter().zip(&self.pads) {
            w.set(g.group(), p.bits()).unwrap();
        }
        bits.iter()
            .copied()
            .chain(w.into_bits())
            .map(|b| if b { f.one() } else { f.zero() })
            .collect()
    }
    fn trees(
        &self,
        claims: &ExactClaims,
        quotients: &[u64; CLAIMS],
        f: &Gf2_128Field,
    ) -> Vec<TreeInstance> {
        // Reproduce the fixture's pads for each independent oracle case.
        let mut rng = DeterministicRng::new(5);
        let masked: [MaskedWord<N>; CLAIMS] = std::array::from_fn(|t| {
            MaskedWord::mask(Word::new(quotients[t]).unwrap(), Otp::sample(&mut rng))
        });
        self.plan
            .encode(f, claims)
            .trees(&self.plan, &self.groups, &self.otp, &masked, f)
            .unwrap()
    }
}
/// Evaluate every leaf directly: each tree's product must equal its target.
fn accepts(trees: &[TreeInstance], inputs: &[Gf2_128], f: &Gf2_128Field) -> bool {
    trees.iter().all(|tree| {
        let product = tree.leaves.iter().fold(f.one(), |acc, l| {
            let v = f.addf(&l.constant, &f.mulf(&l.coefficient, &inputs[l.source]));
            f.mulf(&acc, &v)
        });
        product == tree.target
    })
}

#[test]
fn exact_quotients_match_an_integer_oracle_and_reject_every_other_quotient() {
    let f = Gf2_128Field::new();
    let widths = [3, 3];
    let values = [5u32, 6];
    let weights = vec![
        [Q / 2, Q - 1, 17, 8123456, 917, 1],
        [31337, Q / 2 + 1, Q - 31, 0, 7212345, 8380000],
    ];
    let targets = targets(&values, &weights);
    let expected = oracle(&values, &widths, &weights, &targets);
    let s = setup::<2>(&widths);
    let bits: Vec<_> = values
        .iter()
        .flat_map(|v| (0..3).map(move |r| v >> r & 1 != 0))
        .collect();
    let claims = ExactClaims { weights, targets };
    let quotients = s
        .plan
        .encode(&f, &claims)
        .quotients(&s.plan, &bits)
        .unwrap();
    assert_eq!(quotients.map(Word::value), expected);
    let inputs = s.inputs(&bits, &f);
    assert!(accepts(&s.trees(&claims, &expected, &f), &inputs, &f));
    for t in 0..CLAIMS {
        for q in 0..1u64 << 2 {
            if q != expected[t] {
                let mut bad = expected;
                bad[t] = q;
                let trees = s.trees(&claims, &bad, &f);
                assert!(!accepts(&trees, &inputs, &f), "claim {t}, quotient {q}");
            }
        }
    }
    for i in 0..bits.len() {
        let mut bad = bits.clone();
        bad[i] = !bad[i];
        let trees = s.trees(&claims, &expected, &f);
        assert!(!accepts(&trees, &s.inputs(&bad, &f), &f), "source bit {i}");
    }
}

#[test]
fn exact_full_width_words_match_an_integer_dot_product() {
    let f = Gf2_128Field::new();
    let widths = [23, 20, 10, 1];
    let values = [Q - 1, (1 << 20) - 1, 1023, 1];
    let weights: Vec<[u32; CLAIMS]> = (0..4)
        .map(|i| {
            std::array::from_fn(|t| [Q / 2, Q / 2 + 1, Q - 1, 1, 31337, 8123456][(i + t) % CLAIMS])
        })
        .collect();
    let targets = targets(&values, &weights);
    let expected = oracle(&values, &widths, &weights, &targets);
    let s = setup::<5>(&widths);
    let bits: Vec<_> = values
        .iter()
        .zip(&widths)
        .flat_map(|(&value, &width)| (0..width).map(move |r| value >> r & 1 != 0))
        .collect();
    let claims = ExactClaims { weights, targets };
    let quotients = s
        .plan
        .encode(&f, &claims)
        .quotients(&s.plan, &bits)
        .unwrap();
    assert_eq!(quotients.map(Word::value), expected);
    assert!(accepts(
        &s.trees(&claims, &expected, &f),
        &s.inputs(&bits, &f),
        &f
    ));
    // The plan refuses a quotient width that cannot cover the claims.
    assert!(ExactPlan::<4>::new(widths.to_vec()).is_err());
}

#[test]
fn exact_fragment_checks_every_source_assignment() {
    let f = Gf2_128Field::new();
    for widths in [vec![1], vec![2], vec![1, 1]] {
        let s = setup::<1>(&widths);
        let bits_total: usize = widths.iter().sum();
        let weights: Vec<[u32; CLAIMS]> = (0..widths.len())
            .map(|j| {
                std::array::from_fn(|t| [1, 17, Q / 2, Q / 2 + 1, Q - 1, 8123456][(t + j) % CLAIMS])
            })
            .collect();
        let shape = s.plan.shape();
        let c = fragment(0, s.suffix.end(), shape).unwrap();
        for assignment in 0..1usize << bits_total {
            let bits: Vec<_> = (0..bits_total).map(|r| assignment >> r & 1 != 0).collect();
            let mut offset = 0;
            let values: Vec<_> = widths
                .iter()
                .map(|&width| {
                    let word = (assignment >> offset) & ((1 << width) - 1);
                    offset += width;
                    word as u32
                })
                .collect();
            let claims = ExactClaims {
                weights: weights.clone(),
                targets: targets(&values, &weights),
            };
            let quotients = s
                .plan
                .encode(&f, &claims)
                .quotients(&s.plan, &bits)
                .unwrap();
            let leaves =
                virtual_inputs(shape, s.trees(&claims, &quotients.map(Word::value), &f), &f)
                    .unwrap();
            let committed = s.inputs(&bits, &f);
            let with_leaves = |source: &[Gf2_128]| {
                let mut inputs = source.to_vec();
                for e in &leaves.entries {
                    inputs.push(f.addf(&e.constant, &f.mulf(&e.coefficient, &source[e.source])));
                }
                inputs
            };
            eval_circuit(with_leaves(&committed), &c, &f).unwrap();
            for changed in 0..bits_total {
                let mut bad = committed.clone();
                bad[changed] = f.addf(&bad[changed], &f.one());
                assert!(
                    eval_circuit(with_leaves(&bad), &c, &f).is_err(),
                    "unchecked source bit {changed}"
                );
            }
        }
    }
}

#[test]
fn exact_mode_prover_and_verifier_agree_and_bind_the_masked_quotients() {
    use crate::{
        core::algebra::SupportsU64Conversions,
        runtime::{
            algebra::fp24_ext6::RuntimeFp24Ext6,
            v2::{
                foreign::adapter::AdapterMode,
                proto::composed::WriteAdapterMessage,
                transcript::{Transcript, ZkStatement},
                zk::storage::ModularClaim,
            },
        },
    };
    let f = Gf2_128Field::new();
    let af = RuntimeFp24Ext6::new();
    let widths = vec![23, 20, 10, 1];
    let values = [Q - 1, (1 << 20) - 1, 1023, 1];
    let mut suffix = ReservedSuffix::new(54);
    let mode = ExactMode::<5>::new(widths.clone(), 0, &mut suffix).unwrap();
    assert_eq!(mode.virtual_inputs(), 2 * (54 + 15));
    let mut at = 0;
    let weights: Vec<_> = (0..4u32)
        .map(|i| {
            af.from_coefficients(std::array::from_fn(|t| {
                (i + 7) * 31337 * (t as u32 + 1) % Q
            }))
        })
        .collect();
    let terms: Vec<_> = widths
        .iter()
        .zip(&weights)
        .map(|(&width, w)| {
            at += width;
            (Group::new(at - width, width).unwrap(), *w)
        })
        .collect();
    let elements: Vec<_> = values
        .iter()
        .map(|&v| af.u64_to_element(u64::from(v)))
        .collect();
    let target = terms
        .iter()
        .zip(&elements)
        .fold(af.zero(), |s, ((_, w), v)| af.addf(&s, &af.mulf(w, v)));
    let claim = ModularClaim { terms, target };
    let pads = mode.sample_pads(&mut DeterministicRng::new(9));
    let mut w = suffix.witness();
    mode.write_pads(&pads, &mut w).unwrap();
    let mut tp = Transcript::new(&ZkStatement {
        context: b"exact-mode",
    });
    // Exact conversion has no randomness: asking for its unit input must
    // leave the challenge stream untouched.
    let mut with_conversion = tp.fork_for_test();
    let mut without_conversion = tp.fork_for_test();
    assert_eq!(
        with_conversion.borrow().draw(|r| r.bytes(32)),
        without_conversion.borrow().draw(|r| r.bytes(32))
    );
    let mut tv = tp.fork_for_test();
    let (masked, leaves) =
        ExactMode::prove(&mut tp.bound(&mode), &claim, &elements, pads, &af, &f).unwrap();
    let mut encoded = Vec::new();
    masked.write(&mut encoded);
    let mut input = encoded.as_slice();
    let decoded: [MaskedWord<5>; CLAIMS] =
        std::array::from_fn(|_| MaskedWord::read(&mut input).unwrap());
    assert!(input.is_empty());
    assert_eq!(decoded, masked);
    assert_eq!(
        ExactMode::verify(&mut tv.bound(&mode), &claim, &decoded, &af, &f).unwrap(),
        leaves
    );
    assert_eq!(
        tp.borrow().draw(|r| r.bytes(32)),
        tv.borrow().draw(|r| r.bytes(32))
    );
    // The fragment accepts the honest leaves over the committed bits.
    let mut inputs: Vec<_> = values
        .iter()
        .zip(&widths)
        .flat_map(|(&v, &width)| (0..width).map(move |r| v >> r & 1 != 0))
        .chain(w.into_bits())
        .map(|b| if b { f.one() } else { f.zero() })
        .collect();
    for e in leaves.entries.clone() {
        let x = f.addf(&e.constant, &f.mulf(&e.coefficient, &inputs[e.source]));
        inputs.push(x);
    }
    eval_circuit(inputs, mode.fragment(), &f).unwrap();
    // A different masked quotient changes the transcript and the leaves.
    let mut altered_transcript = Transcript::new(&ZkStatement {
        context: b"exact-mode",
    });
    let mut bad = masked;
    let flipped: Vec<u8> = {
        let mut b = Vec::new();
        bad[0].write(&mut b);
        b[0] ^= 1;
        b
    };
    bad[0] = MaskedWord::read(&mut flipped.as_slice()).unwrap();
    let other =
        ExactMode::verify(&mut altered_transcript.bound(&mode), &claim, &bad, &af, &f).unwrap();
    assert_ne!(other, leaves);
    // A value outside its group is refused by the prover.
    let mut wide = elements.clone();
    wide[3] = af.u64_to_element(2);
    let mut tx = Transcript::new(&ZkStatement { context: b"x" });
    let wide_pads = mode.sample_pads(&mut DeterministicRng::new(10));
    assert!(ExactMode::prove(&mut tx.bound(&mode), &claim, &wide, wide_pads, &af, &f).is_err());
}
