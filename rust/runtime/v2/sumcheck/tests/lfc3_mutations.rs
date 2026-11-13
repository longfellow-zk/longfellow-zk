// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Every circuit the LFC3 reader accepts must be safe to hand to the sumcheck
//! verifier with an arbitrary proof. Several verifier paths unwrap or assert
//! on circuit metadata (assertion counts per constant class, nonzero constant
//! records); they rely on the reader deriving that metadata with the same
//! classifier the sumcheck split uses. This test pins that invariant.
use std::panic::{catch_unwind, AssertUnwindSafe};

use crate::{
    core::{
        algebra::SerializableField,
        proto::v2::{
            Circuit, CircuitReader, CircuitWriter, Constant, Layer, Linear, Quadratic,
            RawCircuitBuilder, Stream,
        },
    },
    runtime::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field, RuntimeField, SupportsSampling},
        random::{DeterministicRng, RandomEngine},
        v2::{
            sumcheck::{
                circuit_geometry, derive_constraints_for_circuits, LayerProof, RoundPoly,
                SumcheckProof,
            },
            transcript::Transcript,
        },
    },
};

/// Deterministic xorshift64 for mutation positions and values.
struct XorShift(u64);
impl XorShift {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

/// Three layers using general, one, minus-one and zero-coefficient
/// (assertion) terms in every stream kind.
fn base<const W: usize, F: RuntimeField<W> + SerializableField>(f: &F) -> Circuit<F> {
    let two = f.addf(&f.one(), &f.one());
    let five = f.addf(&f.addf(&two, &two), &f.one());
    let layer = |nw, q: Vec<Quadratic>, l: Vec<Linear>, k: Vec<Constant>| {
        Layer::with_assertions(
            nw,
            Stream::<Quadratic>::from_terms(q),
            Stream::<Linear>::from_terms(l),
            Stream::<Constant>::from_terms(k),
            |k| k == 0,
        )
    };
    let q = |g, l, r, k| Quadratic { g, l, r, k };
    let l = |g, l, k| Linear { g, l, k };
    let raw = RawCircuitBuilder {
        ninput: 6,
        npublic_input: 2,
        noutput: 2,
        logv: 1,
        constants: vec![f.zero(), f.one(), f.mone(), five],
        layers: vec![
            layer(
                3,
                vec![q(0, 2, 0, 0), q(1, 1, 2, 3)],
                vec![l(0, 0, 2), l(0, 1, 1), l(1, 2, 0)],
                vec![Constant { g: 1, k: 3 }],
            ),
            layer(
                5,
                vec![q(1, 1, 2, 1), q(2, 4, 4, 2), q(0, 3, 1, 0)],
                vec![l(0, 0, 1), l(2, 3, 3)],
                vec![Constant { g: 0, k: 1 }],
            ),
            layer(
                6,
                vec![q(0, 0, 5, 1), q(3, 2, 3, 3)],
                vec![l(1, 1, 1), l(2, 4, 2), l(4, 5, 0)],
                vec![Constant { g: 4, k: 2 }],
            ),
        ],
    }
    .build();
    Circuit::from_raw(f, raw)
}

fn random_proof<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    logw: &[usize],
    rng: &mut DeterministicRng,
    f: &F,
) -> SumcheckProof<W, F> {
    SumcheckProof {
        layers: logw
            .iter()
            .map(|&n| LayerProof {
                rounds: (0..n)
                    .map(|_| RoundPoly {
                        coefficients: [rng.elt_field(f), rng.elt_field(f)],
                    })
                    .collect(),
                cross: rng.elt_field(f),
                claims: [rng.elt_field(f), rng.elt_field(f)],
            })
            .collect(),
    }
}

/// Mutate the encoded body (header excluded, stale ID ignored), and run the
/// verifier on every reader-accepted result, alone and combined with the
/// original. Returns the number of accepted mutants; panics propagate.
fn check_mutations<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    f: &F,
    iterations: usize,
    seed: u64,
) -> usize {
    let original = base(f);
    let bytes = CircuitWriter::new(f).to_bytes(&original);
    let reader = CircuitReader::new(f);
    let mut xs = XorShift(seed);
    let mut accepted = 0;
    for iteration in 0..iterations {
        let mut mutated = bytes.clone();
        let body = mutated.len() - 32;
        for _ in 0..1 + xs.next() % 3 {
            let at = 8 + (xs.next() as usize) % (body - 8);
            match xs.next() % 4 {
                0 => mutated[at] ^= 1 << (xs.next() % 8),
                1 => mutated[at] = xs.next() as u8,
                2 => mutated[at] = mutated[at].wrapping_add(1),
                _ => mutated[at] = mutated[at].wrapping_sub(1),
            }
        }
        let Ok(c) = reader.from_bytes_recomputing_id(&mutated) else {
            continue;
        };
        accepted += 1;
        for list in [vec![&c], vec![&c, &original], vec![&original, &c, &c]] {
            let Ok(geometry) = circuit_geometry(list.as_slice()) else {
                continue;
            };
            let mut rng = DeterministicRng::new(seed ^ iteration as u64);
            let proof = random_proof(&geometry.logw_layers, &mut rng, f);
            let outcome = catch_unwind(AssertUnwindSafe(|| {
                let _ = derive_constraints_for_circuits(
                    list.as_slice(),
                    &proof,
                    &mut Transcript::new(b"lfc3-mutations").borrow(),
                    f,
                );
            }));
            assert!(
                outcome.is_ok(),
                "sumcheck verifier panicked on a reader-accepted circuit \
                 (iteration {iteration}, seed {seed:#x}, {} circuits)",
                list.len()
            );
        }
    }
    accepted
}

#[test]
fn reader_accepted_circuits_never_panic_sumcheck_verifier() {
    const ITERATIONS: usize = 4000;
    let binary = check_mutations(&Gf2_128Field::new(), ITERATIONS, 0x9e37_79b9_7f4a_7c15);
    let prime = check_mutations(&P256Field::new(), ITERATIONS, 0x2545_f491_4f6c_dd1d);
    // Guard against a vacuous run: a useful share of mutants must reach the verifier.
    assert!(
        binary > ITERATIONS / 20,
        "only {binary} binary mutants accepted"
    );
    assert!(
        prime > ITERATIONS / 20,
        "only {prime} prime mutants accepted"
    );
}
