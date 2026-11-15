// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::{
    algebra::packing::PackingField,
    random::{DeterministicRng, RandomEngine},
};

#[test]
fn factored_transpose_and_public_tables_match_dense_trace_pairing() {
    let f = F::new();
    let parameters = Parameters::new(f.clone(), f.packing_extension()).unwrap();
    let mut rng = DeterministicRng::new(73);
    let n = 17;
    let packed: Vec<_> = (0..n).map(|_| rng.elt_field(&f)).collect();
    let mut claim = Claim {
        factors: (0..130)
            .map(|index| Factor {
                words: (0..[n, n - 1, n - 5, 0][index % 4])
                    .map(|word| {
                        if index >= 2 && word % 5 == 0 {
                            f.zero()
                        } else {
                            rng.elt_field(&f)
                        }
                    })
                    .collect(),
                lanes: if index < 2 {
                    std::array::from_fn(|_| rng.elt_field(&f))
                } else {
                    let mut lanes = [f.zero(); 128];
                    lanes[index - 2] = f.one();
                    lanes
                },
            })
            .collect(),
        rhs: NativeRow {
            constant: f.zero(),
            terms: vec![],
        },
        auxiliary_count: 0,
    };
    // Duplicate coordinate factors cancel, including their short/empty tails.
    claim.factors.push(claim.factors[2].clone());
    claim.factors.push(claim.factors[129].clone());
    let delta: [E; 128] = std::array::from_fn(|_| rng.elt_field(&f));
    let gamma = delta.map(|d| f.mulf(&d, &d));
    let mut components = [f.zero(); 128];
    let mut weights = vec![f.zero(); n];
    let mut target = f.zero();
    // Independently expand the coefficient matrix, using explicit bits and
    // the trace-dual basis rather than the optimized transpose or lookup.
    for factor in &claim.factors {
        for (i, &word) in packed.iter().enumerate() {
            let mut column = [f.zero(); 128];
            for j in 0..128 {
                let coefficient = f.mulf(
                    &factor.words.get(i).copied().unwrap_or(f.zero()),
                    &factor.lanes[j],
                );
                if word.to_u128() >> j & 1 != 0 {
                    f.add(&mut target, &coefficient);
                }
                for (h, value) in column.iter_mut().enumerate() {
                    if coefficient.to_u128() >> h & 1 != 0 {
                        f.add(value, &parameters.dual()[j]);
                    }
                }
            }
            for h in 0..128 {
                f.fma(&mut components[h], &column[h], &word);
                f.fma(&mut weights[i], &column[h], &gamma[h]);
            }
        }
    }
    let kernel = kernel::prover::Kernel::new(&claim, &f);
    assert_eq!(
        kernel.components(&claim, &packed, &parameters, &f),
        components
    );
    assert_eq!(kernel.weights(&claim, &delta, &parameters, &f), weights);
    assert_eq!(
        kernel::verifier::verifier_weights(&claim, &delta, &parameters, &f),
        weights
    );
    for (h, component) in components.iter().enumerate() {
        assert_eq!(
            parameters.trace(component),
            E::from(target.to_u128() >> h & 1)
        );
    }
}
