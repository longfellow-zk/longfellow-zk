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
use crate::runtime::random::{DeterministicRng, RandomEngine};
#[test]
fn all_boolean_windows_match_dense_rounds_including_incomplete_blocks() {
    let f = F::new();
    let mut rng = DeterministicRng::new(91);
    for n in [1, 2, 3, 4, 5, 7, 8, 15, 16, 17, 31, 32, 33, 127, 129] {
        let bits = (0..n).map(|_| rng.u128() & 1 != 0).collect::<PackedBits>();
        let mut w = (0..n)
            .map(|i| E::from(u128::from(bits.get(i))))
            .collect::<Vec<_>>();
        let mut q = (0..n).map(|_| E::from(rng.u128())).collect::<Vec<_>>();
        let mut monomials = vec![f.one()];
        for _round in 0..4 {
            let claim = crate::runtime::algebra::blas::dot(&q, &w, &f);
            assert_eq!(
                mixed_round(&bits, &q, &monomials, &claim, &f),
                prover::quad_round_poly(&q, &w, &claim, &f),
                "n={n}"
            );
            assert_eq!(bind_window(&bits, &monomials, &f), w);
            let z = E::from(rng.u128());
            dense::bind(&mut w, &z, &f);
            dense::bind(&mut q, &z, &f);
            let m = monomials.len();
            for i in 0..m {
                monomials.push(f.mulf(&monomials[i], &z))
            }
        }
    }
}
