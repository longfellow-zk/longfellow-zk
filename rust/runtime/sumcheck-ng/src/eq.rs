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

use runtime_algebra::RuntimeField;

/// Dense multilinear equality weights EQ(point, i), for 0 <= i < n.
/// Missing indices up to 2^logn are implicitly zero, including an empty domain.
pub fn weights<const W: usize, F: RuntimeField<W>>(
    logn: usize,
    n: usize,
    point: &[F::E],
    f: &F,
) -> Vec<F::E> {
    assert!(crate::sane_logw(logn) && point.len() >= logn);
    assert!(n as u64 <= (1u64 << logn));
    let mut weights = vec![f.zero(); n];
    if n != 0 {
        fill_single(&mut weights, &point[..logn], &f.one(), f);
    }
    weights
}

fn fill_single<const W: usize, F: RuntimeField<W>>(
    weights: &mut [F::E],
    point: &[F::E],
    weight: &F::E,
    f: &F,
) {
    if let Some((r, lower_bits)) = point.split_last() {
        let stride = 1usize << lower_bits.len();
        let high = f.mulf(weight, r);
        let low = f.subf(weight, &high);
        if stride < weights.len() {
            let (left, right) = weights.split_at_mut(stride);
            fill_single(left, lower_bits, &low, f);
            fill_single(right, lower_bits, &high, f);
        } else {
            fill_single(weights, lower_bits, &low, f);
        }
    } else {
        weights[0] = weight.clone();
    }
}

/// Return chi + alpha * mu as the next layer's public weights.
pub fn next_weights<const W: usize, F: RuntimeField<W>>(
    mut chi: Vec<F::E>,
    mu: &[F::E],
    alpha: &F::E,
    f: &F,
) -> Vec<F::E> {
    assert_eq!(chi.len(), mu.len());
    for (x, y) in chi.iter_mut().zip(mu) {
        f.fma(x, alpha, y);
    }
    chi
}
