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

use crate::dense::{affine_interpolation, affine_interpolation_nz_z, affine_interpolation_z_nz};

/// two "hand" variables
#[derive(Clone, Copy)]
pub struct HCorner {
    pub h: [u32; 2],
}

/// Representation of the quad after `bind_g`, in which case g = 0
/// and we don't need to store it.
///
/// Ideally we would write
///   struct hcorner {
///     `quad_corner_t` h[2];
///     Elt v;
///   };
/// However, Elt may be 128-bit aligned, causing holes in the struct.
/// Thus we store an array of H and an array of V.
pub struct HQuad<const W: usize, F: RuntimeField<W>> {
    pub hc: Vec<HCorner>,
    pub vc: Vec<F::E>,
}

impl<const W: usize, F: RuntimeField<W> + core_algebra::SerializableField> HQuad<W, F> {
    /// Bind g in an already-Morton-ordered layer; see [`Self::from_g_binding`].
    #[allow(clippy::too_many_arguments)]
    pub fn bind_g(
        layer: &core_proto::circuit::Layer<F>,
        constants: &[F::E],
        logv: usize,
        nv: usize,
        g0: &[F::E],
        g1: &[F::E],
        alpha: &F::E,
        beta: &F::E,
        f: &F,
    ) -> Self {
        assert!(crate::sane_logw(logv), "logv must be sane");
        let dot = crate::eq::eq2(logv, nv, g0, g1, alpha, f);
        Self::from_g_binding(layer, constants, &dot, beta, f)
    }

    /// Bind g and coalesce adjacent equal input pairs in stored traversal order.
    /// The layer must already be Morton-ordered by (h0, h1), with h0 in the
    /// low bit of each interleaved pair. No sorting or reordering is performed.
    pub fn from_g_binding(
        layer: &core_proto::circuit::Layer<F>,
        constants: &[F::E],
        dot: &[F::E],
        beta: &F::E,
        f: &F,
    ) -> Self {
        let cap = layer.nterms_after_bind_g();
        let mut hc: Vec<HCorner> = Vec::with_capacity(cap);
        let mut vc: Vec<F::E> = Vec::with_capacity(cap);
        layer.for_each_term(
            constants,
            #[inline(always)]
            |term| {
                let dot_val = dot
                    .get(term.g as usize)
                    .expect("term.g out of bounds for dot");
                let vcc = if f.is_zero(&term.k) {
                    f.mulf(beta, dot_val)
                } else {
                    f.mulf(&term.k, dot_val)
                };
                if hc.last().is_some_and(|last| last.h == [term.h0, term.h1]) {
                    if let Some(last) = vc.last_mut() {
                        f.add(last, &vcc);
                    }
                } else {
                    hc.push(HCorner {
                        h: [term.h0, term.h1],
                    });
                    vc.push(vcc);
                }
            },
        );
        debug_assert!(
            hc.windows(2).all(|pair| {
                let [a, b] = [pair[0].h, pair[1].h];
                if (a[1] ^ b[1]).leading_zeros() <= (a[0] ^ b[0]).leading_zeros() {
                    a[1] < b[1]
                } else {
                    a[0] < b[0]
                }
            }),
            "round-major proving requires Morton-ordered circuit terms"
        );
        Self { hc, vc }
    }

    /// Fold the next low bit. Starting from the circuit's Morton order, callers
    /// must alternate hand 0, hand 1 so that mergeable corners stay adjacent.
    pub fn bind_h(&mut self, r: &F::E, hand: usize, f: &F) {
        let n = self.hc.len();
        assert_eq!(self.vc.len(), n, "hc and vc must have equal length");
        let ohand = 1 - hand;
        let mut rd = 0;
        let mut wr = 0;
        let hc_slice = &mut self.hc[..n];
        let vc_slice = &mut self.vc[..n];

        while rd < n {
            let hc_rd = &hc_slice[rd];
            let mut hcc = HCorner { h: [0, 0] };
            hcc.h[hand] = hc_rd.h[hand] >> 1;
            hcc.h[ohand] = hc_rd.h[ohand];

            let vcc;
            let rd1 = rd + 1;
            if rd1 < n
                && hc_rd.h[ohand] == hc_slice[rd1].h[ohand]
                && (hc_rd.h[hand] >> 1) == (hc_slice[rd1].h[hand] >> 1)
                && hc_slice[rd1].h[hand] == hc_rd.h[hand] + 1
            {
                // we have two corners.
                vcc = affine_interpolation(r, &vc_slice[rd], &vc_slice[rd1], f);
                rd += 2;
            } else {
                // we have one corner and the other one is zero.
                if (hc_rd.h[hand] & 1) == 0 {
                    vcc = affine_interpolation_nz_z(r, &vc_slice[rd], f);
                } else {
                    vcc = affine_interpolation_z_nz(r, &vc_slice[rd], f);
                }
                rd = rd1;
            }

            hc_slice[wr] = hcc;
            vc_slice[wr] = vcc;
            wr += 1;
        }

        self.hc.truncate(wr);
        self.vc.truncate(wr);
    }

    #[must_use]
    pub fn scalar(&self) -> F::E {
        assert_eq!(self.hc.len(), 1, "HQuad size must be 1");
        assert_eq!(self.hc[0].h[0], 0, "HQuad index h0 must be 0");
        assert_eq!(self.hc[0].h[1], 0, "HQuad index h1 must be 0");
        assert_eq!(self.vc.len(), 1, "HQuad vc length must be 1");
        self.vc[0].clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core_algebra::{SupportsU128Conversions, SupportsU64Conversions};
    use core_proto::{Layer, TermDelta};
    use runtime_algebra::{gf2_128::Gf2_128Field, p256::P256Field};

    // Independent bit-by-bit reference, including the most significant bits.
    fn morton(h: [u32; 2]) -> u64 {
        let mut key = 0;
        for bit in 0..32 {
            key |= (((h[0] >> bit) & 1) as u64) << (2 * bit);
            key |= (((h[1] >> bit) & 1) as u64) << (2 * bit + 1);
        }
        key
    }

    fn check_morton_binding<
        const W: usize,
        F: RuntimeField<W> + core_algebra::SerializableField,
    >(
        f: &F,
        elt: impl Fn(u64) -> F::E,
    ) {
        let constants = [f.zero(), f.one(), elt(2), f.neg(&f.one())];
        let dot = [elt(3), elt(5), elt(7)];
        let beta = elt(11);
        let mut terms = Vec::new();
        // Equal pairs occur at different g values and include assertion-marker k=0.
        for g in 0..3 {
            for h0 in [0, 1, 2, 3, 4, 7, 1 << 31, u32::MAX] {
                for h1 in [0, 1, 2, 3, 4, 7, 1 << 31, u32::MAX] {
                    terms.push((g, [h0, h1], (g + h0.wrapping_add(h1) % 4) % 4));
                }
            }
        }
        let mut expected = std::collections::BTreeMap::new();
        for &(g, h, k) in &terms {
            let weight = if k == 0 {
                &beta
            } else {
                &constants[k as usize]
            };
            f.fma(
                expected.entry(morton(h)).or_insert_with(|| f.zero()),
                &dot[g as usize],
                weight,
            );
        }
        terms.sort_by_key(|&(_, h, _)| morton(h));
        let mut previous = [0u32; 3];
        let deltas = terms
            .iter()
            .map(|&(g, h, k)| {
                let delta = TermDelta {
                    g: g.wrapping_sub(previous[0]),
                    h: [
                        h[0].wrapping_sub(previous[1]),
                        h[1].wrapping_sub(previous[2]),
                    ],
                    k_index: k,
                };
                previous = [g, h[0], h[1]];
                delta
            })
            .collect();
        let layer = Layer::new_compressed(1usize << 32, 32, vec![deltas], vec![0]);
        let quad = HQuad::from_g_binding(&layer, &constants, &dot, &beta, f);
        assert_eq!(quad.hc.len(), expected.len());
        for ((hc, vc), (key, value)) in quad.hc.iter().zip(&quad.vc).zip(&expected) {
            assert_eq!(morton(hc.h), *key);
            assert_eq!(vc, value);
        }
        let empty = Layer::new_compressed(0, 0, vec![], vec![]);
        let empty_quad = HQuad::from_g_binding(&empty, &constants, &[], &beta, f);
        assert!(empty_quad.hc.is_empty() && empty_quad.vc.is_empty());
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "round-major proving requires Morton-ordered circuit terms")]
    fn rejects_non_morton_pairs() {
        use core_algebra::AlgebraicField;

        let f = P256Field::new();
        // (2,2) follows (0,3) in Morton order, despite preceding it in this layer.
        let layer = Layer::new_compressed(
            4,
            2,
            vec![vec![
                TermDelta {
                    g: 0,
                    h: [2, 2],
                    k_index: 0,
                },
                TermDelta {
                    g: 0,
                    h: [0u32.wrapping_sub(2), 1],
                    k_index: 0,
                },
            ]],
            vec![0],
        );
        HQuad::from_g_binding(&layer, &[f.one()], &[f.one()], &f.one(), &f);
    }

    #[test]
    fn morton_pair_binding_prime_field() {
        let f = P256Field::new();
        check_morton_binding(&f, |v| f.u64_to_element(v));
    }

    #[test]
    fn morton_pair_binding_binary_field() {
        let f = Gf2_128Field::new();
        check_morton_binding(&f, |v| f.u128_to_element(v as u128));
    }
}
