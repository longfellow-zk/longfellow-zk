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

use super::logic::{BinaryLogic, Depth};
use crate::{
    circuits::{
        arithmetic::Arithmetic,
        bitvec::{BitvecIO, BitvecLogic, V32},
        boolean::Boolean,
        sha256::{constants::K, Derived, Given},
    },
    compile::algebra::gf2_128::Gf2_128Field,
    core::proto::v2::Circuit,
};
pub(super) struct Sha256<'a, L: Depth> {
    logic: &'a L,
    bv: BitvecLogic<'a, L>,
}

impl<'a, L: Depth> Sha256<'a, L> {
    pub(super) fn new(logic: &'a L) -> Self {
        Self {
            logic,
            bv: BitvecLogic::new(logic),
        }
    }

    fn xorb(&self, a: &V32<L>, b: &V32<L>) -> V32<L> {
        V32::new(Arithmetic::new(self.logic).xorb(a.as_array(), b.as_array()))
    }

    fn andb(&self, a: &V32<L>, b: &V32<L>) -> V32<L> {
        V32::new(Arithmetic::new(self.logic).andb(a.as_array(), b.as_array()))
    }

    #[inline]
    fn ch(&self, x: &V32<L>, y: &V32<L>, z: &V32<L>) -> V32<L> {
        self.xorb(z, &self.andb(x, &self.xorb(y, z)))
    }

    #[inline]
    fn bigsigma0(&self, x: &V32<L>) -> V32<L> {
        self.bv.xor3(
            &self.bv.rotr(2, x),
            &self.bv.rotr(13, x),
            &self.bv.rotr(22, x),
        )
    }

    #[inline]
    fn bigsigma1(&self, x: &V32<L>) -> V32<L> {
        self.bv.xor3(
            &self.bv.rotr(6, x),
            &self.bv.rotr(11, x),
            &self.bv.rotr(25, x),
        )
    }

    #[inline]
    fn sigma0(&self, x: &V32<L>) -> V32<L> {
        self.bv.xor3(
            &self.bv.rotr(7, x),
            &self.bv.rotr(18, x),
            &self.bv.shr(3, x),
        )
    }

    #[inline]
    fn sigma1(&self, x: &V32<L>) -> V32<L> {
        self.bv.xor3(
            &self.bv.rotr(17, x),
            &self.bv.rotr(19, x),
            &self.bv.shr(10, x),
        )
    }

    pub(super) fn assert_transform_block(
        &self,
        given: &Given<V32<L>>,
        derived: &Derived<V32<L>>,
    ) -> L::Assertions {
        let mut w = Vec::with_capacity(64);
        w.extend(given.input_block.iter().cloned());
        w.extend(derived.outw.iter().cloned());

        let adder = CsaAdder::new(self.logic);
        // Key schedule assertions
        let schedule_assertions = self.logic.assert_mapi("schedule", 16..64, |i| {
            adder.assert_wrapping_sum(
                &w[i],
                &[&[
                    self.sigma1(&w[i - 2]),
                    w[i - 7].clone(),
                    self.sigma0(&w[i - 15]),
                    w[i - 16].clone(),
                ]],
            )
        });

        // Round assertions
        let mut state = std::array::from_fn(|i| given.h0[i].clone());
        let round_assertions = self.logic.assert_mapi("rounds", 0..64, |t| {
            let [a, b, c, d, e, f, g, h] = state.clone();

            let t1 = [
                h,
                self.bigsigma1(&e),
                self.bv.of_u32(K[t]),
                self.ch(&e, &f, &g),
                w[t].clone(),
            ];
            let t2 = [
                self.bigsigma0(&a),
                self.xorb(&a, &self.andb(&self.xorb(&a, &b), &self.xorb(&a, &c))),
            ];

            // Assert oute[t] is sum of d and t1 using grouping
            let oute_assertion = adder.assert_wrapping_sum(
                &derived.oute[t],
                &[std::slice::from_ref(&d) as &[V32<L>], &t1 as &[V32<L>]],
            );

            // Assert outa[t] is sum of t2 and t1 using grouping
            let outa_assertion =
                adder.assert_wrapping_sum(&derived.outa[t], &[&t2 as &[V32<L>], &t1 as &[V32<L>]]);

            state = [
                derived.outa[t].clone(),
                a,
                b,
                c,
                derived.oute[t].clone(),
                e,
                f,
                g,
            ];

            self.logic
                .assert_all("round_step", &[oute_assertion, outa_assertion])
        });

        // Final state addition assertions
        let final_assertions = self.logic.assert_mapi("final", 0..8, |i| {
            adder.assert_wrapping_sum(&derived.h1[i], &[&[given.h0[i].clone(), state[i].clone()]])
        });

        self.logic.assert_all(
            "sha256",
            &[schedule_assertions, final_assertions, round_assertions],
        )
    }
}

/// For a wrapping sum, sum(terms)+~expected must be 2^32-1 modulo 2^32.
/// Carry-save compression preserves that congruence. Two words sum to all ones
/// exactly when they are complementary, so the final equality is linear.
struct CsaAdder<'a, L: Depth> {
    logic: &'a L,
    bv: BitvecLogic<'a, L>,
    boolean: Boolean<'a, L>,
}
impl<'a, L: Depth> CsaAdder<'a, L> {
    fn new(logic: &'a L) -> Self {
        Self {
            logic,
            bv: BitvecLogic::new(logic),
            boolean: Boolean::new(logic),
        }
    }
    fn notb(&self, a: &V32<L>) -> V32<L> {
        V32::new(a.iter().map(|bit| self.boolean.notb(bit)).collect())
    }
    fn compress(&self, mut work: Vec<V32<L>>) -> Vec<V32<L>> {
        use crate::circuits::bitvec::Bitvec;
        while work.len() > 2 {
            work.sort_by_key(|word| {
                word.iter()
                    .map(|b| self.logic.wire_depth(&self.boolean.as_eltw(b)))
                    .max()
                    .unwrap_or(0)
            });
            let c = work.remove(2);
            let b = work.remove(1);
            let a = work.remove(0);
            // Discarded carry is a multiple of 2^32 in this wrapping relation.
            let sum = self.bv.xor3(&a, &b, &c);
            let mut carry = Vec::with_capacity(32);
            carry.push(self.boolean.falseb());
            for i in 0..31 {
                let x = a.bit(i);
                let y = b.bit(i);
                let z = c.bit(i);
                carry.push(
                    self.boolean.xorb(
                        x,
                        &self
                            .boolean
                            .andb(&self.boolean.xorb(x, y), &self.boolean.xorb(x, z)),
                    ),
                );
            }
            let carry_word: V32<L> = Bitvec::new(carry);
            work.push(Bitvec::new(
                sum.iter().map(|bit| self.boolean.precious(bit)).collect(),
            ));
            work.push(Bitvec::new(
                carry_word
                    .iter()
                    .map(|bit| self.boolean.precious(bit))
                    .collect(),
            ));
        }
        work
    }
    fn assert_wrapping_sum(&self, expected: &V32<L>, groups: &[&[V32<L>]]) -> L::Assertions {
        let mut terms: Vec<_> = groups
            .iter()
            .flat_map(|g| self.compress(g.to_vec()))
            .collect();
        terms.push(self.notb(expected));
        let compressed = self.compress(terms);
        let complement = if compressed.len() == 1 {
            self.bv.of_u32(u32::MAX)
        } else {
            self.notb(&compressed[1])
        };
        // Each residual is Boolean. Combining bit equalities with GF128 basis
        // coefficients would destroy the shared bit-plane circuit relation.
        self.logic.assert_mapi("carry_save_sum", 0..32, |i| {
            self.boolean
                .assert_eq("bit", compressed[0].bit(i), complement.bit(i))
        })
    }
}

/// Compile with Boolean-only coefficients before viewing field words as lanes.
/// A packed field equality would mix lanes, so reject it at this boundary.
pub(super) fn compile_base() -> Result<Circuit<Gf2_128Field>, String> {
    use crate::{
        compile::{
            algebra::gf2_128::Gf2_128Field,
            compiler::{compile_v2, segment_circuit_v2},
            logic::K_FIRST_WIRE_POSITION,
        },
        core::algebra::AlgebraicField,
    };
    let field = Gf2_128Field::new();
    let (compiled, _, _) = compile_v2(&field, |inner| {
        let logic = BinaryLogic(inner);
        let mut pos = K_FIRST_WIRE_POSITION;
        let bv = BitvecLogic::new(&logic);
        let io = BitvecIO::new(&bv);
        let given = Given::from_fn(|| io.next::<32>(&mut pos));
        let derived = Derived::from_fn(|| io.next::<32>(&mut pos));
        assert_eq!(pos - K_FIRST_WIRE_POSITION, super::INPUT_BITS);
        (
            Sha256::new(&logic).assert_transform_block(&given, &derived),
            K_FIRST_WIRE_POSITION,
        )
    });
    if compiled
        .constants
        .iter()
        .any(|x| *x != field.zero() && *x != field.one())
    {
        return Err("SIMD circuit requires Boolean coefficients".into());
    }
    Ok(segment_circuit_v2(&field, compiled))
}
