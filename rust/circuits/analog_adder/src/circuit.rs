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
        boolean::Boolean,
    },
    compile::{
        algebra::field::{CompileBinaryField, CompileField, SupportsU64Conversions},
        logic::Logic,
    },
};

pub struct AnalogAdder<'a, L: Logic> {
    logic: &'a L,
    bv: BitvecLogic<'a, L>,
    boolean: Boolean<'a, L>,
}

impl<'a, L: Logic<F = F>, F: CompileField> AnalogAdder<'a, L> {
    pub fn new(logic: &'a L) -> Self {
        Self {
            logic,
            bv: BitvecLogic::new(logic),
            boolean: Boolean::new(logic),
        }
    }

    pub fn assert_wrapping_sum<const N: usize>(
        &self,
        expected: &Bitvec<L, N>,
        terms: &[&[Bitvec<L, N>]],
    ) -> L::Assertions
    where
        F: FieldWrappingSum,
    {
        if self.logic.boolean_arithmetic() {
            return self.assert_boolean_sum(expected, terms);
        }
        self.logic
            .field()
            .assert_wrapping_sum(self, expected, terms)
    }
}

impl<'a, L: Logic> AnalogAdder<'a, L> {
    fn assert_boolean_sum<const N: usize>(
        &self,
        expected: &Bitvec<L, N>,
        terms: &[&[Bitvec<L, N>]],
    ) -> L::Assertions {
        let mut work = terms
            .iter()
            .flat_map(|g| g.iter().cloned())
            .collect::<Vec<_>>();
        assert!(!work.is_empty());
        #[cfg(feature = "experimental")]
        if work.len() > 2 && self.logic.uses_witness_bits() {
            let arith = crate::circuits::arithmetic::Arithmetic::new(self.logic);
            let mut acc = work[0].clone();
            let mut checks = Vec::new();
            // Witness-assisted mode reuses the existing local carry relation.
            let probe = arith.wrapping_add(acc.as_array(), work[1].as_array());
            let computed = probe
                .iter()
                .map(|b| self.boolean.as_eltw(b))
                .collect::<Vec<_>>();
            if let Some(first_wires) = self.logic.witness_bits(&computed) {
                let first_claimed = Bitvec::new(
                    first_wires
                        .into_iter()
                        .map(|w| self.boolean.of_eltw_with_assertion(w, self.logic.ok()))
                        .collect(),
                );
                checks.push(arith.assert_wrapping_add(
                    first_claimed.as_array(),
                    acc.as_array(),
                    work[1].as_array(),
                ));
                acc = first_claimed;
                for term in &work[2..work.len() - 1] {
                    let sum = arith.wrapping_add(acc.as_array(), term.as_array());
                    let values = sum
                        .iter()
                        .map(|b| self.boolean.as_eltw(b))
                        .collect::<Vec<_>>();
                    let wires = self
                        .logic
                        .witness_bits(&values)
                        .expect("active Boolean witness policy");
                    let claimed = Bitvec::new(
                        wires
                            .into_iter()
                            .map(|w| self.boolean.of_eltw_with_assertion(w, self.logic.ok()))
                            .collect(),
                    );
                    checks.push(arith.assert_wrapping_add(
                        claimed.as_array(),
                        acc.as_array(),
                        term.as_array(),
                    ));
                    acc = claimed;
                }
                checks.push(arith.assert_wrapping_add(
                    expected.as_array(),
                    acc.as_array(),
                    work.last().unwrap().as_array(),
                ));
                return self.logic.assert_all("Boolean_partial_sums", &checks);
            }
        }
        // Carry-save compression keeps each stage Boolean and reduces the term count.
        while work.len() > 2 {
            let mut next = Vec::new();
            for chunk in work.chunks(3) {
                if chunk.len() != 3 {
                    next.extend_from_slice(chunk);
                    continue;
                }
                let sum = self.bv.xor3(&chunk[0], &chunk[1], &chunk[2]);
                let carry = self.bv.maj(&chunk[0], &chunk[1], &chunk[2]);
                next.push(Bitvec::new(
                    sum.iter().map(|b| self.boolean.precious(b)).collect(),
                ));
                next.push(Bitvec::new(
                    (0..N)
                        .map(|i| {
                            if i == 0 {
                                self.boolean.falseb()
                            } else {
                                self.boolean.precious(carry.bit(i - 1))
                            }
                        })
                        .collect(),
                ));
            }
            work = next;
        }
        if work.len() == 1 {
            self.bv.assert_eq("boolean_sum", expected, &work[0])
        } else {
            crate::circuits::arithmetic::Arithmetic::new(self.logic).assert_wrapping_add(
                expected.as_array(),
                work[0].as_array(),
                work[1].as_array(),
            )
        }
    }
}

pub trait FieldWrappingSum: CompileField {
    fn assert_wrapping_sum<L: Logic<F = Self>, const N: usize>(
        &self,
        adder: &AnalogAdder<'_, L>,
        expected: &Bitvec<L, N>,
        terms: &[&[Bitvec<L, N>]],
    ) -> L::Assertions;
}

impl<T> FieldWrappingSum for crate::compile::algebra::fp::FpField<T>
where crate::compile::algebra::fp::FpField<T>: CompileField
{
    fn assert_wrapping_sum<L: Logic<F = Self>, const N: usize>(
        &self,
        adder: &AnalogAdder<'_, L>,
        expected: &Bitvec<L, N>,
        terms: &[&[Bitvec<L, N>]],
    ) -> L::Assertions {
        let flat_terms: Vec<Bitvec<L, N>> = terms.iter().flat_map(|g| g.iter().cloned()).collect();
        let n = flat_terms.len();
        assert!(n > 0, "assert_wrapping_sum requires at least 1 term");

        let dim = self.pseudo_dimension_of_multiplicative_group();
        assert!(
            dim > N,
            "Field dimension {dim} must be strictly greater than term bit-width {N}"
        );
        let max_terms = 1usize.checked_shl((dim - N) as u32).unwrap_or(usize::MAX);
        assert!(
            n < max_terms,
            "Field dimension {} is too small to sum {} terms of width {} without overflow (max terms: {})",
            dim,
            n,
            N,
            max_terms - 1
        );

        let p = adder.bv.as_eltw_field(expected);

        let group_sums: Vec<_> = terms
            .iter()
            .map(|g| {
                let eltw_g: Vec<_> = g.iter().map(|t| adder.bv.as_eltw_field(t)).collect();
                adder.logic.sum(&eltw_g)
            })
            .collect();
        let c = adder.logic.sum(&group_sums);

        let diff_c_p = adder.logic.sub(&c, &p);
        let z = adder.logic.precious(&diff_c_p);

        let two_to_n = self.pseudo_basis_unsafe(N);

        let mut factors = Vec::with_capacity(n);
        let field = adder.logic.field();
        for i in 0..n {
            let i_element = field.u64_to_element(i as u64);
            let i_wire = adder.logic.konst(&i_element);
            let offset_wire = adder.logic.mulk(&two_to_n, &i_wire);
            factors.push(adder.logic.sub(&z, &offset_wire));
        }

        let prod = adder.logic.prod(&factors);
        adder.logic.assert0("assert_wrapping_sum_prime", &prod)
    }
}

impl FieldWrappingSum for crate::compile::algebra::gf2_128::Gf2_128Field {
    fn assert_wrapping_sum<L: Logic<F = Self>, const N: usize>(
        &self,
        adder: &AnalogAdder<'_, L>,
        expected: &Bitvec<L, N>,
        terms: &[&[Bitvec<L, N>]],
    ) -> L::Assertions {
        let n = terms.iter().map(|g| g.len()).sum::<usize>();
        assert!(n > 0, "assert_wrapping_sum requires at least 1 term");
        let dim = self.pseudo_dimension_of_multiplicative_group();
        assert!(
            dim > N,
            "Field dimension {dim} must be strictly greater than term bit-width {N}"
        );
        let max_terms = 1usize.checked_shl((dim - N) as u32).unwrap_or(usize::MAX);
        assert!(
            n < max_terms,
            "Field dimension {} is too small to sum {} terms of width {} without overflow (max terms: {})",
            dim,
            n,
            N,
            max_terms - 1
        );

        let alpha = self.generator();
        let mut basis = vec![adder.logic.konst(&alpha); N];
        for i in 1..N {
            basis[i] = adder.logic.mul(&basis[i - 1], &basis[i - 1]);
        }

        let alpha_k = adder.logic.mul(&basis[N - 1], &basis[N - 1]);

        let inject = |v: &Bitvec<L, N>| {
            let mut factors = Vec::with_capacity(N);
            for (i, b_wire) in basis.iter().enumerate().take(N) {
                let bit_wire = adder.boolean.as_eltw(v.bit(i));
                let basis_minus_one = adder.logic.sub(b_wire, &adder.logic.one());
                let term = adder.logic.mul(&basis_minus_one, &bit_wire);
                let factor = adder.logic.add(&adder.logic.one(), &term);
                factors.push(factor);
            }
            adder.logic.prod(&factors)
        };

        let want = inject(expected);

        // Group-wise injection products
        let mut group_prods = Vec::with_capacity(terms.len());
        for g in terms {
            let g_inject: Vec<_> = g.iter().map(&inject).collect();
            group_prods.push(adder.logic.prod(&g_inject));
        }

        let got = adder.logic.prod(&group_prods);

        let mut p = vec![adder.logic.one(); n];
        for i in 1..n {
            p[i] = adder.logic.mul(&p[i - 1], &alpha_k);
        }

        let mut ff = Vec::with_capacity(n);
        for p_elt in &p {
            let term = adder.logic.sub(&got, &adder.logic.mul(p_elt, &want));
            ff.push(term);
        }

        let prod = adder.logic.prod(&ff);
        adder.logic.assert0("assert_wrapping_sum_gf2", &prod)
    }
}
