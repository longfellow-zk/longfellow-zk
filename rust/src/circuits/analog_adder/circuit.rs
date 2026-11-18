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
        algebra::{fp::FpField, gf2_128::Gf2_128Field, CompileBinaryField, CompileField},
        logic::Logic,
    },
    core::algebra::{AlgebraicField, SupportsU64Conversions},
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
        self.logic
            .field()
            .assert_wrapping_sum(self, expected, terms)
    }

    pub(crate) fn assert_wrapping_sums_equal<const N: usize>(
        &self,
        left: &[Bitvec<L, N>],
        right: &[&[Bitvec<L, N>]],
    ) -> L::Assertions
    where
        F: FieldWrappingSum,
    {
        self.logic
            .field()
            .assert_wrapping_sums_equal(self, left, right)
    }
}

pub trait FieldWrappingSum: CompileField {
    fn assert_wrapping_sum<L: Logic<F = Self>, const N: usize>(
        &self,
        adder: &AnalogAdder<'_, L>,
        expected: &Bitvec<L, N>,
        terms: &[&[Bitvec<L, N>]],
    ) -> L::Assertions {
        self.assert_wrapping_sums_equal(adder, std::slice::from_ref(expected), terms)
    }

    /// Assert that the two nonempty sums are equal modulo `2^N`.
    ///
    /// The right-hand groups control how the circuit combines the addends.
    fn assert_wrapping_sums_equal<L: Logic<F = Self>, const N: usize>(
        &self,
        adder: &AnalogAdder<'_, L>,
        left: &[Bitvec<L, N>],
        right: &[&[Bitvec<L, N>]],
    ) -> L::Assertions;
}

impl<T> FieldWrappingSum for FpField<T>
where FpField<T>: CompileField
{
    fn assert_wrapping_sums_equal<L: Logic<F = Self>, const N: usize>(
        &self,
        adder: &AnalogAdder<'_, L>,
        left: &[Bitvec<L, N>],
        right: &[&[Bitvec<L, N>]],
    ) -> L::Assertions {
        let right_len = right.iter().map(|group| group.len()).sum::<usize>();
        assert!(!left.is_empty() && right_len > 0);
        let n = left.len() + right_len - 1;

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

        let left_sum = if let [word] = left {
            adder.bv.as_eltw_field(word)
        } else {
            let words: Vec<_> = left.iter().map(|t| adder.bv.as_eltw_field(t)).collect();
            adder.logic.sum(&words)
        };

        let group_sums: Vec<_> = right
            .iter()
            .map(|g| {
                let eltw_g: Vec<_> = g.iter().map(|t| adder.bv.as_eltw_field(t)).collect();
                adder.logic.sum(&eltw_g)
            })
            .collect();
        let right_sum = adder.logic.sum(&group_sums);

        // Shift the smallest possible wrap, 1 - left.len(), to zero.
        let two_to_n = self.pseudo_basis_unsafe(N);
        let difference = adder.logic.sub(&right_sum, &left_sum);
        let shifted_difference = if left.len() == 1 {
            difference
        } else {
            let wraps = adder
                .logic
                .konst(&self.u64_to_element((left.len() - 1) as u64));
            adder
                .logic
                .add(&difference, &adder.logic.mulk(&two_to_n, &wraps))
        };
        let z = adder.logic.precious(&shifted_difference);

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

impl FieldWrappingSum for Gf2_128Field {
    fn assert_wrapping_sums_equal<L: Logic<F = Self>, const N: usize>(
        &self,
        adder: &AnalogAdder<'_, L>,
        left: &[Bitvec<L, N>],
        right: &[&[Bitvec<L, N>]],
    ) -> L::Assertions {
        let right_len = right.iter().map(|group| group.len()).sum::<usize>();
        assert!(!left.is_empty() && right_len > 0);
        let n = left.len() + right_len - 1;
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

        let encoded_left = if let [word] = left {
            inject(word)
        } else {
            let encoded_words: Vec<_> = left.iter().map(&inject).collect();
            adder.logic.prod(&encoded_words)
        };

        // Group-wise injection products
        let mut group_prods = Vec::with_capacity(right.len());
        for g in right {
            let g_inject: Vec<_> = g.iter().map(&inject).collect();
            group_prods.push(adder.logic.prod(&g_inject));
        }

        let encoded_right = adder.logic.prod(&group_prods);

        // R - L can wrap from 1 - left.len() through right_len - 1.
        // Use powers of alpha^(2^N), starting at the lowest wrap.
        let mut roots = vec![adder.logic.one(); n];
        if left.len() > 1 {
            let mut wrap = alpha;
            for _ in 0..N {
                wrap = self.mulf(&wrap, &wrap);
            }
            let inverse_wrap = self.invert(&wrap);
            let mut start = inverse_wrap;
            for _ in 2..left.len() {
                start = self.mulf(&start, &inverse_wrap);
            }
            roots[0] = adder.logic.konst(&start);
        }
        for i in 1..n {
            roots[i] = adder.logic.mul(&roots[i - 1], &alpha_k);
        }

        let mut factors = Vec::with_capacity(n);
        for root in &roots {
            let factor = adder
                .logic
                .sub(&encoded_right, &adder.logic.mul(root, &encoded_left));
            factors.push(factor);
        }

        let prod = adder.logic.prod(&factors);
        adder.logic.assert0("assert_wrapping_sum_gf2", &prod)
    }
}
