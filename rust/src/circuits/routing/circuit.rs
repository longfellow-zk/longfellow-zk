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
        arithmetic::Arithmetic,
        bitvec::{Bitvec, BitvecLogic},
        boolean::{Bitw, Boolean},
    },
    compile::logic::{Eltw, Logic},
};

fn extend<T: Clone>(a: &[T], default: &T, i: isize) -> T {
    let n = a.len() as isize;
    if i >= 0 && i < n {
        a[i as usize].clone()
    } else {
        default.clone()
    }
}

fn really_shift<L: Logic, T: Clone, FMux>(
    mux: &FMux,
    selector: &[Bitw<L>],
    n: usize,
    k: usize,
    a: &mut [T],
    shift: usize,
    default: &T,
) where
    FMux: Fn(&[Bitw<L>], &dyn Fn(usize) -> T) -> T,
{
    let aa = a.to_vec();
    let limit = n.min(k.saturating_add(shift));
    for (i, elem) in a.iter_mut().enumerate().take(limit) {
        *elem = mux(selector, &|j| {
            extend(&aa, default, (i + j * shift) as isize)
        });
    }
}

pub struct Routing<'a, L: Logic> {
    logic: &'a L,
    arith: Arithmetic<'a, L>,
}

impl<'a, L: Logic> Routing<'a, L> {
    pub fn new(logic: &'a L) -> Self {
        Self {
            logic,
            arith: Arithmetic::new(logic),
        }
    }

    fn amount_selector(&self, logc: usize, amount: &[Bitw<L>], l: usize) -> Vec<Bitw<L>> {
        let c = 1 << logc;
        let consumed_amount: Vec<Bitw<L>> = (0..logc).map(|k| amount[l + k].clone()).collect();
        let eq_fn = |x: &[Bitw<L>], y: &[Bitw<L>]| self.arith.eqb(x, y);
        (0..c)
            .map(|val| self.arith.relint(&eq_fn, &consumed_amount, val as u64))
            .collect()
    }

    fn generic_shift<T: Clone, FMux>(
        &self,
        mux: &FMux,
        unroll: usize,
        amount: &[Bitw<L>],
        k: usize,
        a: &[T],
        default: &T,
    ) -> Vec<T>
    where
        FMux: Fn(&[Bitw<L>], &dyn Fn(usize) -> T) -> T,
    {
        let n = a.len();
        let logn = amount.len();
        let mut tmp = a.to_vec();

        assert!(unroll > 0, "unroll parameter must be > 0");
        let mut l = logn;
        let mut target_nrounds = logn.div_ceil(unroll);

        while target_nrounds > 0 {
            let consumed = l.div_ceil(target_nrounds);
            l -= consumed;
            let shift = 1 << l;
            let selector = self.amount_selector(consumed, amount, l);
            really_shift(mux, &selector, n, k, &mut tmp, shift, default);
            target_nrounds -= 1;
        }

        (0..k)
            .map(|i| {
                if i < n {
                    tmp[i].clone()
                } else {
                    default.clone()
                }
            })
            .collect()
    }

    /// Shift `a` left by `amount` elements, filling with zeros: the same
    /// function as `shift_bitvec` with a zero default, with the stages given
    /// explicitly as a nonempty list of positive widths. Stage `s` decodes
    /// the next `groups[s]` amount bits below those of the previous stages,
    /// starting from bit `sum(groups) - 1`.
    /// Higher amount bits shift every element out (`a.len()` must not exceed
    /// `1 << sum(groups)`); the last stage's selectors check that they are
    /// zero.
    ///
    /// A stage cannot start before its selector, so the data of the first
    /// stage is carried up to the depth of the first selector. Those copies
    /// depend only on `a`, and shifts of one array share them; a narrow first
    /// group keeps them shallow, while a wide one shortens the stages that
    /// follow.
    pub fn shift_bitvec_grouped<const N: usize, const M: usize>(
        &self,
        groups: &[usize],
        amount: &Bitvec<L, M>,
        k: usize,
        a: &[Bitvec<L, N>],
    ) -> Vec<Bitvec<L, N>> {
        let bv_logic = BitvecLogic::new(self.logic);
        let mux =
            |sel: &[Bitw<L>], data: &dyn Fn(usize) -> Bitvec<L, N>| bv_logic.one_hot_mux(sel, data);
        self.grouped_shift(groups, amount.as_array(), k, a, bv_logic.zero(), &mux)
    }

    /// `shift_bitvec_grouped` for field elements, such as packed bytes: each
    /// stage costs one term per element and selector value, instead of one
    /// per bit.
    pub fn shift_eltw_grouped<const M: usize>(
        &self,
        groups: &[usize],
        amount: &Bitvec<L, M>,
        k: usize,
        a: &[Eltw<L>],
    ) -> Vec<Eltw<L>> {
        let boolean = Boolean::new(self.logic);
        let mux = |sel: &[Bitw<L>], data: &dyn Fn(usize) -> Eltw<L>| {
            let terms: Vec<_> = sel
                .iter()
                .enumerate()
                .map(|(j, s)| {
                    let datum = self.logic.precious(&data(j));
                    self.logic.mul(&boolean.as_eltw(s), &datum)
                })
                .collect();
            self.logic.sum(&terms)
        };
        self.grouped_shift(groups, amount.as_array(), k, a, self.logic.zero(), &mux)
    }

    fn grouped_shift<T: Clone, FMux>(
        &self,
        groups: &[usize],
        bits: &[Bitw<L>],
        k: usize,
        a: &[T],
        zero: T,
        mux: &FMux,
    ) -> Vec<T>
    where
        FMux: Fn(&[Bitw<L>], &dyn Fn(usize) -> T) -> T,
    {
        assert!(
            !groups.is_empty() && groups.iter().all(|&w| w > 0),
            "shift groups must be nonempty and have positive widths",
        );
        let total = groups
            .iter()
            .try_fold(0usize, |total, &w| total.checked_add(w))
            .expect("shift group widths overflow");
        assert!(total < usize::BITS as usize, "too many shift address bits");
        assert!(total <= bits.len() && a.len() <= 1 << total);
        let boolean = Boolean::new(self.logic);
        let high_zero = (total < bits.len()).then(|| {
            let eq_fn = |x: &[Bitw<L>], y: &[Bitw<L>]| self.arith.eqb(x, y);
            self.arith.relint(&eq_fn, &bits[total..], 0)
        });
        let n = a.len();
        let mut tmp = a.to_vec();
        let mut l = total;
        for (stage, &consumed) in groups.iter().enumerate() {
            l -= consumed;
            let mut selector = self.amount_selector(consumed, bits, l);
            if let (Some(all_zero), true) = (&high_zero, stage + 1 == groups.len()) {
                for sel in &mut selector {
                    *sel = boolean.tree_andb(sel, all_zero);
                }
            }
            really_shift(mux, &selector, n, k, &mut tmp, 1 << l, &zero);
        }
        tmp.resize(k, zero);
        tmp
    }

    pub fn shift_bitvec<const N: usize, const M: usize>(
        &self,
        unroll: usize,
        amount: &Bitvec<L, M>,
        k: usize,
        a: &[Bitvec<L, N>],
        default: &Bitvec<L, N>,
    ) -> Vec<Bitvec<L, N>> {
        let bv_logic = BitvecLogic::new(self.logic);
        let mux =
            |sel: &[Bitw<L>], data: &dyn Fn(usize) -> Bitvec<L, N>| bv_logic.one_hot_mux(sel, data);
        self.generic_shift(&mux, unroll, amount.as_array(), k, a, default)
    }
}
