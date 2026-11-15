// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Integer equations without Boolean carry circuits. Witnesses remain bounded
//! bit vectors: encode n as n in prime fields, or g^n in GF(2^128).
use crate::{
    circuits::{
        bitvec::Bitvec,
        boolean::{Bitw, Boolean},
    },
    compile::{
        algebra::CompileField,
        logic::{Eltw, Logic},
    },
    core::algebra::{AlgebraicField, ElementOf, SerializableField},
};

pub(in crate::mdoc::circuits) struct Counter<'a, L: Logic> {
    logic: &'a L,
    boolean: Boolean<'a, L>,
    binary: bool,
    powers: Vec<ElementOf<L::F>>,
}

fn pow<F: CompileField>(f: &F, base: &ElementOf<F>, mut exponent: u128) -> ElementOf<F> {
    let mut result = f.one();
    let mut power = base.clone();
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = f.mulf(&result, &power);
        }
        power = f.mulf(&power, &power);
        exponent >>= 1;
    }
    result
}

impl<'a, L: Logic> Counter<'a, L> {
    /// Extend the modular encoding for raw argument bytes. These intermediates
    /// need not represent bounded counters: the lexer checks their integer
    /// bit-vector bounds before they affect an accepted length or arity.
    pub(in crate::mdoc::circuits) fn widened(&self, bits: usize) -> Self {
        assert!((self.powers.len()..=16).contains(&bits));
        let mut powers = self.powers.clone();
        while powers.len() < bits {
            let last = powers.last().unwrap();
            powers.push(if self.binary {
                self.logic.field().mulf(last, last)
            } else {
                self.logic.field().addf(last, last)
            });
        }
        Self {
            logic: self.logic,
            boolean: Boolean::new(self.logic),
            binary: self.binary,
            powers,
        }
    }

    pub(in crate::mdoc::circuits) fn new(logic: &'a L, bits: usize) -> Self {
        assert!((5..=16).contains(&bits));
        let f = logic.field();
        let binary = f.is_binary();
        let base = if binary {
            assert_eq!(
                f.pseudo_dimension(),
                128,
                "binary counters require GF(2^128)"
            );
            let g = f.pseudo_basis(1);
            assert!(!f.is_zero(&g));
            // P is a prime divisor of 2^128-1. This test forces the order of g
            // to contain P, hence exceed every possible difference between
            // the bounded integers in our equations (less than 2^17).
            const P: u128 = 6_700_417;
            assert_eq!(u128::MAX % P, 0);
            assert!(
                pow(f, &g, u128::MAX / P) != f.one(),
                "counter base has insufficient order"
            );
            g
        } else {
            // Nonbinary compiler fields use powers of two in the prime
            // subfield as their pseudo-basis. Its dimension is the floor
            // of log2(characteristic), including for the sextic field.
            assert!(f.pseudo_dimension() > bits, "counter field too small");
            f.one()
        };
        let mut power = base;
        let powers = (0..bits)
            .map(|_| {
                let result = power.clone();
                power = if binary {
                    f.mulf(&power, &power)
                } else {
                    f.addf(&power, &power)
                };
                result
            })
            .collect();
        Self {
            logic,
            boolean: Boolean::new(logic),
            binary,
            powers,
        }
    }

    pub(in crate::mdoc::circuits) fn constant(&self, n: u64) -> Eltw<L> {
        assert!(
            n < 1u64 << self.powers.len(),
            "counter constant does not fit"
        );
        let f = self.logic.field();
        let mut value = if self.binary { f.one() } else { f.zero() };
        for (i, power) in self.powers.iter().enumerate() {
            if n >> i & 1 != 0 {
                value = if self.binary {
                    f.mulf(&value, power)
                } else {
                    f.addf(&value, power)
                };
            }
        }
        self.logic.konst(&value)
    }

    pub(in crate::mdoc::circuits) fn encode<const N: usize>(&self, n: &Bitvec<L, N>) -> Eltw<L> {
        assert_eq!(N, self.powers.len());
        let terms: Vec<_> = n
            .iter()
            .zip(&self.powers)
            .map(|(bit, power)| {
                let field_bit = self.boolean.as_eltw(bit);
                if self.binary {
                    self.logic.add(
                        &self.logic.one(),
                        &self.logic.mulk(
                            &self.logic.field().subf(power, &self.logic.field().one()),
                            &field_bit,
                        ),
                    )
                } else {
                    self.logic.mulk(power, &field_bit)
                }
            })
            .collect();
        if self.binary {
            self.logic.prod(&terms)
        } else {
            self.logic.sum(&terms)
        }
    }

    pub(in crate::mdoc::circuits) fn add(&self, a: &Eltw<L>, b: &Eltw<L>) -> Eltw<L> {
        if self.binary {
            self.logic.mul(a, b)
        } else {
            self.logic.add(a, b)
        }
    }

    pub(in crate::mdoc::circuits) fn select(
        &self,
        bit: &Bitw<L>,
        a: &Eltw<L>,
        b: &Eltw<L>,
    ) -> Eltw<L> {
        self.logic.add(
            b,
            &self
                .logic
                .mul(&self.boolean.as_eltw(bit), &self.logic.sub(a, b)),
        )
    }

    pub(in crate::mdoc::circuits) fn increment(&self, value: &Eltw<L>, bit: &Bitw<L>) -> Eltw<L> {
        self.add(
            value,
            &self.select(bit, &self.constant(1), &self.constant(0)),
        )
    }
}

#[cfg(test)]
mod tests;
