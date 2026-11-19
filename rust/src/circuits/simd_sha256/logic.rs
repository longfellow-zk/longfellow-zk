// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Compiler policy local to the packed SHA circuit. Ordinary compilers keep
//! their existing Boolean operations; no runtime or witness state is mutated.
use crate::{
    compile::{
        algebra::gf2_128::Gf2_128Field,
        compiler::{ir::ExprNode, CompilerAssertions, CompilerLogic},
        logic::{Logic, LogicIO},
    },
    core::algebra::ElementOf,
};
pub(super) struct BinaryLogic<'a>(pub CompilerLogic<'a, Gf2_128Field>);
impl<'a> Logic for BinaryLogic<'a> {
    type F = Gf2_128Field;
    type Wire = ExprNode<'a, Gf2_128Field>;
    type Assertions = CompilerAssertions<'a, Gf2_128Field>;
    fn field(&self) -> &Self::F {
        self.0.field()
    }
    fn zero(&self) -> Self::Wire {
        self.0.zero()
    }
    fn one(&self) -> Self::Wire {
        self.0.one()
    }
    fn konst(&self, x: &ElementOf<Self::F>) -> Self::Wire {
        self.0.konst(x)
    }
    fn precious(&self, x: &Self::Wire) -> Self::Wire {
        self.0.precious(x)
    }
    fn sum(&self, x: &[Self::Wire]) -> Self::Wire {
        self.0.sum(x)
    }
    fn neg(&self, x: &Self::Wire) -> Self::Wire {
        self.0.neg(x)
    }
    fn add(&self, x: &Self::Wire, y: &Self::Wire) -> Self::Wire {
        self.0.add(x, y)
    }
    fn sub(&self, x: &Self::Wire, y: &Self::Wire) -> Self::Wire {
        self.0.sub(x, y)
    }
    fn mul(&self, x: &Self::Wire, y: &Self::Wire) -> Self::Wire {
        self.0.mul(&self.0.precious(x), &self.0.precious(y))
    }
    fn mulk(&self, k: &ElementOf<Self::F>, x: &Self::Wire) -> Self::Wire {
        self.0.mulk(k, x)
    }
    fn quadratic(&self, k: &ElementOf<Self::F>, x: &Self::Wire, y: &Self::Wire) -> Self::Wire {
        self.0.quadratic(k, x, y)
    }
    fn ok(&self) -> Self::Assertions {
        self.0.ok()
    }
    fn assert0(&self, n: &str, x: &Self::Wire) -> Self::Assertions {
        self.0.assert0(n, x)
    }
    fn assert_all(&self, n: &str, x: &[Self::Assertions]) -> Self::Assertions {
        self.0.assert_all(n, x)
    }
    fn assert_when(&self, enable: &Self::Wire, assertions: Self::Assertions) -> Self::Assertions {
        self.0.assert_when(enable, assertions)
    }
    fn with_assertions(&self, a: Self::Assertions, x: &Self::Wire) -> Self::Wire {
        self.0.with_assertions(a, x)
    }
    fn to_stringw_debug(&self, x: &Self::Wire) -> String {
        self.0.to_stringw_debug(x)
    }
}
impl LogicIO for BinaryLogic<'_> {
    fn input(&self, i: usize) -> Self::Wire {
        self.0.input(i)
    }
}

impl Depth for BinaryLogic<'_> {
    fn wire_depth(&self, x: &Self::Wire) -> usize {
        x.depth
    }
}
/// This circuit orders carry-save operands by the compiler's multiplication
/// depth. Keep that scheduling policy local to this experimental circuit.
pub(super) trait Depth: Logic {
    fn wire_depth(&self, x: &Self::Wire) -> usize;
}
