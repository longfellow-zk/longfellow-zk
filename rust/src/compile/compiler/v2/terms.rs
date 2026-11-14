// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Native term arities: every stored operand is a real wire.
use graph::Wire;

use crate::compile::{algebra::field::CompileField, compiler::graph};

pub(super) enum Term<F: CompileField> {
    Quadratic(F::E, [Wire; 2]),
    Linear(F::E, Wire),
    Constant(F::E),
}
impl<F: CompileField> Term<F> {
    pub(super) fn coefficient(&self) -> &F::E {
        match self {
            Self::Quadratic(k, _) | Self::Linear(k, _) | Self::Constant(k) => k,
        }
    }
    pub(super) fn inputs(&self) -> &[Wire] {
        match self {
            Self::Quadratic(_, wires) => wires,
            Self::Linear(_, wire) => std::slice::from_ref(wire),
            Self::Constant(_) => &[],
        }
    }
    pub(super) fn rename(&self, mut wire: impl FnMut(Wire) -> Wire) -> Self {
        match self {
            Self::Quadratic(k, [left, right]) => {
                let mut wires = [wire(*left), wire(*right)];
                wires.sort_unstable();
                Self::Quadratic(k.clone(), wires)
            }
            Self::Linear(k, w) => Self::Linear(k.clone(), wire(*w)),
            Self::Constant(k) => Self::Constant(k.clone()),
        }
    }
}
pub(super) type Node<F> = graph::Node<Term<F>>;
pub(super) type CircuitGraph<F> = graph::Graph<Term<F>>;
