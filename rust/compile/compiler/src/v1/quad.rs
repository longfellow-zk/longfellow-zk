// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V1 quadratic terms retain the reserved One wire.
pub use crate::compile::compiler::graph::Wire;
use crate::core::algebra::ElementOf;
pub type Term<F> = (ElementOf<F>, Wire, Wire);
pub type WExpr<F> = crate::compile::compiler::graph::Node<Term<F>>;
pub type QuadCircuit<F> = crate::compile::compiler::graph::Graph<Term<F>>;
