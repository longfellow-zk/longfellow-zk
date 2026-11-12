// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V1 quadratic terms retain the reserved One wire.
pub(crate) use crate::compile::compiler::graph::Wire;
use crate::core::algebra::ElementOf;
pub(crate) type Term<F> = (ElementOf<F>, Wire, Wire);
pub(crate) type WExpr<F> = crate::compile::compiler::graph::Node<Term<F>>;
pub(crate) type QuadCircuit<F> = crate::compile::compiler::graph::Graph<Term<F>>;
