// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V1 quadratic terms retain the reserved One wire.
pub(crate) use crate::compile::compiler::graph::Wire;
use crate::{
    compile::compiler::graph::{Graph, Node},
    core::algebra::ElementOf,
};
pub(crate) type Term<F> = (ElementOf<F>, Wire, Wire);
pub(crate) type WExpr<F> = Node<Term<F>>;
pub(crate) type QuadCircuit<F> = Graph<Term<F>>;
