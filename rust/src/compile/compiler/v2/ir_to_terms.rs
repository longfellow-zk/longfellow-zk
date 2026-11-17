// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Lower depth-aligned v2 expressions into native term arities.

use rustc_hash::FxHashMap;

use super::terms::{CircuitGraph, Node, Term};
use crate::compile::{
    algebra::CompileField,
    compiler::{
        graph::{push_node, Wire, WireMemoizer},
        ir::{Assertions, Expr, ExprNode},
    },
    logic::{AssertionId, AssertionScope},
};

fn walk_wire<F: CompileField>(
    f: &F,
    memo: &WireMemoizer,
    nodes: &mut Vec<Node<F>>,
    node: ExprNode<'_, F>,
) -> Wire {
    memo.call(node, |n| match &n.v {
        Expr::Input(position) => push_node(
            nodes,
            Node::Input {
                position_in_input_array: position
                    .checked_sub(1)
                    .expect("input zero was reserved by the source API"),
            },
        ),
        Expr::Sum(list, _) => {
            assert!(!list.is_empty(), "ir_to_terms: empty sum");
            let terms = list
                .iter()
                .map(|item| compile_term(f, memo, nodes, item))
                .collect();
            push_node(nodes, Node::Sum(terms))
        }
        Expr::Linear(..) | Expr::Quadratic(..) => {
            let term = compile_term(f, memo, nodes, n);
            push_node(nodes, Node::Sum(vec![term]))
        }
        Expr::One | Expr::Constant(_) | Expr::WithAssertions(..) => {
            panic!("ir_to_terms: unexpected wire expression variant: {n:?}")
        }
    })
}

fn compile_term<F: CompileField>(
    f: &F,
    memo: &WireMemoizer,
    nodes: &mut Vec<Node<F>>,
    node: &ExprNode<'_, F>,
) -> Term<F> {
    match &node.v {
        Expr::Quadratic(k, x, y) => {
            assert!(!f.is_zero(k));
            let left = walk_wire(f, memo, nodes, *x);
            let right = walk_wire(f, memo, nodes, *y);
            Term::Quadratic((*k).clone(), [left, right])
        }
        Expr::Linear(k, x) => {
            assert!(!f.is_zero(k));
            let w = walk_wire(f, memo, nodes, *x);
            Term::Linear((*k).clone(), w)
        }
        Expr::Constant(k) => {
            assert!(!f.is_zero(k));
            Term::Constant((*k).clone())
        }
        _ => panic!("ir_to_terms: expected term node, got {node:?}"),
    }
}

pub(super) fn rewrite<F: CompileField>(
    f: &F,
    assertions: Assertions<'_, F>,
    tracker: &AssertionScope,
) -> (CircuitGraph<F>, Vec<(usize, AssertionId)>) {
    let mut nodes = Vec::new();
    let mut records = Vec::new();
    let memo = WireMemoizer::new();
    let mut assertion_inputs = FxHashMap::default();
    for item in assertions {
        let key = match &item.expr.v {
            Expr::Quadratic(k, x, y) => {
                assert!(!f.is_zero(k));
                let a = walk_wire(f, &memo, &mut nodes, *x);
                let b = walk_wire(f, &memo, &mut nodes, *y);
                (a.min(b), Some(a.max(b)))
            }
            _ => (walk_wire(f, &memo, &mut nodes, item.expr), None),
        };
        if let Some(&id) = assertion_inputs.get(&key) {
            tracker.union(id, item.id);
        } else {
            let node = match key {
                (a, Some(b)) => Node::Sum(vec![Term::Quadratic(f.zero(), [a, b])]),
                (a, None) => Node::Assert0(a),
            };
            let index = push_node(&mut nodes, node);
            assertion_inputs.insert(key, item.id);
            records.push((index, item.id));
        }
    }
    // Traversal starts at assertion roots and creates only their dependencies.
    // A repeated assertion key can only reuse memoized wires, so it creates
    // no orphan nodes. The scheduler checks this invariant independently.
    (CircuitGraph { nodes }, records)
}
