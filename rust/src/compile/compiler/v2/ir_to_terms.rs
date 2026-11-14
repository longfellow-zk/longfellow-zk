// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Lower source expressions into explicit native term arities.
use super::terms::{CircuitGraph, Node, Term};
use crate::compile::{
    algebra::field::CompileField,
    compiler::{
        graph::{push_node, Wire, WireMemoizer},
        ir::{Assertions, Expr, ExprNode},
    },
    logic::scope::{AssertionId, AssertionScope},
};

// None denotes the source multiplicative identity, which has no native wire.
fn walk_factor<F: CompileField>(
    f: &F,
    memo: &WireMemoizer<Option<Wire>>,
    nodes: &mut Vec<Node<F>>,
    node: ExprNode<'_, F>,
) -> Option<Wire> {
    memo.call(node, |n| match &n.v {
        Expr::Input(position) => Some(push_node(
            nodes,
            Node::Input {
                position_in_input_array: position
                    .checked_sub(1)
                    .expect("input zero was reserved by the source API"),
            },
        )),
        Expr::Sum(list, _) => {
            assert!(!list.is_empty(), "ir_to_terms: empty sum");
            let terms = list
                .iter()
                .map(|item| compile_term(f, memo, nodes, item))
                .collect();
            Some(push_node(nodes, Node::Sum(terms)))
        }
        Expr::One => None,
        Expr::Quadratic(..) => {
            let term = compile_term(f, memo, nodes, n);
            if matches!(&term, Term::Constant(k) if *k == f.one()) {
                None
            } else {
                Some(push_node(nodes, Node::Sum(vec![term])))
            }
        }
        Expr::Constant(_) | Expr::Linear(..) | Expr::WithAssertions(..) => {
            panic!("ir_to_terms: unexpected expression variant: {n:?}")
        }
    })
}
fn compile_term<F: CompileField>(
    f: &F,
    memo: &WireMemoizer<Option<Wire>>,
    nodes: &mut Vec<Node<F>>,
    node: &ExprNode<'_, F>,
) -> Term<F> {
    match &node.v {
        Expr::Quadratic(k, x, y) => {
            assert!(!f.is_zero(k));
            match (
                walk_factor(f, memo, nodes, *x),
                walk_factor(f, memo, nodes, *y),
            ) {
                (Some(left), Some(right)) => Term::Quadratic((*k).clone(), [left, right]),
                (Some(w), None) | (None, Some(w)) => Term::Linear((*k).clone(), w),
                (None, None) => Term::Constant((*k).clone()),
            }
        }
        Expr::Input(_) => Term::Linear(f.one(), walk_factor(f, memo, nodes, *node).unwrap()),
        Expr::One => Term::Constant(f.one()),
        _ => panic!("ir_to_terms: expected term node, got {node:?}"),
    }
}

pub(super) fn rewrite<'src, 'dst, F: CompileField>(
    _arena: &'dst crate::compile::compiler::arena::CompilerArena<'dst, F>,
    f: &'dst F,
    assertions: Assertions<'src, F>,
    tracker: &AssertionScope,
) -> (CircuitGraph<F>, Vec<(usize, AssertionId)>) {
    let mut nodes = Vec::new();
    let mut records = Vec::new();
    let memo = WireMemoizer::new();
    let mut assertion_inputs = rustc_hash::FxHashMap::default();
    for item in assertions {
        let factors = match &item.expr.v {
            Expr::Quadratic(k, x, y) => {
                assert!(!f.is_zero(k));
                (
                    walk_factor(f, &memo, &mut nodes, *x),
                    walk_factor(f, &memo, &mut nodes, *y),
                )
            }
            _ => (walk_factor(f, &memo, &mut nodes, item.expr), None),
        };
        let key = match factors {
            (Some(a), Some(b)) => (a.min(b), Some(a.max(b))),
            (Some(w), None) | (None, Some(w)) => (w, None),
            (None, None) => panic!("cannot satisfy a nonzero constant assertion"),
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
    (CircuitGraph { nodes }, records)
}
