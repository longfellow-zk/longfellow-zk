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

use crate::compile::{
    algebra::field::CompileField,
    compiler::{
        ir::{Assertions, Expr, ExprNode},
        quad::{QuadCircuit, Term, WExpr, Wire},
    },
};

// A missing factor describes a term's arity, never a node or circuit input.
const MISSING_FACTOR: Wire = usize::MAX;

struct WireMemoizer {
    cache: std::cell::RefCell<Vec<Option<Wire>>>,
}

impl WireMemoizer {
    fn new() -> Self {
        WireMemoizer {
            cache: std::cell::RefCell::new(Vec::new()),
        }
    }

    fn call<'a, F: CompileField, FUNC>(&self, node: ExprNode<'a, F>, f: FUNC) -> Wire
    where FUNC: FnOnce(&ExprNode<'a, F>) -> Wire {
        let id = node.id;
        {
            let cache = self.cache.borrow();
            if id < cache.len() {
                if let Some(w) = cache[id] {
                    return w;
                }
            }
        }
        let val = f(&node);
        let mut cache = self.cache.borrow_mut();
        if id >= cache.len() {
            cache.resize(id + 1, None);
        }
        cache[id] = Some(val);
        val
    }
}

fn push_node<F: CompileField>(nodes: &mut Vec<WExpr<F>>, n: WExpr<F>) -> Wire {
    let c = nodes.len();
    nodes.push(n);
    c
}

fn walk_eltw<F: CompileField>(
    f: &F,
    ememo: &WireMemoizer,
    nodes: &mut Vec<WExpr<F>>,
    node: ExprNode<'_, F>,
) -> Wire {
    ememo.call(node, |n| match &n.v {
        Expr::Input(position_in_input_array) => {
            let wexpr = WExpr::Input {
                position_in_input_array: position_in_input_array
                    .checked_sub(1)
                    .expect("input zero was reserved by the source API"),
            };
            push_node(nodes, wexpr)
        }
        Expr::Sum(list, _) => {
            assert!(!list.is_empty(), "ir_to_quad: empty list in sum");
            let terms: Vec<Term<F>> = list
                .iter()
                .map(|item| compile_term(f, ememo, nodes, item))
                .collect();
            push_node(nodes, WExpr::Sum(terms))
        }
        Expr::One => MISSING_FACTOR,
        Expr::Quadratic(..) => {
            let term = compile_term(f, ememo, nodes, n);
            if term.1 == MISSING_FACTOR && term.2 == MISSING_FACTOR && term.0 == f.one() {
                MISSING_FACTOR
            } else {
                push_node(nodes, WExpr::Sum(vec![term]))
            }
        }
        Expr::Constant(_) | Expr::Linear(..) | Expr::WithAssertions(..) => {
            panic!("ir_to_quad: unexpected expression variant: {n:?}")
        }
    })
}

fn compile_term<F: CompileField>(
    f: &F,
    ememo: &WireMemoizer,
    nodes: &mut Vec<WExpr<F>>,
    node: &ExprNode<'_, F>,
) -> Term<F> {
    match &node.v {
        Expr::Quadratic(e, x, y) => {
            assert!(!f.is_zero(e));
            let wx = walk_eltw(f, ememo, nodes, *x);
            let wy = walk_eltw(f, ememo, nodes, *y);
            ((*e).clone(), wx, wy)
        }
        Expr::Input(_) => {
            let w = walk_eltw(f, ememo, nodes, *node);
            (f.one(), MISSING_FACTOR, w)
        }
        Expr::One => (f.one(), MISSING_FACTOR, MISSING_FACTOR),
        _ => panic!("ir_to_quad: expected term node, got {node:?}"),
    }
}

use crate::compile::logic::scope::{AssertionId, AssertionScope};

/// Rewrite into a stylized Quad circuit with debug info mapping quad node index
/// to assertion ID.
pub fn rewrite<'src, 'dst, F: CompileField>(
    _arena: &'dst crate::compile::compiler::arena::CompilerArena<'dst, F>,
    f: &'dst F,
    x: Assertions<'src, F>,
    tracker: &AssertionScope,
) -> (QuadCircuit<F>, Vec<(usize, AssertionId)>) {
    let mut nodes = Vec::new();
    let mut quad_asserts = Vec::new();
    let ememo = WireMemoizer::new();
    let mut assertion_factors = rustc_hash::FxHashMap::default();
    for item in x.iter() {
        {
            let (a, b) = match &item.expr.v {
                Expr::Quadratic(e, x, y) => {
                    assert!(!f.is_zero(e));
                    (
                        walk_eltw(f, &ememo, &mut nodes, *x),
                        walk_eltw(f, &ememo, &mut nodes, *y),
                    )
                }
                _ => (walk_eltw(f, &ememo, &mut nodes, item.expr), MISSING_FACTOR),
            };
            let (a, b) = (a.min(b), a.max(b));
            assert!(
                a != MISSING_FACTOR,
                "cannot satisfy a nonzero constant assertion"
            );
            if let Some(&id) = assertion_factors.get(&(a, b)) {
                tracker.union(id, item.id);
            } else {
                let node = if b == MISSING_FACTOR {
                    WExpr::Assert0(a)
                } else {
                    WExpr::Sum(vec![(f.zero(), a, b)])
                };
                let index = push_node(&mut nodes, node);
                assertion_factors.insert((a, b), item.id);
                quad_asserts.push((index, item.id));
            }
        }
    }
    (QuadCircuit { nodes }, quad_asserts)
}
