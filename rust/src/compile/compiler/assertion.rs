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
    algebra::CompileField,
    compiler::{
        algsimp::AlgebraicRewriter,
        arena::{walk, CompilerArena},
        cse::Cse,
        ir::{AssertionItem, Assertions, ExprNode, RawAssertions, RewriteT},
    },
    logic::AssertionScope,
};

fn dedup_assertions<'a, F: CompileField>(
    arena: &'a CompilerArena<'a, F>,
    assertions: &[AssertionItem<'a, F>],
    tracker: &AssertionScope,
) -> Assertions<'a, F> {
    // Keep the first occurrence of each expression, in input order. The map
    // is only searched: iterating it would make the circuit depend on hash
    // order, which differs between hosts.
    let mut first = rustc_hash::FxHashMap::default();
    let mut unique = Vec::new();
    for item in assertions {
        if let Some(&existing) = first.get(&item.expr.id) {
            tracker.union(existing, item.id);
        } else {
            first.insert(item.expr.id, item.id);
            unique.push(*item);
        }
    }
    arena.alloc_slice(&unique)
}

/// A rewriter that strips all nested `WithAssertions` nodes from an expression
/// tree, collecting them into a side channel (`collected`) while delegating all
/// other node constructions to a generic `NEXT` rewriter (typically `Cse`).
struct StripRewriter<'re, 'a, F: CompileField, NEXT> {
    next: &'re NEXT,
    collected: std::cell::RefCell<Vec<AssertionItem<'a, F>>>,
}

/// Separate the root expressions from assertions carried by their wires.
pub(super) fn strip_attached<'a, F: CompileField>(
    arena: &'a CompilerArena<'a, F>,
    assertions: Assertions<'a, F>,
) -> (Assertions<'a, F>, Vec<AssertionItem<'a, F>>) {
    let rewriter = StripRewriter {
        next: &Cse::new(arena),
        collected: std::cell::RefCell::new(Vec::new()),
    };
    let roots = walk(arena, assertions, &rewriter);
    (roots, rewriter.collected.into_inner())
}

impl<'re, 'a, F: CompileField, NEXT: RewriteT<'a, F>> RewriteT<'a, F>
    for StripRewriter<'re, 'a, F, NEXT>
{
    fn ok(&self) -> RawAssertions<'a, F> {
        self.next.ok()
    }

    fn assert0(&self, x: &ExprNode<'a, F>) -> RawAssertions<'a, F> {
        self.next.assert0(x)
    }

    fn assertions(&self, assertions: &[RawAssertions<'a, F>]) -> RawAssertions<'a, F> {
        self.next.assertions(assertions)
    }

    fn input(&self, position_in_input_array: usize) -> ExprNode<'a, F> {
        self.next.input(position_in_input_array)
    }

    fn sum(&self, elements: &[ExprNode<'a, F>], precious: bool) -> ExprNode<'a, F> {
        self.next.sum(elements, precious)
    }

    fn one(&self) -> ExprNode<'a, F> {
        self.next.one()
    }

    fn constant(&self, elt: &F::E) -> ExprNode<'a, F> {
        self.next.constant(elt)
    }

    fn linear(&self, elt: &F::E, x: &ExprNode<'a, F>) -> ExprNode<'a, F> {
        self.next.linear(elt, x)
    }

    fn quadratic(&self, elt: &F::E, x: &ExprNode<'a, F>, y: &ExprNode<'a, F>) -> ExprNode<'a, F> {
        self.next.quadratic(elt, x, y)
    }

    fn with_assertions(
        &self,
        assertions: &Assertions<'a, F>,
        x: &ExprNode<'a, F>,
    ) -> ExprNode<'a, F> {
        self.collected
            .borrow_mut()
            .extend(assertions.iter().cloned());
        // Strip the assertions by returning the inner expression directly
        x
    }
}

/// Recursively walks the expression DAG and strips all `WithAssertions` nodes
/// using a `Cse` rewriter, returning a single flattened assertion set in target arena ('dst).
fn strip_all<'src, 'dst, F: CompileField>(
    arena: &'dst CompilerArena<'dst, F>,
    assertions: Assertions<'src, F>,
    tracker: &AssertionScope,
) -> Assertions<'dst, F> {
    let cse = Cse::new(arena);
    let rewriter = StripRewriter {
        next: &cse,
        collected: std::cell::RefCell::new(Vec::new()),
    };

    // Perform initial walk from source assertions to destination arena.
    let stripped_slice = walk(arena, assertions, &rewriter);
    let new_sub_exprs = rewriter.collected.replace(Vec::new());

    if new_sub_exprs.is_empty() {
        return dedup_assertions(arena, stripped_slice, tracker);
    }

    let mut current_items = stripped_slice.to_vec();
    current_items.extend(new_sub_exprs);

    loop {
        let unique_items = dedup_assertions(arena, &current_items, tracker);
        let next_stripped = walk(arena, unique_items, &rewriter);
        let next_sub_exprs = rewriter.collected.replace(Vec::new());

        if next_sub_exprs.is_empty() {
            current_items = next_stripped.to_vec();
            break;
        }

        let mut next_items = next_stripped.to_vec();
        next_items.extend(next_sub_exprs);
        current_items = next_items;
    }

    dedup_assertions(arena, &current_items, tracker)
}

/// Rewrite function performing algebraic simplification with CSE after
/// stripping all assertions from the DAG, rewriting into target arena ('dst).
pub fn rewrite<'src, 'dst, F: CompileField>(
    arena: &'dst CompilerArena<'dst, F>,
    f: &'dst F,
    assertions: &'src [AssertionItem<'src, F>],
    tracker: &AssertionScope,
    expand_bilinear: bool,
) -> Assertions<'dst, F> {
    let stripped = strip_all(arena, assertions, tracker);
    let cse = Cse::new(arena);
    let algebraic = AlgebraicRewriter::with_bilinear_expansion(f, cse, expand_bilinear);
    let rewritten = walk(arena, stripped, &algebraic);
    dedup_assertions(arena, rewritten, tracker)
}
