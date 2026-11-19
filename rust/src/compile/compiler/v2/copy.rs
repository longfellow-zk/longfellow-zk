// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Longfellow v2 depth-alignment copy pass using native `1 * x` linear terms.

use crate::compile::{
    algebra::CompileField,
    compiler::{
        arena::{walk_roots, CompilerArena},
        assertion::dedup_assertions,
        cse::Cse,
        ir::{Assertions, Expr, ExprNode, RawAssertions, RewriteT},
    },
    logic::AssertionScope,
};

/// Introduce depth-alignment copy wires for v2 using `Linear(1, x)` terms and
/// attach sum constants directly at the sum's output depth, with no `One` wire
/// or `one_at_depth` chain.
pub(in crate::compile::compiler) struct CopyRewriter<'a, F: CompileField, NEXT> {
    f: &'a F,
    next: NEXT,
}

fn depth_term<F: CompileField>(node: &ExprNode<'_, F>) -> usize {
    match &node.v {
        Expr::Linear(_, _) | Expr::Quadratic(_, _, _) => node.depth,
        _ => panic!("v2::copy::depth_term: unexpected node variant: {node:?}"),
    }
}

impl<'a, F: CompileField, NEXT> CopyRewriter<'a, F, NEXT>
where NEXT: RewriteT<'a, F>
{
    pub(in crate::compile::compiler) fn new(f: &'a F, next: NEXT) -> Self {
        Self { f, next }
    }

    fn ground_quadratic(
        &self,
        e: &F::E,
        x: &ExprNode<'a, F>,
        y: &ExprNode<'a, F>,
    ) -> ExprNode<'a, F> {
        assert_eq!(x.depth, y.depth);
        self.next.quadratic(e, x, y)
    }

    fn copy(&self, x: &ExprNode<'a, F>) -> ExprNode<'a, F> {
        match &x.v {
            // Lift any constant factor off a copied term so the underlying
            // unit product or unit copy wire shares CSE in lower layers.
            Expr::Quadratic(e1, x1, y1) => {
                let sub_quad = self.ground_quadratic(&self.f.one(), x1, y1);
                self.next.linear(e1, &sub_quad)
            }
            Expr::Linear(e1, x1) if *e1 != &self.f.one() => {
                let sub_copy = self.next.linear(&self.f.one(), x1);
                self.next.linear(e1, &sub_copy)
            }
            Expr::Constant(_) | Expr::One => {
                panic!("v2::copy: constants must not be copied across layers")
            }
            _ => self.next.linear(&self.f.one(), x),
        }
    }

    fn lift(&self, d: usize, x: &ExprNode<'a, F>) -> ExprNode<'a, F> {
        let mut current = *x;
        loop {
            let cx = depth_term(&current);
            if cx == d {
                return current;
            }
            assert!(cx < d, "v2::copy::lift: depth too high ({cx} > {d})");
            current = self.copy(&current);
        }
    }

    /// Coalesce like `Linear` or `Quadratic` terms at a single depth `d` and
    /// drop any zero-summed cancellations before emitting a `Sum` node.
    fn coalesce_same_depth(&self, mut terms: Vec<ExprNode<'a, F>>) -> Vec<ExprNode<'a, F>> {
        fn key<F: CompileField>(term: &ExprNode<'_, F>) -> (u8, usize, usize) {
            match &term.v {
                Expr::Linear(_, w) => (0, w.id, 0),
                Expr::Quadratic(_, a, b) => (1, a.id.min(b.id), a.id.max(b.id)),
                _ => panic!("v2::copy: expected Linear or Quadratic, got {term:?}"),
            }
        }

        terms.sort_by_key(key);
        terms
            .chunk_by(|a, b| key(a) == key(b))
            .filter_map(|group| {
                let coefficient = group.iter().fold(self.f.zero(), |sum, term| {
                    let (Expr::Linear(k, _) | Expr::Quadratic(k, _, _)) = &term.v else {
                        unreachable!("term key checked the variants");
                    };
                    self.f.addf(&sum, k)
                });
                if self.f.is_zero(&coefficient) {
                    return None;
                }
                Some(match &group[0].v {
                    Expr::Linear(_, w) => self.next.linear(&coefficient, w),
                    Expr::Quadratic(_, a, b) => self.ground_quadratic(&coefficient, a, b),
                    _ => unreachable!("term key checked the variants"),
                })
            })
            .collect()
    }

    fn sum_wire_terms(&self, elements: &[ExprNode<'a, F>], const_sum: &F::E) -> ExprNode<'a, F> {
        if elements.is_empty() {
            return self.next.constant(const_sum);
        }
        let d = elements.iter().map(depth_term).max().unwrap();
        let (mut aligned, no): (Vec<ExprNode<'a, F>>, Vec<ExprNode<'a, F>>) =
            elements.iter().copied().partition(|n| depth_term(n) == d);

        if !no.is_empty() {
            let zero = self.f.zero();
            let folded_no = self.sum_wire_terms(&no, &zero);
            if let Expr::Constant(c) = &folded_no.v {
                debug_assert!(self.f.is_zero(c));
            } else {
                let term_no = match &folded_no.v {
                    Expr::Linear(_, _) | Expr::Quadratic(_, _, _) => folded_no,
                    _ => self.next.linear(&self.f.one(), &folded_no),
                };
                let lifted_no = self.lift(d, &term_no);
                aligned.push(lifted_no);
            }
        }

        let mut coalesced = self.coalesce_same_depth(aligned);
        if coalesced.is_empty() {
            return self.next.constant(const_sum);
        }
        if !self.f.is_zero(const_sum) {
            coalesced.push(self.next.constant(const_sum));
        }
        if coalesced.len() == 1 {
            coalesced[0]
        } else {
            self.next.sum(&coalesced, false)
        }
    }
}

impl<'a, F: CompileField, NEXT> RewriteT<'a, F> for CopyRewriter<'a, F, NEXT>
where NEXT: RewriteT<'a, F>
{
    fn ok(&self) -> RawAssertions<'a, F> {
        self.next.ok()
    }

    fn assert0(&self, x: &ExprNode<'a, F>) -> RawAssertions<'a, F> {
        match &x.v {
            Expr::Constant(e) if self.f.is_zero(e) => self.next.ok(),
            Expr::Constant(_) | Expr::One => panic!("cannot satisfy a nonzero constant assertion"),
            Expr::Linear(e, inner) => {
                assert!(!self.f.is_zero(e));
                self.assert0(inner)
            }
            _ => self.next.assert0(x),
        }
    }

    fn assertions(&self, assertions: &[RawAssertions<'a, F>]) -> RawAssertions<'a, F> {
        self.next.assertions(assertions)
    }

    fn input(&self, position_in_input_array: usize) -> ExprNode<'a, F> {
        self.next.input(position_in_input_array)
    }

    fn sum(&self, elements: &[ExprNode<'a, F>], _precious: bool) -> ExprNode<'a, F> {
        assert!(!elements.is_empty(), "v2::copy::sum: empty elements");
        let mut const_sum = self.f.zero();
        let mut wire_terms = Vec::with_capacity(elements.len());
        for x in elements {
            match &x.v {
                Expr::One => const_sum = self.f.addf(&const_sum, &self.f.one()),
                Expr::Constant(c) => const_sum = self.f.addf(&const_sum, c),
                Expr::Input(_) | Expr::Sum(_, _) => {
                    wire_terms.push(self.next.linear(&self.f.one(), x));
                }
                Expr::Linear(k, _) | Expr::Quadratic(k, _, _) => {
                    if !self.f.is_zero(k) {
                        wire_terms.push(*x);
                    }
                }
                Expr::WithAssertions(..) => panic!("UnexpectedWithAssertion"),
            }
        }
        self.sum_wire_terms(&wire_terms, &const_sum)
    }

    fn one(&self) -> ExprNode<'a, F> {
        self.next.constant(&self.f.one())
    }

    fn constant(&self, elt: &F::E) -> ExprNode<'a, F> {
        self.next.constant(elt)
    }

    fn linear(&self, elt: &F::E, x: &ExprNode<'a, F>) -> ExprNode<'a, F> {
        if self.f.is_zero(elt) {
            return self.next.constant(elt);
        }
        match &x.v {
            Expr::One => self.next.constant(elt),
            Expr::Constant(c) => self.next.constant(&self.f.mulf(elt, c)),
            Expr::Linear(e1, inner) => self.linear(&self.f.mulf(elt, e1), inner),
            Expr::Quadratic(e1, u, v) => self.ground_quadratic(&self.f.mulf(elt, e1), u, v),
            _ => self.next.linear(elt, x),
        }
    }

    fn quadratic(&self, elt: &F::E, x: &ExprNode<'a, F>, y: &ExprNode<'a, F>) -> ExprNode<'a, F> {
        if self.f.is_zero(elt) {
            return self.next.constant(elt);
        }
        match (&x.v, &y.v) {
            (Expr::One, _) => self.linear(elt, y),
            (_, Expr::One) => self.linear(elt, x),
            (Expr::Constant(cx), _) => self.linear(&self.f.mulf(elt, cx), y),
            (_, Expr::Constant(cy)) => self.linear(&self.f.mulf(elt, cy), x),
            _ => {
                let dx = x.depth;
                let dy = y.depth;
                if dx < dy {
                    self.quadratic(elt, &self.copy(x), y)
                } else if dx > dy {
                    self.quadratic(elt, x, &self.copy(y))
                } else {
                    self.ground_quadratic(elt, x, y)
                }
            }
        }
    }

    fn with_assertions(
        &self,
        _assertions: &Assertions<'a, F>,
        _x: &ExprNode<'a, F>,
    ) -> ExprNode<'a, F> {
        panic!("UnexpectedWithAssertion")
    }
}

/// Align wire depths using `Linear(1, x)` copy wires, rewriting from arena
/// `'a` to target arena `'b`.
pub(super) fn rewrite<'a, 'b, F: CompileField>(
    arena: &'b CompilerArena<'b, F>,
    f: &'b F,
    x: Assertions<'a, F>,
    tracker: &AssertionScope,
) -> Assertions<'b, F> {
    let cse = Cse::new(arena);
    let copy_rewriter = CopyRewriter::new(f, cse);
    let mut copied = Vec::new();
    walk_roots(arena, x, &copy_rewriter, |item| copied.push(item));
    let one = f.one();
    // A nonzero scale does not affect a product's zero check. Use the
    // interned unit product so deduplication keeps all assertion IDs.
    let canonical = copied.into_iter().map(|mut item| {
        if let Expr::Quadratic(k, left, right) = &item.expr.v {
            assert!(!f.is_zero(k));
            item.expr = copy_rewriter.ground_quadratic(&one, left, right);
        }
        item
    });
    dedup_assertions(arena, canonical, tracker)
}
