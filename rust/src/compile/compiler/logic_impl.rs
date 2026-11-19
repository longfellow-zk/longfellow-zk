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
        arena::CompilerArena,
        assertion::strip_attached,
        cse::Cse,
        ir::{promote_sum_to_precious, AssertionItem, Expr, ExprNode, RewriteT},
    },
    logic::{AssertionScope, Logic, LogicIO, NIL_ASSERTION_ID},
};

#[derive(Debug, PartialEq, Eq)]
pub struct CompilerAssertions<'a, F: CompileField> {
    pub items: &'a [AssertionItem<'a, F>],
}

impl<'a, F: CompileField> Clone for CompilerAssertions<'a, F> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, F: CompileField> Copy for CompilerAssertions<'a, F> {}

pub struct CompilerLogic<
    'a,
    F: CompileField,
    NEXT: RewriteT<'a, F> = AlgebraicRewriter<'a, F, Cse<'a, F>>,
> {
    arena: &'a CompilerArena<'a, F>,
    f: &'a F,
    tracker: &'a AssertionScope,
    next: NEXT,
    // TODO: Remove the v1 compiler, then remove this flag and its Logic hook.
    retain_bit_assertions_v1: bool,
}

impl<'a, F: CompileField> CompilerLogic<'a, F> {
    pub fn new(
        arena: &'a CompilerArena<'a, F>,
        f: &'a F,
        tracker: &'a AssertionScope,
        retain_bit_assertions_v1: bool,
    ) -> Self {
        let cse = Cse::new(arena);
        let next = AlgebraicRewriter::with_bilinear_expansion(f, cse, !retain_bit_assertions_v1);
        Self {
            arena,
            f,
            tracker,
            next,
            retain_bit_assertions_v1,
        }
    }
}

impl<'a, F: CompileField, NEXT> Logic for CompilerLogic<'a, F, NEXT>
where NEXT: RewriteT<'a, F>
{
    type F = F;
    type Wire = ExprNode<'a, F>;
    type Assertions = CompilerAssertions<'a, F>;

    fn retain_bit_assertions_v1(&self) -> bool {
        self.retain_bit_assertions_v1
    }

    fn field(&self) -> &Self::F {
        self.f
    }

    fn zero(&self) -> Self::Wire {
        self.next.constant(&self.f.zero())
    }

    fn one(&self) -> Self::Wire {
        self.next.one()
    }

    fn konst(&self, x: &F::E) -> Self::Wire {
        self.next.constant(x)
    }

    fn precious(&self, x: &Self::Wire) -> Self::Wire {
        promote_sum_to_precious(x, &self.next)
    }

    fn sum(&self, xs: &[Self::Wire]) -> Self::Wire {
        self.next.sum(xs, false)
    }

    fn neg(&self, x: &Self::Wire) -> Self::Wire {
        self.next.linear(&self.f.mone(), x)
    }

    fn add(&self, x: &Self::Wire, y: &Self::Wire) -> Self::Wire {
        self.next.sum(&[*x, *y], false)
    }

    fn sub(&self, x: &Self::Wire, y: &Self::Wire) -> Self::Wire {
        self.next.sum(&[*x, self.neg(y)], false)
    }

    fn mul(&self, x: &Self::Wire, y: &Self::Wire) -> Self::Wire {
        self.next.quadratic(&self.f.one(), x, y)
    }

    fn mulk(&self, e: &F::E, y: &Self::Wire) -> Self::Wire {
        self.next.linear(e, y)
    }

    fn quadratic(&self, e: &F::E, x: &Self::Wire, y: &Self::Wire) -> Self::Wire {
        self.next.quadratic(e, x, y)
    }

    fn ok(&self) -> Self::Assertions {
        CompilerAssertions {
            items: self.arena.alloc_slice(&[]),
        }
    }

    fn assert0(&self, name: &str, x: &Self::Wire) -> Self::Assertions {
        assert!(!name.is_empty(), "assert0 requires a non-empty name");
        let id = self.tracker.new_leaf(name);
        let own_raw = self.next.assert0(x);

        let mut items = Vec::with_capacity(own_raw.len());
        for &expr in own_raw {
            items.push(AssertionItem { expr, id });
        }

        CompilerAssertions {
            items: self.arena.alloc_slice(&items),
        }
    }

    fn assert_all(&self, name: &str, assertions: &[Self::Assertions]) -> Self::Assertions {
        assert!(!name.is_empty(), "assert_all requires a non-empty name");
        let mut items = Vec::new();
        let mut seen = rustc_hash::FxHashSet::default();
        let mut seen_roots = rustc_hash::FxHashSet::default();
        for child_group in assertions {
            for item in child_group.items {
                if seen.insert((item.expr.id, item.id)) {
                    let root = self.tracker.find(item.id);
                    if seen_roots.insert(root) {
                        self.tracker.prepend_scope(item.id, name);
                    }
                    items.push(*item);
                }
            }
        }
        CompilerAssertions {
            items: self.arena.alloc_slice(&items),
        }
    }

    fn assert_when(&self, enable: &Self::Wire, assertions: Self::Assertions) -> Self::Assertions {
        match &enable.v {
            Expr::One => return assertions,
            Expr::Constant(value) if self.f.is_zero(value) => return self.ok(),
            Expr::Constant(_) => return assertions,
            _ => {}
        }
        // Strip attachments before multiplying the residues. Otherwise the
        // normal compiler pass would lift them back out as unconditional.
        let enable_root = self.arena.alloc_slice(&[AssertionItem {
            expr: enable,
            id: NIL_ASSERTION_ID,
        }]);
        let (enable_roots, mut attached) = strip_attached(self.arena, enable_root);
        let (roots, dependencies) = strip_attached(self.arena, assertions.items);
        let gated = |item: &AssertionItem<'a, F>| {
            let residual = self.mul(&enable_roots[0].expr, &item.expr);
            let id = item.id;
            self.next
                .assert0(&residual)
                .iter()
                .map(move |&expr| AssertionItem {
                    expr,
                    id: self.tracker.duplicate_leaf(id),
                })
        };

        attached.extend(dependencies.iter().flat_map(gated));
        let mut guarded_roots: Vec<_> = roots.iter().flat_map(gated).collect();
        if !attached.is_empty() {
            // Keep attachment paths outside the surrounding assertion group.
            if guarded_roots.is_empty() {
                guarded_roots.push(AssertionItem {
                    expr: self.zero(),
                    id: NIL_ASSERTION_ID,
                });
            }
            guarded_roots[0].expr = self
                .next
                .with_assertions(&self.arena.alloc_slice(&attached), &guarded_roots[0].expr);
        }
        CompilerAssertions {
            items: self.arena.alloc_slice(&guarded_roots),
        }
    }

    fn with_assertions(&self, assertions: Self::Assertions, x: &Self::Wire) -> Self::Wire {
        self.next.with_assertions(&assertions.items, x)
    }

    fn to_stringw_debug(&self, _x: &Self::Wire) -> String {
        "<ir>".to_string()
    }
}

impl<'a, F: CompileField, NEXT> LogicIO for CompilerLogic<'a, F, NEXT>
where NEXT: RewriteT<'a, F>
{
    fn input(&self, position_in_input_array: usize) -> Self::Wire {
        assert!(
            position_in_input_array > 0,
            "position_in_input_array = 0 is reserved for the constant One"
        );
        self.arena.record_input(position_in_input_array);
        self.next.input(position_in_input_array)
    }
}

impl<'a, F: CompileField, NEXT> std::fmt::Debug for CompilerLogic<'a, F, NEXT>
where NEXT: RewriteT<'a, F>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CompilerLogic").finish()
    }
}
