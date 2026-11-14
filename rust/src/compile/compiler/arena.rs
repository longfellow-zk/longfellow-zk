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

use std::cell::{Cell, OnceCell};

use crate::compile::{
    algebra::CompileField,
    compiler::{
        ir::{AssertionItem, Assertions, Expr, ExprNode, RewriteT},
        node::Node,
    },
};

/// The compiler's storage. Nodes and slices live in a bump arena, which never
/// runs destructors, so it may hold only `Copy` values. Field constants can
/// own heap storage (a prime-field element owns a `BigUint`), so they live in
/// `constants`, which drops them with the arena.
pub struct CompilerArena<'a, F: CompileField> {
    bump: bumpalo::Bump,
    constants: DropArena<F::E>,
    next_node_id: Cell<usize>,
    input_end: Cell<usize>,
    _marker: std::marker::PhantomData<&'a F>,
}

/// An append-only arena that hands out shared references and drops its values
/// when it is dropped. Values sit in chunks of set-once slots, each chunk twice
/// the size of the previous one, so nothing moves once allocated and a value
/// is found after walking O(log n) chunk links.
pub(in crate::compile::compiler) struct DropArena<T> {
    first: Chunk<T>,
    /// Chunks beyond `first` and the slots used in the last chunk.
    extra_chunks: Cell<usize>,
    used: Cell<usize>,
}

struct Chunk<T> {
    slots: Box<[OnceCell<T>]>,
    next: OnceCell<Box<Chunk<T>>>,
}

impl<T> Chunk<T> {
    fn new(len: usize) -> Self {
        Self {
            slots: (0..len).map(|_| OnceCell::new()).collect(),
            next: OnceCell::new(),
        }
    }
}

impl<T> DropArena<T> {
    const FIRST_CHUNK: usize = 64;

    pub(in crate::compile::compiler) fn new() -> Self {
        Self {
            first: Chunk::new(Self::FIRST_CHUNK),
            extra_chunks: Cell::new(0),
            used: Cell::new(0),
        }
    }

    pub(in crate::compile::compiler) fn alloc(&self, value: T) -> &T {
        let mut chunk = &self.first;
        for _ in 0..self.extra_chunks.get() {
            chunk = chunk.next.get().expect("counted chunks exist");
        }
        let mut i = self.used.get();
        if i == chunk.slots.len() {
            let len = chunk.slots.len() * 2;
            chunk = chunk.next.get_or_init(|| Box::new(Chunk::new(len)));
            self.extra_chunks.set(self.extra_chunks.get() + 1);
            i = 0;
        }
        self.used.set(i + 1);
        let slot = &chunk.slots[i];
        if slot.set(value).is_err() {
            unreachable!("arena slots are filled once, in order");
        }
        slot.get().expect("the slot was just filled")
    }
}

impl<F: CompileField> Default for CompilerArena<'_, F> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, F: CompileField> CompilerArena<'a, F> {
    #[must_use]
    pub fn new() -> Self {
        Self {
            bump: bumpalo::Bump::new(),
            constants: DropArena::new(),
            next_node_id: Cell::new(0),
            input_end: Cell::new(0),
            _marker: std::marker::PhantomData,
        }
    }

    /// Store a field constant for the arena's lifetime; it is dropped with the
    /// arena, releasing any heap storage it owns.
    pub(in crate::compile::compiler) fn alloc_constant(&'a self, value: F::E) -> &'a F::E {
        self.constants.alloc(value)
    }

    pub(super) fn record_input(&self, position: usize) {
        self.input_end.set(
            self.input_end
                .get()
                .max(position.checked_add(1).expect("input index overflow")),
        );
    }
    pub(super) fn input_end(&self) -> usize {
        self.input_end.get()
    }

    pub fn alloc_node(&'a self, expr: Expr<'a, F>, depth: usize) -> ExprNode<'a, F> {
        // A node is two counts and an `Expr`; `Expr` being `Copy` means it owns
        // nothing, so leaving nodes undropped in the bump arena leaks nothing.
        const fn owns_nothing<T: Copy>() {}
        owns_nothing::<Expr<'a, F>>();
        let id = self.next_node_id.get();
        self.next_node_id.set(id + 1);
        self.bump.alloc(Node::new(id, expr, depth))
    }

    /// `Copy` guarantees the values own nothing the bump arena would leak.
    pub fn alloc_slice<T: Copy>(&'a self, slice: &[T]) -> &'a [T] {
        self.bump.alloc_slice_copy(slice)
    }

    pub fn alloc_str(&'a self, s: &str) -> &'a str {
        self.bump.alloc_str(s)
    }

    /// `Copy` guarantees the value owns nothing the bump arena would leak.
    pub fn alloc<T: Copy>(&'a self, val: T) -> &'a T {
        self.bump.alloc(val)
    }
}

/// Recursively walks the expression/assertion tree from input arena ('a) to target arena ('b).
pub(super) fn walk<'a, 'b, F: CompileField, NEXT: RewriteT<'b, F>>(
    arena: &'b CompilerArena<'b, F>,
    assertions: Assertions<'a, F>,
    rewriter: &NEXT,
) -> Assertions<'b, F> {
    fn children<F: CompileField>(node: ExprNode<'_, F>) -> Vec<ExprNode<'_, F>> {
        match &node.v {
            Expr::Input(_) | Expr::One | Expr::Constant(_) => Vec::new(),
            Expr::Sum(list, _) => list.to_vec(),
            Expr::Linear(_, x) => vec![*x],
            Expr::Quadratic(_, x, y) => vec![*x, *y],
            Expr::WithAssertions(a, x) => {
                let mut children = vec![*x];
                children.extend(a.iter().map(|item| item.expr));
                children
            }
        }
    }

    // Single-pass post-order DFS walk using a heap-allocated stack
    let mut visited = Vec::new();
    let mut cache: Vec<Option<ExprNode<'b, F>>> = Vec::new();
    let mut stack = Vec::new();

    // Push root assertion expressions
    for item in assertions.iter() {
        stack.push((item.expr, false));
    }

    while let Some((node, children_visited)) = stack.pop() {
        let id = node.id;
        if id < visited.len() && visited[id] {
            continue;
        }
        if children_visited {
            if id >= visited.len() {
                visited.resize(id + 1, false);
            }
            visited[id] = true;
            let rewritten = match &node.v {
                Expr::Input(a) => rewriter.input(*a),
                Expr::One => rewriter.one(),
                Expr::Constant(e) => rewriter.constant(e),
                Expr::Sum(list, precious) => {
                    let walked_list: Vec<ExprNode<'b, F>> =
                        list.iter().map(|child| cache[child.id].unwrap()).collect();
                    rewriter.sum(&walked_list, *precious)
                }
                Expr::Linear(e, x) => {
                    let walked_x = cache[x.id].unwrap();
                    rewriter.linear(e, &walked_x)
                }
                Expr::Quadratic(e, x, y) => {
                    let walked_x = cache[x.id].unwrap();
                    let walked_y = cache[y.id].unwrap();
                    rewriter.quadratic(e, &walked_x, &walked_y)
                }
                Expr::WithAssertions(a, x) => {
                    let mut seen = rustc_hash::FxHashSet::default();
                    let mut walked_assertions = Vec::new();
                    for item in a.iter() {
                        let walked_assertion = cache[item.expr.id].unwrap();
                        for &expr in rewriter.assert0(&walked_assertion) {
                            if seen.insert(expr.id) {
                                walked_assertions.push(AssertionItem { expr, id: item.id });
                            }
                        }
                    }
                    let walked_a = arena.alloc_slice(&walked_assertions);
                    let walked_x = cache[x.id].unwrap();
                    rewriter.with_assertions(&walked_a, &walked_x)
                }
            };
            if id >= cache.len() {
                cache.resize(id + 1, None);
            }
            cache[id] = Some(rewritten);
        } else {
            stack.push((node, true));
            for child in children(node) {
                stack.push((child, false));
            }
        }
    }

    // Normalize retained roots just like nested assertions: stripping attached
    // assertions can turn a root into zero or a scalar multiple of another root.
    let mut seen = rustc_hash::FxHashSet::default();
    let mut walked_list = Vec::new();
    for item in assertions.iter() {
        let walked = cache[item.expr.id].unwrap();
        for &expr in rewriter.assert0(&walked) {
            if seen.insert(expr.id) {
                walked_list.push(AssertionItem { expr, id: item.id });
            }
        }
    }

    arena.alloc_slice(&walked_list)
}

#[cfg(test)]
mod tests;
