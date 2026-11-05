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
        ir::{Expr, ExprNode},
        node::Node,
    },
};

pub struct CompilerArena<'a, F: CompileField> {
    pub(in crate::compile::compiler) bump: bumpalo::Bump,
    next_node_id: std::cell::Cell<usize>,
    input_end: std::cell::Cell<usize>,
    _marker: std::marker::PhantomData<&'a F>,
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
            next_node_id: std::cell::Cell::new(0),
            input_end: std::cell::Cell::new(0),
            _marker: std::marker::PhantomData,
        }
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
        let id = self.next_node_id.get();
        self.next_node_id.set(id + 1);
        self.bump.alloc(Node::new(id, expr, depth))
    }

    pub fn alloc_slice<T: Clone>(&'a self, slice: &[T]) -> &'a [T] {
        self.bump.alloc_slice_clone(slice)
    }

    pub fn alloc_str(&'a self, s: &str) -> &'a str {
        self.bump.alloc_str(s)
    }

    pub fn alloc<T>(&'a self, val: T) -> &'a T {
        self.bump.alloc(val)
    }
}
