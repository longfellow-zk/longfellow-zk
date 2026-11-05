// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Owned compiler graph and source-expression memoization shared by both backends.
use super::ir::ExprNode;
use crate::compile::algebra::field::CompileField;
pub type Wire = usize;

#[derive(Clone)]
pub enum Node<T> {
    Input { position_in_input_array: usize },
    Sum(Vec<T>),
    Assert0(Wire),
}
#[derive(Clone)]
pub struct Graph<T> {
    pub nodes: Vec<Node<T>>,
}

pub(super) struct WireMemoizer<V = Wire> {
    cache: std::cell::RefCell<Vec<Option<V>>>,
}

impl<V: Copy> WireMemoizer<V> {
    pub(super) fn new() -> Self {
        WireMemoizer {
            cache: std::cell::RefCell::new(Vec::new()),
        }
    }

    pub(super) fn call<'a, F: CompileField, FUNC>(&self, node: ExprNode<'a, F>, f: FUNC) -> V
    where FUNC: FnOnce(&ExprNode<'a, F>) -> V {
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

pub(super) fn push_node<N>(nodes: &mut Vec<N>, n: N) -> Wire {
    let c = nodes.len();
    nodes.push(n);
    c
}
