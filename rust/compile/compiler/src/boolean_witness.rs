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

//! Export source Boolean expressions as a neutral topological witness recipe.
use crate::{
    compile::{
        algebra::field::CompileField,
        compiler::ir::{Expr, ExprNode},
    },
    core::bits::recipe::{BitOp, BitRecipe},
};
#[derive(Default)]
pub(super) struct WitnessBuilder {
    pub recipe: BitRecipe,
    pub base: Option<usize>,
    seen: rustc_hash::FxHashMap<usize, usize>,
}
impl WitnessBuilder {
    pub fn export<F: CompileField>(&mut self, x: ExprNode<'_, F>, f: &F) -> usize {
        if let Some(&i) = self.seen.get(&x.id) {
            return i;
        }
        let op = match x.v {
            Expr::Input(i) => BitOp::Input(i),
            Expr::One => BitOp::Constant(true),
            Expr::Constant(k) => {
                assert!(
                    *k == f.zero() || *k == f.one(),
                    "non-Boolean witness constant"
                );
                BitOp::Constant(*k == f.one())
            }
            Expr::Linear(k, a) => {
                assert!(*k == f.one());
                let i = self.export(a, f);
                self.seen.insert(x.id, i);
                return i;
            }
            Expr::Quadratic(k, a, b) => {
                assert!(*k == f.one());
                BitOp::And(self.export(a, f), self.export(b, f))
            }
            Expr::Sum(terms, _) => {
                let mut result = None;
                for &term in terms {
                    let i = self.export(term, f);
                    result = Some(if let Some(previous) = result {
                        let next = self.recipe.nodes.len();
                        self.recipe.nodes.push(BitOp::Xor(previous, i));
                        next
                    } else {
                        i
                    });
                }
                if let Some(i) = result {
                    self.seen.insert(x.id, i);
                    return i;
                }
                BitOp::Constant(false)
            }
            Expr::WithAssertions(_, a) => {
                let i = self.export(a, f);
                self.seen.insert(x.id, i);
                return i;
            }
        };
        let i = self.recipe.nodes.len();
        self.recipe.nodes.push(op);
        self.seen.insert(x.id, i);
        i
    }
    pub fn alias<F: CompileField>(&mut self, wire: ExprNode<'_, F>, computed: usize) {
        self.seen.insert(wire.id, computed);
        self.recipe.outputs.push(computed);
    }
}
