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

//! Longfellow v1 algebraic compilation pipeline and scheduling entry point.

use crate::{
    compile::{
        algebra::field::CompileField,
        compiler::{
            arena::CompilerArena,
            logic_impl::{CompilerAssertions, CompilerLogic},
        },
        logic::AssertionScope,
    },
    core::proto::v1::{Circuit, CircuitGeometry},
};

/// Compile with the historical Morton order.
pub fn compile<F, Build>(
    f: &F,
    build: Build,
) -> (
    Circuit<F>,
    CircuitGeometry,
    crate::compile::compiler::debug::CircuitDebugSymbols,
)
where
    F: CompileField + crate::core::algebra::SerializableField,
    Build: for<'src> FnOnce(CompilerLogic<'src, F>) -> (CompilerAssertions<'src, F>, usize, usize),
{
    let source_arena = crate::compile::compiler::arena::CompilerArena::new();
    let source_tracker = AssertionScope::new();

    let source_logic = CompilerLogic::new(&source_arena, f, &source_tracker, true);
    let (assertions, npublic_input, subfield_boundary) = build(source_logic);
    let arena1 = CompilerArena::new();
    let simplified =
        crate::compile::compiler::assertion::rewrite(&arena1, f, assertions.items, &source_tracker);

    // Source arena can be dropped after rewriting source assertions into arena1.
    drop(source_arena);

    // Pass 2: copy rewrite into arena2 (inserts term copies and depth alignment)
    let arena2 = CompilerArena::new();
    let copy_propagated = crate::compile::compiler::copy::rewrite(&arena2, f, simplified);

    // The copy rewrite owns its arena; release the simplified expressions.
    drop(arena1);

    // Pass 3: ir_to_quad rewrite into owned QuadCircuit representation
    let (quad_circuit, quad_asserts) = crate::compile::compiler::v1::ir_to_quad::rewrite(
        &arena2,
        f,
        copy_propagated,
        &source_tracker,
    );

    // Quad nodes are owned; release the expression arena before scheduling.
    drop(arena2);

    let (circuit, info, symbols) = super::scheduler::schedule(
        f,
        quad_circuit,
        &quad_asserts,
        npublic_input,
        subfield_boundary,
        source_tracker,
    );

    assert!(info.ninput > 0);
    assert!(info.nterms > 0);
    (circuit, info, symbols)
}
