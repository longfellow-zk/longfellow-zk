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

//! Longfellow v2 algebraic compilation pipeline and scheduling entry point.

use crate::{
    compile::{
        algebra::field::CompileField,
        compiler::{
            arena::CompilerArena,
            logic_impl::{CompilerAssertions, CompilerLogic},
        },
        logic::AssertionScope,
    },
    core::proto::circuit::CircuitGeometry,
};

/// Compile directly into the concrete v2 streams, with no One input.
pub fn compile_v2<F, Build>(
    f: &F,
    build: Build,
) -> (
    crate::core::proto::v2::Circuit<F>,
    CircuitGeometry,
    crate::compile::compiler::debug::CircuitDebugSymbols,
)
where
    F: CompileField,
    Build: for<'src> FnOnce(CompilerLogic<'src, F>) -> (CompilerAssertions<'src, F>, usize, usize),
{
    compile_v2_with_classes(f, build, Default::default())
}

/// Compile with an explicit coefficient policy for format and timing comparisons.
pub fn compile_v2_with_classes<F, Build>(
    f: &F,
    build: Build,
    classes: crate::core::proto::fixed::CoefficientClasses,
) -> (
    crate::core::proto::v2::Circuit<F>,
    CircuitGeometry,
    crate::compile::compiler::debug::CircuitDebugSymbols,
)
where
    F: CompileField,
    Build: for<'src> FnOnce(CompilerLogic<'src, F>) -> (CompilerAssertions<'src, F>, usize, usize),
{
    let (nodes, assertions, npublic, boundary, tracker) = lower(f, build);
    let (circuit, info, symbols) = super::scheduler::schedule(
        f,
        nodes,
        &assertions,
        npublic,
        boundary,
        tracker,
        classes.for_field(f.is_binary()),
    );
    assert!(info.ninput > 0);
    assert!(info.nterms > 0);
    (circuit, info, symbols)
}

fn lower<F, Build>(
    f: &F,
    build: Build,
) -> (
    crate::compile::compiler::quad::QuadCircuit<F>,
    Vec<(usize, crate::compile::logic::scope::AssertionId)>,
    usize,
    usize,
    AssertionScope,
)
where
    F: CompileField,
    Build: for<'src> FnOnce(CompilerLogic<'src, F>) -> (CompilerAssertions<'src, F>, usize, usize),
{
    let source_tracker = AssertionScope::new();
    // Each rewrite owns its destination arena. End the source arena's scope
    // as soon as the next representation is complete; only owned quads survive.
    let (quad_circuit, quad_asserts, npublic_input, subfield_boundary) = {
        let copy_arena = CompilerArena::new();
        let (copied, npublic_input, subfield_boundary) = {
            let simplified_arena = CompilerArena::new();
            let (simplified, npublic_input, subfield_boundary) = {
                let source_arena = CompilerArena::new();
                let source_logic = CompilerLogic::new(&source_arena, f, &source_tracker);
                let (assertions, npublic_input, subfield_boundary) = build(source_logic);
                let simplified = crate::compile::compiler::assertion::rewrite(
                    &simplified_arena,
                    f,
                    assertions.items,
                    &source_tracker,
                );
                (simplified, npublic_input, subfield_boundary)
            };
            let copied = crate::compile::compiler::copy::rewrite(&copy_arena, f, simplified);
            (copied, npublic_input, subfield_boundary)
        };
        let (quad_circuit, quad_asserts) =
            super::ir_to_terms::rewrite(&copy_arena, f, copied, &source_tracker);
        (quad_circuit, quad_asserts, npublic_input, subfield_boundary)
    };

    (
        quad_circuit,
        quad_asserts,
        npublic_input,
        subfield_boundary,
        source_tracker,
    )
}
