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

use std::ops::Range;

use super::{scheduler, terms::Node};
#[cfg(all(test, target_pointer_width = "32"))]
use crate::compile::compiler::arena::one_compilation;
use crate::{
    compile::{
        algebra::CompileField,
        compiler::{arena::CompilerArena, CompilerAssertions, CompilerLogic},
        debug::CircuitDebugSymbols,
        logic::{AssertionId, AssertionScope},
    },
    core::proto::{v2::RawCircuit, CircuitGeometry},
};

/// Compile into identity-free v2 streams, with no One input. Call
/// `segment_circuit_v2` to finalize the representation and compute its ID.
/// The shared source API numbers inputs from one and includes its reserved
/// position in the public-input boundary; native circuit indices start at zero.
pub fn compile_v2<F, Build>(
    f: &F,
    build: Build,
) -> (RawCircuit<F>, CircuitGeometry, CircuitDebugSymbols)
where
    F: CompileField,
    Build: for<'src> FnOnce(CompilerLogic<'src, F>) -> (CompilerAssertions<'src, F>, usize),
{
    compile_v2_shared_inputs(f, |logic| {
        let (assertions, npublic) = build(logic);
        (assertions, npublic, Vec::new())
    })
}

/// Retain private inputs whose constraints are checked by another frontend.
///
/// Ranges use one-based source positions and may cover only private inputs.
/// The composed protocol must authenticate the other frontend against these
/// same inputs. Ordinary `compile_v2` continues to reject unused inputs.
pub fn compile_v2_shared_inputs<F, Build>(
    f: &F,
    build: Build,
) -> (RawCircuit<F>, CircuitGeometry, CircuitDebugSymbols)
where
    F: CompileField,
    Build: for<'src> FnOnce(
        CompilerLogic<'src, F>,
    ) -> (CompilerAssertions<'src, F>, usize, Vec<Range<usize>>),
{
    #[cfg(all(test, target_pointer_width = "32"))]
    let _one = one_compilation();
    let mut shared_ranges = Vec::new();
    let (mut nodes, assertions, npublic, declared_inputs, tracker) = lower(f, |logic| {
        let (assertions, npublic, ranges) = build(logic);
        shared_ranges = ranges;
        (assertions, npublic)
    });
    let mut external = vec![false; declared_inputs];
    let input_end = declared_inputs
        .checked_add(1)
        .expect("input position overflow");
    for range in shared_ranges {
        assert!(
            range.start >= npublic.max(1) && range.end <= input_end && range.start <= range.end,
            "invalid shared input range"
        );
        external[range.start - 1..range.end - 1].fill(true);
    }
    let mut present = vec![false; declared_inputs];
    for node in &nodes {
        if let Node::Input {
            position_in_input_array,
        } = node
        {
            present[*position_in_input_array] = true;
        }
    }
    for (position, is_present) in present.into_iter().enumerate() {
        if !is_present {
            assert!(
                external[position],
                "some inputs are unused, cannot schedule"
            );
            nodes.push(Node::Input {
                position_in_input_array: position,
            });
        }
    }
    let (circuit, info, symbols) =
        scheduler::schedule(f, nodes, &assertions, npublic, &external, tracker);
    assert_eq!(
        info.ninput, declared_inputs,
        "some inputs are unused, cannot schedule"
    );
    assert!(info.ninput > 0);
    assert!(info.nterms > 0);
    (circuit, info, symbols)
}

fn lower<F, Build>(
    f: &F,
    build: Build,
) -> (
    Vec<Node<F>>,
    Vec<(usize, AssertionId)>,
    usize,
    usize,
    AssertionScope,
)
where
    F: CompileField,
    Build: for<'src> FnOnce(CompilerLogic<'src, F>) -> (CompilerAssertions<'src, F>, usize),
{
    let source_tracker = AssertionScope::new();
    // Each rewrite owns its destination arena. End the source arena's scope
    // as soon as the next representation is complete; only owned quads survive.
    let (quad_circuit, quad_asserts, npublic_input, declared_inputs) = {
        let copy_arena = CompilerArena::new();
        let (copied, npublic_input, declared_inputs) = {
            let simplified_arena = CompilerArena::new();
            let (simplified, npublic_input, declared_inputs) = {
                let source_arena = CompilerArena::new();
                let source_logic = CompilerLogic::new(&source_arena, f, &source_tracker, false);
                let (assertions, npublic_input) = build(source_logic);
                let simplified = crate::compile::compiler::assertion::rewrite(
                    &simplified_arena,
                    f,
                    assertions.items,
                    &source_tracker,
                    true,
                );
                let declared_inputs = source_arena
                    .input_end()
                    .checked_sub(1)
                    .expect("circuit has no inputs");
                (simplified, npublic_input, declared_inputs)
            };
            let copied = super::copy::rewrite(&copy_arena, f, simplified, &source_tracker);
            (copied, npublic_input, declared_inputs)
        };
        let (quad_circuit, quad_asserts) = super::ir_to_terms::rewrite(f, copied);
        (quad_circuit, quad_asserts, npublic_input, declared_inputs)
    };

    (
        quad_circuit,
        quad_asserts,
        npublic_input,
        declared_inputs,
        source_tracker,
    )
}

#[cfg(test)]
mod tests;
