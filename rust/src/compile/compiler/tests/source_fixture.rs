// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    compile::{
        algebra::CompileField,
        compiler::{compile_v2, segment_circuit_v2, CompilerAssertions, CompilerLogic},
        proto::CircuitDebugSymbols,
    },
    core::proto::{v2::Circuit, CircuitGeometry},
};

pub(crate) fn compile<F, Build>(
    f: &F,
    build: Build,
) -> (Circuit<F>, CircuitGeometry, CircuitDebugSymbols)
where
    F: CompileField,
    Build: for<'src> FnOnce(CompilerLogic<'src, F>) -> (CompilerAssertions<'src, F>, usize, usize),
{
    let (raw, geometry, symbols) = compile_v2(f, |logic| {
        let (assertions, npublic, _) = build(logic);
        (assertions, npublic)
    });
    (segment_circuit_v2(f, raw), geometry, symbols)
}
