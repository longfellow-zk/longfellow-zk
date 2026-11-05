// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
pub(crate) fn compile<F, Build>(
    f: &F,
    build: Build,
) -> (
    crate::core::proto::v2::Circuit<F>,
    crate::core::proto::CircuitGeometry,
    crate::compile::compiler::debug::CircuitDebugSymbols,
)
where
    F: crate::compile::algebra::field::CompileField,
    Build: for<'src> FnOnce(
        crate::compile::compiler::CompilerLogic<'src, F>,
    ) -> (
        crate::compile::compiler::CompilerAssertions<'src, F>,
        usize,
        usize,
    ),
{
    crate::compile::compiler::compile_v2(f, |logic| {
        let (assertions, npublic, _) = build(logic);
        (assertions, npublic)
    })
}
