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

use crate::{
    circuits::{
        bitvec::{BitvecIO, BitvecLogic},
        experimental::mldsa::{
            compile::verifier::{MlDsaVerifier, PublicKeyW, SignatureW, VerificationWitness},
            params::MlDsaParams,
        },
    },
    compile::algebra::fp24_ext6::CompileFp24Ext6,
    core::proto::CircuitGeometry,
};

// Keep analysis, evaluation, and proof benchmarks on exactly the same circuit.
// The public input is the expanded key; mu and the signature are private inputs.
#[allow(dead_code)]
pub fn compile_verifier<P: MlDsaParams>(
    field: &CompileFp24Ext6,
) -> (
    crate::core::proto::v2::Circuit<CompileFp24Ext6>,
    CircuitGeometry,
    crate::compile::compiler::CircuitDebugSymbols,
) {
    crate::compile::compiler::compile_v2(field, build::<P>)
}

fn build<'a, P: MlDsaParams>(
    logic: crate::compile::compiler::CompilerLogic<'a, CompileFp24Ext6>,
) -> (
    crate::compile::compiler::CompilerAssertions<'a, CompileFp24Ext6>,
    usize,
    usize,
) {
    let bitvec = BitvecLogic::new(&logic);
    let mut position = crate::compile::logic::K_FIRST_WIRE_POSITION;
    let public_key = PublicKeyW::input::<P>(&logic, &bitvec, &mut position);
    let public_input_count = position;
    let signature = SignatureW::input::<P>(&logic, &bitvec, &mut position);
    let witness = VerificationWitness::input::<P>(&logic, &bitvec, &mut position);
    let byte_io = BitvecIO::new(&bitvec);
    let mu: Vec<_> = (0..64).map(|_| byte_io.next(&mut position)).collect();
    let verifier = MlDsaVerifier::<_, P>::new(&logic);
    (
        verifier.assert_valid_signature_on_mu(&public_key, &signature, &mu, &witness),
        public_input_count,
        position,
    )
}

#[allow(dead_code)] // Used by the benchmark, not the ordinary circuit tests.
pub fn compile_v2_verifier<P: MlDsaParams>(
    field: &CompileFp24Ext6,
) -> (
    crate::core::proto::v2::Circuit<CompileFp24Ext6>,
    CircuitGeometry,
    crate::compile::compiler::CircuitDebugSymbols,
) {
    crate::compile::compiler::compile_v2(field, build::<P>)
}

#[allow(dead_code)] // Shared with the circuit-layout benchmark.
pub fn compile_v2_verifier_with_classes<P: MlDsaParams>(
    field: &CompileFp24Ext6,
    classes: crate::core::proto::fixed::CoefficientClasses,
) -> (
    crate::core::proto::v2::Circuit<CompileFp24Ext6>,
    CircuitGeometry,
    crate::compile::compiler::CircuitDebugSymbols,
) {
    crate::compile::compiler::compile_v2_with_classes(field, build::<P>, classes)
}
