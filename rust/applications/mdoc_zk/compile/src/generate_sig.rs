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
    compile::algebra::p256::P256Field,
    core::proto::circuit::Circuit,
    mdoc::{
        circuits::{
            config::K_SIG_MAC_BIT_PLUCKER, signature::circuit::MdocSignature, MdocSigCompileField,
        },
        compile::{allocate_sig::allocate_sig, allocator::WireAllocator},
    },
};

pub fn mdoc_zk_circuits_signature<FC: MdocSigCompileField>(
    fc: &FC,
) -> (
    Circuit<FC>,
    crate::core::proto::circuit::CircuitGeometry,
    crate::compile::compiler::debug::CircuitDebugSymbols,
) {
    crate::compile::compiler::compile_v1(fc, |logic| build_signature(fc, logic))
}
fn build_signature<'src, FC: MdocSigCompileField>(
    fc: &FC,
    iologic: crate::compile::compiler::CompilerLogic<'src, FC>,
) -> (
    crate::compile::compiler::CompilerAssertions<'src, FC>,
    usize,
    usize,
) {
    let bv = crate::circuits::bitvec::BitvecLogic::new(&iologic);
    let bitvec_io = crate::circuits::bitvec::BitvecIO::new(&bv);
    let plucker =
        crate::circuits::bit_plucker::BitPlucker::<_, { K_SIG_MAC_BIT_PLUCKER }>::new(&iologic);

    let mut allocator = WireAllocator::new(
        &iologic,
        &bitvec_io,
        crate::compile::logic::K_FIRST_WIRE_POSITION,
    );

    let curve = crate::compile::algebra::secp256r1::Secp256r1::new(fc);
    let (given, derived, pub_inputs_count, subfield_boundary_val) =
        allocate_sig(&mut allocator, &plucker, &curve);

    let mdoc_sig = MdocSignature::new(&iologic, &curve);
    let assertion = mdoc_sig.assert_signatures_and_macs(&given, &derived);
    (assertion, pub_inputs_count, subfield_boundary_val)
}
/// Compile and segment the legacy quadratic circuit for evaluation tooling.
pub fn generate_sig_circuit(f: &P256Field) -> Result<Circuit<P256Field>, String> {
    let (circuit, _, _) = mdoc_zk_circuits_signature(f);
    Ok(crate::compile::compiler::segment_circuit(f, &circuit))
}
pub fn generate_sig_v2_circuit(
    f: &P256Field,
) -> Result<crate::core::proto::v2::Circuit<P256Field>, String> {
    generate_sig_v2_with_classes(f, Default::default())
}
pub fn generate_sig_v2_with_classes(
    f: &P256Field,
    classes: crate::core::proto::fixed::CoefficientClasses,
) -> Result<crate::core::proto::v2::Circuit<P256Field>, String> {
    let (circuit, _, _) = crate::compile::compiler::compile_v2_with_classes(
        f,
        |logic| build_signature(f, logic),
        classes,
    );
    Ok(crate::compile::compiler::segment_circuit_v2(f, &circuit))
}
