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

pub fn mdoc_zk_circuits_signature<FC>(
    fc: &FC,
) -> (
    Circuit<FC>,
    crate::core::proto::circuit::CircuitGeometry,
    crate::compile::compiler::debug::CircuitDebugSymbols,
)
where FC: MdocSigCompileField {
    signature_with_mode(fc, false)
}

fn signature_with_mode<FC>(
    fc: &FC,
    degree_separated: bool,
) -> (
    Circuit<FC>,
    crate::core::proto::circuit::CircuitGeometry,
    crate::compile::compiler::debug::CircuitDebugSymbols,
)
where
    FC: MdocSigCompileField,
{
    crate::compile::compiler::v2::compile_with_mode(
        fc,
        |iologic| {
            let bv = crate::circuits::bitvec::BitvecLogic::new(&iologic);
            let bitvec_io = crate::circuits::bitvec::BitvecIO::new(&bv);
            let plucker =
                crate::circuits::bit_plucker::BitPlucker::<_, { K_SIG_MAC_BIT_PLUCKER }>::new(
                    &iologic,
                );

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
        },
        degree_separated,
    )
}

/// Compile and segment the NEXT circuit without selecting commitment parameters.
pub fn generate_sig_circuit(f: &P256Field) -> Result<Circuit<P256Field>, String> {
    let (circuit, _, _) = mdoc_zk_circuits_signature(f);
    Ok(crate::compile::compiler::segment_circuit(f, &circuit))
}

#[cfg(feature = "degree-separated")]
pub fn generate_sig_degree_circuit(f: &P256Field) -> Result<Circuit<P256Field>, String> {
    let (circuit, _, _) = signature_with_mode(f, true);
    Ok(crate::compile::compiler::segment_circuit(f, &circuit))
}
