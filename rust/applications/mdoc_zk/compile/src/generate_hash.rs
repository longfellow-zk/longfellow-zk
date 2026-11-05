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
    compile::algebra::gf2_128::Gf2_128Field,
    core::proto::v2::Circuit,
    mdoc::{
        circuits::{
            config::{K_HASH_V256_BIT_PLUCKER, K_HASH_V8_BIT_PLUCKER, K_SHA_BIT_PLUCKER},
            hash::circuit::MdocHash,
            MdocHashCompileField,
        },
        compile::{allocate_hash::allocate_hash, allocator::WireAllocator},
    },
};

pub fn mdoc_zk_circuits_hash<FC>(
    fc: &FC,
    num_attrs: usize,
) -> (
    Circuit<FC>,
    crate::core::proto::CircuitGeometry,
    crate::compile::compiler::debug::CircuitDebugSymbols,
)
where
    FC: MdocHashCompileField,
{
    crate::compile::compiler::compile_v2(fc, |iologic| {
        let bv = crate::circuits::bitvec::BitvecLogic::new(&iologic);
        let bitvec_io = crate::circuits::bitvec::BitvecIO::new(&bv);
        let plucker_v8 =
            crate::circuits::bit_plucker::BitPlucker::<_, { K_HASH_V8_BIT_PLUCKER }>::new(&iologic);
        let plucker_v256 =
            crate::circuits::bit_plucker::BitPlucker::<_, { K_HASH_V256_BIT_PLUCKER }>::new(
                &iologic,
            );
        let plucker_sha =
            crate::circuits::bit_plucker::BitPlucker::<_, { K_SHA_BIT_PLUCKER }>::new(&iologic);

        let mut allocator = WireAllocator::new(
            &iologic,
            &bitvec_io,
            crate::compile::logic::K_FIRST_WIRE_POSITION,
        );

        let (given, derived, pub_inputs_count) = allocate_hash(
            &mut allocator,
            num_attrs,
            &plucker_v8,
            &plucker_v256,
            &plucker_sha,
        );

        let mdoc = MdocHash::new(&iologic, num_attrs);
        let assertion = mdoc.assert_valid_presentation_and_macs(&given, &derived);
        (assertion, pub_inputs_count)
    })
}

/// Compile and segment the NEXT circuit without selecting commitment parameters.
pub fn generate_hash_circuit(
    f: &Gf2_128Field,
    num_attrs: usize,
) -> Result<Circuit<Gf2_128Field>, String> {
    let (circuit, _, _) = mdoc_zk_circuits_hash(f, num_attrs);
    Ok(crate::compile::compiler::segment_circuit_v2(f, &circuit))
}
