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
    core::proto::circuit::Circuit,
    mdoc::{
        circuits::{
            config::{K_HASH_V256_BIT_PLUCKER, K_HASH_V8_BIT_PLUCKER, K_SHA_BIT_PLUCKER},
            hash::circuit::MdocHash,
            MdocHashCompileField,
        },
        compile::{allocate_hash::allocate_hash, allocator::WireAllocator},
    },
};

pub fn mdoc_zk_circuits_hash<FC: MdocHashCompileField>(
    fc: &FC,
    num_attrs: usize,
) -> (
    Circuit<FC>,
    crate::core::proto::circuit::CircuitGeometry,
    crate::compile::compiler::debug::CircuitDebugSymbols,
) {
    crate::compile::compiler::compile_v1(fc, |logic| build_hash(logic, num_attrs))
}
fn build_hash<'src, FC: MdocHashCompileField>(
    iologic: crate::compile::compiler::CompilerLogic<'src, FC>,
    num_attrs: usize,
) -> (
    crate::compile::compiler::CompilerAssertions<'src, FC>,
    usize,
    usize,
) {
    let bv = crate::circuits::bitvec::BitvecLogic::new(&iologic);
    let bitvec_io = crate::circuits::bitvec::BitvecIO::new(&bv);
    let plucker_v8 =
        crate::circuits::bit_plucker::BitPlucker::<_, { K_HASH_V8_BIT_PLUCKER }>::new(&iologic);
    let plucker_v256 =
        crate::circuits::bit_plucker::BitPlucker::<_, { K_HASH_V256_BIT_PLUCKER }>::new(&iologic);
    let plucker_sha =
        crate::circuits::bit_plucker::BitPlucker::<_, { K_SHA_BIT_PLUCKER }>::new(&iologic);

    let mut allocator = WireAllocator::new(
        &iologic,
        &bitvec_io,
        crate::compile::logic::K_FIRST_WIRE_POSITION,
    );

    let (given, derived, pub_inputs_count, subfield_boundary_val) = allocate_hash(
        &mut allocator,
        num_attrs,
        &plucker_v8,
        &plucker_v256,
        &plucker_sha,
    );

    let mdoc = MdocHash::new(&iologic, num_attrs);
    let assertion = mdoc.assert_valid_presentation_and_macs(&given, &derived);
    (assertion, pub_inputs_count, subfield_boundary_val)
}
/// Compile and segment the NEXT circuit without selecting commitment parameters.
pub fn generate_hash_circuit(
    f: &Gf2_128Field,
    num_attrs: usize,
) -> Result<Circuit<Gf2_128Field>, String> {
    let (circuit, _, _) = mdoc_zk_circuits_hash(f, num_attrs);
    Ok(crate::compile::compiler::segment_circuit(f, &circuit))
}

/// Compile NEXT's Boolean-input hash circuit and its authenticated input manifest.
pub fn generate_hash_v2_circuit(
    f: &Gf2_128Field,
    num_attrs: usize,
) -> Result<
    (
        crate::core::proto::v2::Circuit<Gf2_128Field>,
        crate::mdoc::proto::packed::HashInputManifest,
    ),
    String,
> {
    generate_hash_v2_with_classes(f, num_attrs, Default::default())
}
pub fn generate_hash_v2_with_classes(
    f: &Gf2_128Field,
    num_attrs: usize,
    classes: crate::core::proto::fixed::CoefficientClasses,
) -> Result<
    (
        crate::core::proto::v2::Circuit<Gf2_128Field>,
        crate::mdoc::proto::packed::HashInputManifest,
    ),
    String,
> {
    let mut counts = (0, 0);
    let (circuit, _, _) = crate::compile::compiler::compile_v2_with_classes(
        f,
        |logic| {
            let bv = crate::circuits::bitvec::BitvecLogic::new(&logic);
            let io = crate::circuits::bitvec::BitvecIO::new(&bv);
            let p8 = crate::circuits::bit_plucker::BitPlucker::<_, { K_HASH_V8_BIT_PLUCKER }>::new(
                &logic,
            );
            let p256 =
                crate::circuits::bit_plucker::BitPlucker::<_, { K_HASH_V256_BIT_PLUCKER }>::new(
                    &logic,
                );
            let ps =
                crate::circuits::bit_plucker::BitPlucker::<_, { K_SHA_BIT_PLUCKER }>::new(&logic);
            let mut allocator = WireAllocator::new_boolean(
                &logic,
                &io,
                crate::compile::logic::K_FIRST_WIRE_POSITION,
            );
            let (given, derived, npublic, _) =
                allocate_hash(&mut allocator, num_attrs, &p8, &p256, &ps);
            counts = (npublic - 1, allocator.pos - npublic);
            (
                MdocHash::new(&logic, num_attrs)
                    .assert_valid_presentation_and_macs(&given, &derived),
                npublic,
                0,
            )
        },
        classes,
    );
    let manifest = crate::mdoc::proto::packed::HashInputManifest {
        public_bits: counts.0,
        private_bits: counts.1,
    };
    manifest.validate()?;
    if circuit.raw.ninput != manifest.public_bits + manifest.private_bits {
        return Err("NEXT allocation mismatch".into());
    }
    Ok((
        crate::compile::compiler::segment_circuit_v2(f, &circuit),
        manifest,
    ))
}
