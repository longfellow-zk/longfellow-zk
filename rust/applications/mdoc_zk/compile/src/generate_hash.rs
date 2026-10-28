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

pub fn mdoc_zk_circuits_hash<FC>(
    fc: &FC,
    num_attrs: usize,
) -> (
    Circuit<FC>,
    crate::core::proto::circuit::CircuitGeometry,
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
    })
}

/// Compile and segment the NEXT circuit without selecting commitment parameters.
pub fn generate_hash_circuit(
    f: &Gf2_128Field,
    num_attrs: usize,
) -> Result<Circuit<Gf2_128Field>, String> {
    let (circuit, _, _) = mdoc_zk_circuits_hash(f, num_attrs);
    Ok(crate::compile::compiler::segment_circuit(f, &circuit))
}

#[cfg(feature = "experimental")]
pub fn generate_packed_hash_circuit(
    f: &Gf2_128Field,
    num_attrs: usize,
) -> Result<
    (
        Circuit<Gf2_128Field>,
        crate::mdoc::proto::packed::HashInputManifest,
    ),
    String,
> {
    generate_packed_hash_circuit_variant(f, num_attrs, 0)
}
#[cfg(feature = "experimental")]
pub fn generate_packed_hash_circuit_variant(
    f: &Gf2_128Field,
    num_attrs: usize,
    variant: u8,
) -> Result<
    (
        Circuit<Gf2_128Field>,
        crate::mdoc::proto::packed::HashInputManifest,
    ),
    String,
> {
    if variant > 2 {
        return Err("unsupported packed compiler variant".into());
    }
    let mut domain = None;
    let mut late_recipe = false;
    let (circuit, _, _) = crate::compile::compiler::v2::compile_with_mode(
        f,
        |base_logic| {
            let logic = if variant == 0 {
                base_logic
            } else {
                base_logic.with_boolean_arithmetic()
            };
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
            let ninput = allocator.pos;
            let late_ranges = allocator
                .field_input_ranges
                .iter()
                .filter(|r| r.end <= npublic)
                .cloned()
                .collect::<Vec<_>>();
            domain = Some(crate::mdoc::proto::packed::HashInputManifest {
                public_bits: npublic,
                private_bits: ninput - npublic,
                compiler_variant: variant,
                witness_recipe: Default::default(),
            });
            if variant == 2 {
                logic.begin_boolean_witness(ninput);
            }
            let assertion = MdocHash::new(&logic, num_attrs)
                .assert_valid_presentation_and_macs(&given, &derived);
            let recipe = logic.take_boolean_witness();
            late_recipe=recipe.nodes.iter().any(|op|matches!(op,crate::core::bits::recipe::BitOp::Input(i) if late_ranges.iter().any(|r|r.contains(i))));
            let manifest = domain.as_mut().unwrap();
            manifest.private_bits += recipe.outputs.len();
            manifest.witness_recipe = recipe;
            (assertion, npublic, 0)
        },
        cfg!(feature = "degree-separated"),
    );
    if late_recipe {
        return Err("private witness recipe depends on late public MAC inputs".into());
    }
    let mut manifest = domain.ok_or("missing packed domain")?;
    if cfg!(feature = "degree-separated") {
        manifest.public_bits -= 1;
        for op in &mut manifest.witness_recipe.nodes {
            if let crate::core::bits::recipe::BitOp::Input(i) = op {
                *op = if *i == 0 {
                    crate::core::bits::recipe::BitOp::Constant(true)
                } else {
                    crate::core::bits::recipe::BitOp::Input(*i - 1)
                };
            }
        }
    }
    manifest.validate()?;
    if circuit.raw.ninput != manifest.public_bits + manifest.private_bits {
        return Err("packed allocation mismatch".into());
    }
    Ok((
        crate::compile::compiler::segment_circuit(f, &circuit),
        manifest,
    ))
}
