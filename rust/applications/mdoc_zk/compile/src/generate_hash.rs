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
    use crate::compile::logic::LogicIO;
    let mut domain = None;
    let (circuit, _, _) = crate::compile::compiler::compile_v2(f, |base_logic| {
        let logic = if variant == 0 {
            base_logic
        } else {
            base_logic.with_boolean_arithmetic()
        };
        let bv = crate::circuits::bitvec::BitvecLogic::new(&logic);
        let io = crate::circuits::bitvec::BitvecIO::new(&bv);
        let p8 =
            crate::circuits::bit_plucker::BitPlucker::<_, { K_HASH_V8_BIT_PLUCKER }>::new(&logic);
        let p256 =
            crate::circuits::bit_plucker::BitPlucker::<_, { K_HASH_V256_BIT_PLUCKER }>::new(&logic);
        let ps = crate::circuits::bit_plucker::BitPlucker::<_, { K_SHA_BIT_PLUCKER }>::new(&logic);
        let mut allocator =
            WireAllocator::new_packed(&logic, &io, crate::compile::logic::K_FIRST_WIRE_POSITION);
        let (given, derived, npublic, ninput) =
            allocate_hash(&mut allocator, num_attrs, &p8, &p256, &ps);
        let boolean = crate::circuits::boolean::Boolean::new(&logic);
        let values = [&given.issuer_sig_e, &given.device_pk.0, &given.device_pk.1];
        let starts = std::array::from_fn(|i| {
            logic.position_in_input_array(&boolean.as_eltw(values[i / 2].bit((i % 2) * 128)))
                - npublic
        });
        domain = Some(crate::mdoc::proto::packed::HashInputManifest {
            public_bits: npublic,
            private_bits: ninput - npublic,
            mac_starts: starts,
            compiler_variant: variant,
            witness_recipe: Default::default(),
        });
        if variant == 2 {
            logic.begin_boolean_witness(ninput);
        }
        let assertion =
            MdocHash::new(&logic, num_attrs).assert_valid_presentation(&given, &derived);
        let recipe = logic.take_boolean_witness();
        let manifest = domain.as_mut().unwrap();
        manifest.private_bits += recipe.outputs.len();
        manifest.witness_recipe = recipe;
        (assertion, npublic, 0)
    });
    let manifest = domain.ok_or("missing packed domain")?;
    manifest.validate()?;
    if circuit.raw.ninput != manifest.public_bits + manifest.private_bits {
        return Err("packed allocation mismatch".into());
    }
    if variant > 0 {
        use crate::core::algebra::AlgebraicField;
        for (layer_index, layer) in circuit.raw.layers.iter().enumerate() {
            let mut bad = None;
            layer.for_each_term(&circuit.raw.constants, |term| {
                if term.k != f.zero() && term.k != f.one() {
                    bad = Some(term.g);
                }
            });
            if let Some(gate) = bad {
                return Err(format!(
                    "non-Boolean coefficient at layer {layer_index}, gate {gate}"
                ));
            }
        }
    }
    Ok((
        crate::compile::compiler::segment_circuit(f, &circuit),
        manifest,
    ))
}
