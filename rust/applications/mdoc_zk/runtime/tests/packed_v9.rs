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
    compile::algebra::CompileNat,
    core::algebra::Nat,
    mdoc::{
        circuits::parse_test_data,
        development_provider,
        runtime::v2::{packed_v9, req_attr},
    },
};
#[test]
fn packed_v9_mdoc_two_and_four_attributes() {
    let (pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&crate::mdoc::testcases::vectors::TEST_DATA);
    let attrs = parsed
        .attrs
        .iter()
        .cycle()
        .take(4)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect::<Vec<_>>();
    let x = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&pk.0.to_bytes_le()).to_str_radix(16)
    );
    let y = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&pk.1.to_bytes_le()).to_str_radix(16)
    );
    let data = &crate::mdoc::testcases::vectors::TEST_DATA;
    for (n, variant) in [(2, 0), (4, 0), (2, 1), (4, 1), (2, 2), (4, 2)] {
        let bundle = development_provider::compile_packed_v9_variant(n, variant).unwrap();
        let spec = bundle.spec();
        assert_eq!(spec.version, 9);
        eprintln!("v9 variant {variant}, {n} attributes: public bits {}, private bits {}, packed words {}",spec.manifest.public_bits,spec.manifest.private_bits,spec.manifest.private_bits.div_ceil(128));
        let proof = packed_v9::run_mdoc_prover_inner(
            spec,
            bundle.compressed(),
            data.mdoc,
            &x,
            &y,
            data.transcript,
            &attrs[..n],
            now,
            "org.iso.18013.5.1.mDL",
            &mut crate::runtime::random::DeterministicRng::new(42),
        )
        .unwrap();
        assert_eq!(&proof[96..100], b"LFB2");
        packed_v9::run_mdoc_verifier_inner(
            spec,
            bundle.compressed(),
            &x,
            &y,
            data.transcript,
            &attrs[..n],
            now,
            "org.iso.18013.5.1.mDL",
            &proof,
        )
        .unwrap();
        if n == 2 && variant == 1 {
            for window in 1..=4 {
                let optimized = packed_v9::prover::run_mdoc_prover_inner_with_window(
                    spec,
                    bundle.compressed(),
                    data.mdoc,
                    &x,
                    &y,
                    data.transcript,
                    &attrs[..n],
                    now,
                    "org.iso.18013.5.1.mDL",
                    &mut crate::runtime::random::DeterministicRng::new(42),
                    Some(window),
                )
                .unwrap();
                assert_eq!(optimized, proof, "full v9 window={window}");
            }
        }
        let mut bad = proof.clone();
        bad[0] ^= 1;
        assert!(packed_v9::run_mdoc_verifier_inner(
            spec,
            bundle.compressed(),
            &x,
            &y,
            data.transcript,
            &attrs[..n],
            now,
            "org.iso.18013.5.1.mDL",
            &bad
        )
        .is_err());
        let path = std::env::temp_dir().join(format!(
            "longfellow-packed-{}-{n}.cache",
            std::process::id()
        ));
        development_provider::write_packed_v9(&path, &bundle).unwrap();
        let read = development_provider::read_packed_v9(&path).unwrap();
        assert_eq!(read.spec(), bundle.spec());
        assert!(development_provider::read_next(std::fs::File::open(&path).unwrap()).is_err());
        std::fs::remove_file(path).unwrap();
    }
}

#[test]
fn manifest_codec_and_polynomial_mac_basis() {
    use crate::{
        core::bits::PackedBits,
        mdoc::proto::packed::HashInputManifest,
        runtime::{
            algebra::{
                gf2_128::{Gf2_128 as E, Gf2_128Field as F},
                AlgebraicField,
            },
            dual_packing::field::pack,
        },
    };
    let manifest = HashInputManifest {
        public_bits: 1,
        private_bits: 768,
        mac_starts: [0, 128, 256, 384, 512, 640],
        compiler_variant: 0,
        witness_recipe: Default::default(),
    };
    let bytes = manifest.to_bytes();
    let mut obsolete = bytes.clone();
    obsolete[8] = 1;
    assert!(HashInputManifest::from_bytes(&obsolete).is_err());
    assert_eq!(HashInputManifest::from_bytes(&bytes).unwrap(), manifest);
    for n in 0..bytes.len() {
        assert!(HashInputManifest::from_bytes(&bytes[..n]).is_err())
    }
    let mut bad = manifest.clone();
    bad.mac_starts[1] = 1;
    assert!(bad.validate().is_err());
    bad = manifest.clone();
    bad.mac_starts[5] = usize::MAX;
    assert!(bad.validate().is_err());
    bad = manifest.clone();
    bad.compiler_variant = 3;
    assert!(bad.validate().is_err());
    // A recipe output used to hide total-input overflow by reducing the
    // semantic input count before it was checked.
    bad = manifest.clone();
    bad.compiler_variant = 2;
    bad.private_bits = usize::MAX;
    bad.witness_recipe.nodes = vec![crate::core::bits::recipe::BitOp::Constant(false)];
    bad.witness_recipe.outputs = vec![0];
    assert!(bad.validate().is_err());
    assert!(HashInputManifest::from_bytes(&bad.to_bytes()).is_err());
    let bits = (0..768)
        .map(|i| (i * 19 + 17) % 29 < 11)
        .collect::<PackedBits>();
    let pads: [E; 6] = std::array::from_fn(|i| E::from(23 + i as u128));
    let f = F::new();
    let av = 0x1234567890abcdefu128;
    let mut tags = [0; 6];
    for group in 0..3 {
        let message = std::array::from_fn(|byte| {
            (0..8).fold(0u8, |x, bit| {
                x | (u8::from(bits.get(256 * group + 8 * byte + bit)) << bit)
            })
        });
        let tag = crate::circuits::mac::concrete::compute_tag(
            &message,
            av,
            &[pads[2 * group].to_u128(), pads[2 * group + 1].to_u128()],
        );
        tags[group * 2..group * 2 + 2].copy_from_slice(&tag);
    }
    let claims = packed_v9::mac_claims(&manifest, av, &tags, &f).unwrap();
    for claim in claims {
        let mut lhs = f.zero();
        for (i, k) in claim.weights.iter().enumerate() {
            lhs.xor_in_place(&crate::runtime::dual_packing::field::select_bit(
                *k,
                bits.get(i),
            ));
        }
        assert_eq!(lhs, claim.rhs.evaluate(&pads, &f).unwrap());
    }
    assert_eq!(pack(&[false, true].into_iter().collect()), vec![E::from(2)]);
}
