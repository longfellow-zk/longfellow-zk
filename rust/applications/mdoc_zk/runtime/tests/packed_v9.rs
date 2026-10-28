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
        eprintln!("v9 variant {variant}, {n} attributes: public bits {}, private bits {}, recipe outputs {}",spec.manifest.public_bits,spec.manifest.private_bits,spec.manifest.witness_recipe.outputs.len());
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
        assert_eq!(&proof[96..100], b"LFV4");
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
        let mut old_cache = std::fs::read(&path).unwrap();
        old_cache[..8].copy_from_slice(b"MDOCBIT2");
        std::fs::write(&path, old_cache).unwrap();
        assert!(development_provider::read_packed_v9(&path).is_err());
        std::fs::remove_file(path).unwrap();
    }
}

#[test]
fn semantic_manifest_codec_and_witness_recipe() {
    use crate::{
        core::bits::recipe::{BitOp, BitRecipe},
        mdoc::proto::packed::HashInputManifest,
        runtime::algebra::gf2_128::Gf2_128 as E,
    };
    let manifest = HashInputManifest {
        public_bits: 1,
        private_bits: 768,
        compiler_variant: 0,
        witness_recipe: Default::default(),
    };
    let bytes = manifest.to_bytes();
    assert_eq!(&bytes[..8], b"LFHASH02");
    assert_eq!(HashInputManifest::from_bytes(&bytes).unwrap(), manifest);
    for n in 0..bytes.len() {
        assert!(HashInputManifest::from_bytes(&bytes[..n]).is_err());
    }
    let mut obsolete = bytes.clone();
    obsolete[..8].copy_from_slice(b"LFBITS01");
    assert!(HashInputManifest::from_bytes(&obsolete).is_err());
    let mut invalid = manifest.clone();
    invalid.compiler_variant = 3;
    assert!(invalid.validate().is_err());
    invalid = manifest;
    invalid.private_bits = usize::MAX;
    assert!(invalid.validate().is_err());
    assert!(HashInputManifest::from_bytes(&invalid.to_bytes()).is_err());
    let recipe = HashInputManifest {
        public_bits: 1,
        private_bits: 2,
        compiler_variant: 2,
        witness_recipe: BitRecipe {
            nodes: vec![BitOp::Input(0), BitOp::Input(1), BitOp::Xor(0, 1)],
            outputs: vec![2],
        },
    };
    let mut private = vec![E::from(1)];
    recipe.extend_witness(&[E::from(1)], &mut private).unwrap();
    assert_eq!(private, vec![E::from(1), E::from(0)]);
}
