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

//! Explicit packed v9 development compilation and a separately tagged cache.
use crate::{
    core::proto::{archive::CircuitArchiveBuilder, writer::CircuitWriter, FieldID},
    mdoc::{
        compile,
        proto::packed::HashInputManifest,
        runtime::v2::{
            packed_v9::{
                provider::{from_compressed, ProvidedCircuit},
                PackedV9Spec,
            },
            PolygeroParameters,
        },
    },
    runtime::{
        algebra::{
            fp2::Fp2Field,
            gf2_128::Gf2_128Field,
            p256::{P256Field, P256Subfield},
            range_interpolation::{
                BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            },
            subfield::BinarySubfield,
            Subfield, SupportsFFT,
        },
        proto::packed_zk::PackedLayout,
    },
};
pub fn compile_packed_v9(num_attributes: usize) -> Result<ProvidedCircuit, String> {
    compile_packed_v9_variant(num_attributes, 0)
}
pub fn compile_packed_v9_variant(
    num_attributes: usize,
    variant: u8,
) -> Result<ProvidedCircuit, String> {
    if !(1..=4).contains(&num_attributes) {
        return Err("v9 supports one to four attributes".into());
    }
    let cf = crate::compile::algebra::gf2_128::Gf2_128Field::new();
    let cp = crate::compile::algebra::p256::P256Field::new();
    let (hash, manifest) =
        compile::generate_packed_hash_circuit_variant(&cf, num_attributes, variant)?;
    let sig = compile::generate_sig_circuit(&cp)?;
    let mut builder = CircuitArchiveBuilder::new();
    builder.set_circuit_version(9);
    builder.add_entry(
        "sig",
        sig.id,
        CircuitWriter::new(&cp, FieldID::P256).to_bytes_lfc2(&sig),
    );
    builder.add_entry(
        "hash",
        hash.id,
        CircuitWriter::new(&cf, FieldID::Gf2_128).to_bytes_lfc2(&hash),
    );
    builder.add_entry("hash-input", manifest.digest(), manifest.to_bytes());
    let archive = builder.build();
    let bytes = archive.to_bytes();
    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let d = BinaryInterpolatorFactory::new(&f, &sf);
    let p = P256Field::new();
    let ext = Fp2Field::new(&p);
    let pd =
        QuadraticExtensionFftInterpolatorFactory::new(&p, &ext, ext.omega(), ext.omega_order());
    // Decode into runtime field types; compiler field types are deliberately separate.
    let h = crate::core::proto::reader::CircuitReader::new(&f, FieldID::Gf2_128)
        .with_total_term_limit(crate::mdoc::proto::packed::V9_MAX_TOTAL_TERMS)
        .from_bytes(&archive.entries[1].payload, true)?
        .0;
    let s = crate::core::proto::reader::CircuitReader::new(&p, FieldID::P256)
        .from_bytes(&archive.entries[0].payload, true)?
        .0;
    let (layout, _, products) = PackedLayout::new(&h, 6)?;
    let hc = crate::compile::polygero::tune_large_field_at_rate(
        7,
        layout.witness_count,
        &products,
        0,
        16,
        sf.serialized_size_bytes(),
        |c| c.can_interpolate(&d),
    )
    .ok_or("no packed Polygero profile")?;
    let sc = super::next_v2::select_parameters(&s, &pd, &p, &P256Subfield::new(&p))?;
    let par = |c: crate::runtime::polygero::PolygeroConfig| PolygeroParameters {
        k: c.k,
        s: c.s,
        n: c.n,
        t: c.t,
    };
    let spec = PackedV9Spec {
        combined_hash: archive.combined_id,
        num_attributes,
        version: 9,
        manifest,
        polygero_hash: par(hc),
        polygero_sig: par(sc),
    };
    let compressed = zstd::encode_all(
        bytes.as_slice(),
        crate::mdoc::circuits::config::K_ZSTD_LEVEL,
    )
    .map_err(|e| e.to_string())?;
    from_compressed(spec, compressed)
}
pub fn write_packed_v9(path: &std::path::Path, bundle: &ProvidedCircuit) -> Result<(), String> {
    let s = bundle.spec();
    let mut b = b"MDOCBIT2".to_vec();
    b.extend_from_slice(&s.combined_hash);
    for n in [
        s.num_attributes,
        s.version,
        s.polygero_hash.k,
        s.polygero_hash.n,
        s.polygero_hash.s,
        s.polygero_hash.t,
        s.polygero_sig.k,
        s.polygero_sig.n,
        s.polygero_sig.s,
        s.polygero_sig.t,
    ] {
        b.extend_from_slice(&(n as u64).to_le_bytes())
    }
    let manifest = s.manifest.to_bytes();
    b.extend_from_slice(&(manifest.len() as u64).to_le_bytes());
    b.extend(manifest);
    b.extend_from_slice(bundle.compressed());
    std::fs::write(path, b).map_err(|e| e.to_string())
}
pub fn read_packed_v9(path: &std::path::Path) -> Result<ProvidedCircuit, String> {
    let b = std::fs::read(path).map_err(|e| e.to_string())?;
    let start = 8 + 32 + 80 + 8;
    if b.len() < start {
        return Err("truncated packed v9 cache".into());
    }
    let length = usize::try_from(u64::from_le_bytes(b[120..128].try_into().unwrap()))
        .map_err(|_| "manifest length overflow")?;
    let end = start
        .checked_add(length)
        .ok_or("manifest length overflow")?;
    if b.len() <= end || &b[..8] != b"MDOCBIT2" {
        return Err("invalid packed v9 cache".into());
    }
    let mut ns = [0usize; 10];
    for (n, c) in ns.iter_mut().zip(b[40..120].as_chunks::<8>().0) {
        *n = usize::try_from(u64::from_le_bytes(*c))
            .map_err(|_| "cache count overflow")?
    }
    let manifest = HashInputManifest::from_bytes(&b[start..end])?;
    let par = |i: usize| PolygeroParameters {
        k: ns[i],
        n: ns[i + 1],
        s: ns[i + 2],
        t: ns[i + 3],
    };
    let spec = PackedV9Spec {
        combined_hash: b[8..40].try_into().unwrap(),
        num_attributes: ns[0],
        version: ns[1],
        manifest,
        polygero_hash: par(2),
        polygero_sig: par(6),
    };
    from_compressed(spec, b[end..].to_vec())
}
