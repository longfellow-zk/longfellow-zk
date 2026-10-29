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
        runtime::v2::{
            provider::{from_compressed, ProvidedCircuit},
            PolygeroParameters, ZkSpecStruct,
        },
    },
    runtime::{
        algebra::{
            fp2::Fp2Field,
            gf2_128::Gf2_128Field,
            p256::P256Field,
            range_interpolation::{
                BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            },
            subfield_v1::BinarySubfield,
            SupportsFFT,
        },
        proto::zk_v2::packing_layout,
    },
};
pub fn compile_next(num_attributes: usize) -> Result<ProvidedCircuit, String> {
    compile_next_with_classes(num_attributes, Default::default())
}
pub fn compile_next_with_classes(
    num_attributes: usize,
    classes: crate::core::proto::fixed::CoefficientClasses,
) -> Result<ProvidedCircuit, String> {
    if !(1..=4).contains(&num_attributes) {
        return Err("v9 supports one to four attributes".into());
    }
    let cf = crate::compile::algebra::gf2_128::Gf2_128Field::new();
    let cp = crate::compile::algebra::p256::P256Field::new();
    let (hash, manifest) = compile::generate_hash_v2_with_classes(&cf, num_attributes, classes)?;
    let sig = compile::generate_sig_v2_with_classes(&cp, classes)?;
    let mut builder = CircuitArchiveBuilder::new();
    builder.set_circuit_version(9);
    builder.add_entry(
        "sig",
        sig.id,
        CircuitWriter::new(&cp, FieldID::P256).to_bytes_v2(&sig),
    );
    builder.add_entry(
        "hash",
        hash.id,
        CircuitWriter::new(&cf, FieldID::Gf2_128).to_bytes_v2(&hash),
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
        .from_bytes_v2(&archive.entries[1].payload, true)?
        .0;
    let s = crate::core::proto::reader::CircuitReader::new(&p, FieldID::P256)
        .from_bytes_v2(&archive.entries[0].payload, true)?
        .0;
    let (layout, _, products) = packing_layout(&h, &f)?;
    let hc = crate::compile::polygero::tune_large_field_at_rate(
        7,
        layout.witness_count,
        &products,
        16,
        |c| c.can_interpolate(&d),
    )
    .ok_or("no packed Polygero profile")?;
    let sc = select_parameters(&s, &pd, &p)?;
    let par = |c: crate::runtime::polygero::PolygeroConfig| PolygeroParameters {
        k: c.k,
        s: c.s,
        n: c.n,
        t: c.t,
    };
    let spec = ZkSpecStruct {
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
/// Translate the v2 pad layout into public witness coordinates for selection.
/// NEXT uses rate 1/7; the chosen dimensions become part of its saved spec.
pub(super) fn select_parameters<
    const W: usize,
    F: crate::runtime::algebra::RuntimeField<W>
        + crate::core::algebra::SerializableField
        + crate::runtime::algebra::PackingField,
    D: crate::runtime::algebra::RangeInterpolatorFactory<W, F>,
>(
    circuit: &crate::core::proto::v2::Circuit<F>,
    domain: &D,
    f: &F,
) -> Result<crate::runtime::proto::polygero::PolygeroConfig, String> {
    circuit.validate_v2()?;
    let (_, nw, products) = crate::runtime::proto::zk_v2::commitment_layout(circuit, f);
    crate::compile::polygero::tune_large_field_at_rate(
        7,
        nw,
        &products,
        f.serialized_size_bytes(),
        |config| config.can_interpolate(domain),
    )
    .ok_or_else(|| "no supported Polygero tuning profile".to_string())
}
