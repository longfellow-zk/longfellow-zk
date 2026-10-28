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

//! Compile NEXT and choose v2 parameters from its actual public circuit metadata.

use crate::{
    compile::polygero::tune_large_field_at_rate,
    core::{
        algebra::SerializableField,
        proto::{archive::CircuitArchive, circuit::Circuit, reader::CircuitReader, FieldID},
    },
    mdoc::{
        circuits::{config::K_ZSTD_LEVEL, NEXT_VERSION},
        compile,
        runtime::v2::{
            provider::{self, ProvidedCircuit},
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
            RangeInterpolatorFactory, RuntimeField, SupportsFFT,
        },
        proto::{polygero::PolygeroConfig, zk_v2::commitment_layout},
    },
};

/// Compile the development circuit and return its matching specification.
/// Parameter search runs here, once per invocation, outside proving and verification.
pub fn compile_next(num_attributes: usize) -> Result<ProvidedCircuit, String> {
    if !(1..=4).contains(&num_attributes) {
        return Err("NEXT supports one to four attributes".into());
    }
    let bytes = compile::compile_circuits(num_attributes)?;
    let archive = CircuitArchive::from_bytes(&bytes)?;
    let spec = specification(&archive, num_attributes)?;
    let compressed =
        zstd::encode_all(bytes.as_slice(), K_ZSTD_LEVEL).map_err(|error| error.to_string())?;
    provider::from_compressed(spec, compressed)
        .map_err(|error| format!("Invalid compiled NEXT bundle: {error:?}"))
}

/// The compiler supplies IDs and circuit structure; offline selection supplies
/// K, N, S and T. The runtime derives all remaining geometry from those choices.
fn specification(archive: &CircuitArchive, num_attributes: usize) -> Result<ZkSpecStruct, String> {
    if archive.circuit_version as usize != NEXT_VERSION {
        return Err("Compiler returned a circuit other than NEXT".into());
    }
    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let d = BinaryInterpolatorFactory::new(&f, &sf);
    let p = P256Field::new();
    let ext = Fp2Field::new(&p);
    let pd =
        QuadraticExtensionFftInterpolatorFactory::new(&p, &ext, ext.omega(), ext.omega_order());
    let hash = CircuitReader::new(&f, FieldID::Gf2_128)
        .from_bytes(
            &archive.get("hash").ok_or("Missing hash circuit")?.payload,
            false,
        )?
        .0;
    let sig = CircuitReader::new(&p, FieldID::P256)
        .from_bytes(
            &archive
                .get("sig")
                .ok_or("Missing signature circuit")?
                .payload,
            false,
        )?
        .0;
    let h = select_parameters(&hash, &d, &f)?;
    let s = select_parameters(&sig, &pd, &p)?;
    Ok(ZkSpecStruct {
        combined_hash: archive.combined_id,
        num_attributes,
        version: NEXT_VERSION,
        polygero_hash: PolygeroParameters {
            k: h.k,
            n: h.n,
            s: h.s,
            t: h.t,
        },
        polygero_sig: PolygeroParameters {
            k: s.k,
            n: s.n,
            s: s.s,
            t: s.t,
        },
    })
}

/// Translate the v2 pad layout into public witness coordinates for selection.
/// NEXT uses rate 1/7; the chosen dimensions become part of its saved spec.
pub(super) fn select_parameters<
    const W: usize,
    F: RuntimeField<W> + SerializableField + crate::runtime::algebra::PackingField,
    D: RangeInterpolatorFactory<W, F>,
>(
    circuit: &Circuit<F>,
    domain: &D,
    f: &F,
) -> Result<PolygeroConfig, String> {
    circuit.validate_v2()?;
    let (_, nw, products) = commitment_layout(circuit,f);
    tune_large_field_at_rate(7, nw, &products, f.serialized_size_bytes(), |config| config.can_interpolate(domain))
    .ok_or_else(|| "no supported Polygero tuning profile".to_string())
}
