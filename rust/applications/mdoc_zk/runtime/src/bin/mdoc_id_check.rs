// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Does a fresh compile of the mdoc circuits reproduce the *shipped* artifact?
//!
//! This has to be answered before any work on the steps 2-3 sidecar.  `cert::build_sidecar`
//! asserts `compute_id(f, raw) == circuit.id`, and the sidecar is built from a **source compile**
//! -- the shipped `.lfa2` carries no layout names or assertion scope paths, so it cannot be
//! decoded into one.  If the source compile has drifted from the deployed circuit, the sidecar
//! would describe a circuit that step 1 never ingested, and the two halves of the certificate
//! would be about different objects.
//!
//! `LFC3_PROTOCOL.md` already warns that the checked-in fixtures have drifted (`npublic_input` 0
//! versus 1; SHA-256 at 98,993 terms rather than 79,093), so this is not a hypothetical.
//!
//! ```text
//! cargo run --release -p mdoc-zk-runtime --bin mdoc_id_check -- [CIRCUIT_HASH] [NUM_ATTRS]
//! ```

use core_proto::Layer;
use mdoc_zk_runtime::proto::decompress_circuits;

/// v7, one disclosed attribute -- the artifact ingested in `Gen/MdocHash`.
const DEFAULT_MDOC_HASH: &str = "8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121";

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn main() {
    let mut args = std::env::args().skip(1);
    let hash = args.next().unwrap_or_else(|| DEFAULT_MDOC_HASH.to_string());
    let num_attrs: usize = args
        .next()
        .unwrap_or_else(|| "1".to_string())
        .parse()
        .expect("NUM_ATTRS");

    let compressed = mdoc_zk_artifacts::load_circuit_lfa2(&hash);
    let p256r = runtime_algebra::p256::P256Field::new();
    let gf2r = runtime_algebra::gf2_128::Gf2_128Field::new();
    let (shipped_sig, shipped_hash) =
        decompress_circuits(&compressed, &p256r, &gf2r).expect("decode shipped artifact");

    println!("artifact {hash}  (num_attrs = {num_attrs})");
    for (label, id, layers, terms, ninput) in [
        (
            "shipped sig ",
            hex(&shipped_sig.id),
            shipped_sig.raw.layers.len(),
            shipped_sig.raw.layers.iter().map(Layer::num_terms).sum::<usize>(),
            shipped_sig.raw.ninput,
        ),
        (
            "shipped hash",
            hex(&shipped_hash.id),
            shipped_hash.raw.layers.len(),
            shipped_hash.raw.layers.iter().map(Layer::num_terms).sum::<usize>(),
            shipped_hash.raw.ninput,
        ),
    ] {
        println!("  {label}: id={id}  layers={layers} terms={terms} ninput={ninput}");
    }

    // A fresh source compile of the hash circuit, the same call the deployed circuit came from.
    let gf2c = compile_algebra::gf2_128::Gf2_128Field::new();
    let (fresh, _geom, _symbols) = mdoc_zk_compile::generate_hash::mdoc_zk_circuits_hash(&gf2c, num_attrs);
    println!(
        "  fresh hash  : id={}  layers={} terms={} ninput={}",
        hex(&fresh.id),
        fresh.raw.layers.len(),
        fresh.raw.layers.iter().map(Layer::num_terms).sum::<usize>(),
        fresh.raw.ninput
    );

    if fresh.id == shipped_hash.id {
        println!("\nMATCH: a source compile reproduces the shipped hash circuit.");
        println!("       The steps 2-3 sidecar can be built against it.");
    } else {
        println!("\nMISMATCH: the source compile has drifted from the shipped circuit.");
        println!("       A sidecar built from source would describe a different circuit than");
        println!("       step 1 ingested. Reconcile before doing any layout work.");
        std::process::exit(1);
    }
}
