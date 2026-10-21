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

pub mod allocate_hash;
pub mod allocate_sig;
pub mod allocator;
pub mod generate_hash;
pub mod generate_sig;

pub use allocate_hash::*;
pub use allocate_sig::*;
pub use allocator::*;
use compile_algebra::{gf2_128::Gf2_128Field, p256::P256Field};
pub use generate_hash::*;
pub use generate_sig::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LigeroProfile {
    pub rateinv: usize,
    pub nreq: usize,
}

pub fn compile_circuits(
    num_attrs: usize,
    pnym: bool,
    hash_profile: LigeroProfile,
    sig_profile: LigeroProfile,
) -> Result<
    (
        Vec<u8>,
        runtime_ligero::param::LigeroConfig,
        runtime_ligero::param::LigeroConfig,
    ),
    String,
> {
    let f128_compile = Gf2_128Field::new();
    let p256_compile = P256Field::new();
    let (seg_sig, config_sig) = generate_sig_circuit(&p256_compile, sig_profile)?;
    let (seg_hash, config_hash) =
        generate_hash_circuit(&f128_compile, num_attrs, pnym, hash_profile)?;

    let writer_sig =
        core_proto::writer::CircuitWriter::new(&p256_compile, core_proto::FieldID::P256);
    let sig_bytes = writer_sig.to_bytes_lfc2(&seg_sig);

    let writer_hash =
        core_proto::writer::CircuitWriter::new(&f128_compile, core_proto::FieldID::Gf2_128);
    let hash_bytes = writer_hash.to_bytes_lfc2(&seg_hash);

    let mut builder = core_proto::archive::CircuitArchiveBuilder::new();
    builder.set_circuit_version(mdoc_zk_circuits::CURRENT_VERSION as u32);
    builder.add_entry("sig", seg_sig.id, sig_bytes);
    builder.add_entry("hash", seg_hash.id, hash_bytes);

    let archive = builder.build();
    Ok((archive.to_bytes(), config_sig, config_hash))
}

pub use compile_circuits as generate_circuits;

/// Identity of one compiled circuit: `(num_attrs, pnym)`.
pub type CircuitKey = (usize, bool);

/// The circuits that make up `CURRENT_VERSION`. The runtime's `CURRENT_ZK_SPECS` must list
/// exactly these `(num_attributes, pnym)` pairs (checked by a unit test in `zk_spec.rs`).
pub const CURRENT_CIRCUIT_KEYS: [CircuitKey; 5] = [
    (1, false),
    (2, false),
    (4, false),
    (1, true),
    (4, true),
];

/// Result of [`compile_circuits`]: `(lfa2 archive bytes, sig Ligero config, hash Ligero config)`.
pub type CompiledCircuit = (
    Vec<u8>,
    runtime_ligero::param::LigeroConfig,
    runtime_ligero::param::LigeroConfig,
);

/// Compiles every circuit in [`CURRENT_CIRCUIT_KEYS`] in parallel.
///
/// Each result is returned together with its [`CircuitKey`] so callers match circuits by
/// identity rather than by position; the order of the returned vector is unspecified.
pub fn compile_all_circuits(
    hash_profile: LigeroProfile,
    sig_profile: LigeroProfile,
) -> Vec<(CircuitKey, Result<CompiledCircuit, String>)> {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::scope(|s| {
        for key @ (num_attrs, pnym) in CURRENT_CIRCUIT_KEYS {
            let tx_thread = tx.clone();
            s.spawn(move || {
                let res = compile_circuits(num_attrs, pnym, hash_profile, sig_profile);
                tx_thread.send((key, res)).unwrap();
            });
        }
    });
    drop(tx);
    rx.into_iter().collect()
}

pub use compile_all_circuits as generate_all_circuits;
