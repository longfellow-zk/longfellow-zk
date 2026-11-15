// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Offline drivers connecting independently implemented compiler and runtime fields.
use crate::{
    core::proto::v2::CircuitReader,
    mldsa::{
        compile,
        proto::{BinaryKeccak, KeccakBackend, MlDsaParams},
        runtime::hidden::Circuits,
    },
    runtime::{
        algebra::{fp24_ext6::RuntimeFp24Ext6, gf2_128::Gf2_128Field},
        v2::proto::polygero::PolygeroConfig,
    },
};
fn profile() -> PolygeroConfig {
    PolygeroConfig {
        k: 349,
        s: 12,
        n: 2443,
        t: 84,
    }
}
pub fn compile_hidden<P: MlDsaParams>(keccak: BinaryKeccak) -> Result<Circuits, String> {
    let backend = if keccak.external_permutations {
        KeccakBackend::Permutations
    } else {
        KeccakBackend::Scalar
    };
    compile_hidden_with_backend::<P>(keccak, backend)
}
pub fn compile_hidden_with_backend<P: MlDsaParams>(
    keccak: BinaryKeccak,
    backend: KeccakBackend,
) -> Result<Circuits, String> {
    if keccak.external_permutations != (backend != KeccakBackend::Scalar) {
        return Err("hidden Keccak backend mismatch".into());
    }
    let archive = compile::compile_hidden::<P>(keccak)?;
    let binary = Gf2_128Field::new();
    let native = RuntimeFp24Ext6::new();
    // ML-DSA-65 scalar SHAKE uses about 19.3M wires and 68.2M terms;
    // only this trusted compiler-to-runtime bridge opts into the larger caps.
    Circuits::from_archive_with_backend(
        archive,
        profile(),
        CircuitReader::new(&binary)
            .with_trusted_size_limits(1 << 25, 1 << 27)
            .with_trusted_metadata_limit(128 << 20),
        CircuitReader::new(&native)
            .with_trusted_size_limits(1 << 25, 1 << 27)
            .with_trusted_metadata_limit(128 << 20),
        backend,
    )
}
pub fn compile_hidden_scalar<P: MlDsaParams>() -> Result<Circuits, String> {
    compile_hidden::<P>(BinaryKeccak::default())
}
pub fn compile_hidden_simd<P: MlDsaParams>() -> Result<Circuits, String> {
    let k = BinaryKeccak {
        external_permutations: true,
        ..BinaryKeccak::default()
    };
    compile_hidden::<P>(k)
}

mod public;
pub use public::{
    prepare_public, prepare_public_with_backend, prepare_public_with_keccak, Archives,
};
