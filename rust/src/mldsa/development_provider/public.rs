// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Trusted circuit preparation and serialized loading for tests and benchmarks.
use crate::{
    compile::algebra::gf2_128::Gf2_128Field as CB,
    core::proto::v2::{CircuitReader, CircuitWriter},
    mldsa::{
        compile::compile_public,
        proto::{BinaryKeccak, KeccakBackend, MlDsaParams},
        runtime::Circuits,
    },
    runtime::{algebra::gf2_128::Gf2_128Field as B, v2::proto::polygero::PolygeroConfig},
};
pub struct Archives {
    pub binary: Vec<u8>,
    pub config: PolygeroConfig,
    pub keccak: BinaryKeccak,
    pub backend: KeccakBackend,
    pub metadata: Vec<u8>,
}
impl Archives {
    pub fn load(&self) -> Circuits {
        let (binary, tail) = CircuitReader::new(&B::new())
            .from_bytes(&self.binary)
            .unwrap();
        assert!(tail.is_empty());
        Circuits {
            binary,
            keccak: self.keccak,
            config: self.config,
            source: None,
        }
        .with_backend(
            self.backend,
            decode_links(&self.metadata).expect("trusted public Keccak metadata"),
        )
        .expect("trusted public Keccak source")
    }
}
pub fn prepare_public<T: MlDsaParams>() -> Archives {
    prepare_public_with_keccak::<T>(BinaryKeccak::default())
}

/// Prepare a scalar public-key relation with an explicit SHAKE checkpoint layout.
/// The archive cache binds every layout option, and loading retains that layout.
pub fn prepare_public_with_keccak<T: MlDsaParams>(keccak: BinaryKeccak) -> Archives {
    prepare_public_with_backend::<T>(keccak, KeccakBackend::Scalar)
}
/// Prepare either scalar or authenticated packed Keccak, with full setup retained
/// in the archive loader's timing. The backend and endpoint map are trusted setup.
pub fn prepare_public_with_backend<T: MlDsaParams>(
    keccak: BinaryKeccak,
    backend: KeccakBackend,
) -> Archives {
    keccak.validate();
    assert_eq!(
        keccak.external_permutations,
        backend != KeccakBackend::Scalar,
        "Keccak backend does not match the binary circuit"
    );
    use sha2::{Digest, Sha256};
    let mut digest = Sha256::new();
    digest.update(b"mldsa/public-source/keccak-layout/v2");
    digest.update(keccak.label().as_bytes());
    digest.update(backend.label().as_bytes());
    macro_rules! source {
        ($p:literal) => {
            include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/", $p)).as_slice()
        };
    }
    for bytes in [
        source!("src/mldsa/compile.rs"),
        source!("src/mldsa/compile/circuits/binary.rs"),
        source!("src/mldsa/compile/circuits/shared.rs"),
        source!("src/mldsa/compile/circuits/polynomial.rs"),
        source!("src/mldsa/compile/circuits/sample.rs"),
        source!("src/mldsa/compile/circuits/shake.rs"),
        source!("src/mldsa/proto/shake_layout.rs"),
        source!("src/mldsa/proto/params.rs"),
        source!("src/mldsa/proto/sample_routing.rs"),
        source!("src/mldsa/proto/adapter.rs"),
        source!("src/compile/compiler/v2/top.rs"),
        source!("src/compile/compiler/v2/scheduler.rs"),
        source!("src/compile/compiler/v2_segment.rs"),
        source!("src/core/proto/v2/writer/lfc3.rs"),
    ] {
        digest.update(bytes);
    }
    let directory = std::env::var_os("MLDSA_ARCHIVES")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| std::env::temp_dir().join("longfellow-mldsa"));
    std::fs::create_dir_all(&directory).unwrap();
    let name = format!("{}-{}-{:x}", T::K, T::L, digest.finalize());
    let bp = directory.join(format!("{name}-binary.lfc3"));
    let mp = directory.join(format!("{name}-links.bin"));
    let (binary, metadata) = if bp.exists() && mp.exists() {
        (std::fs::read(&bp).unwrap(), std::fs::read(&mp).unwrap())
    } else {
        let compiled = compile_public::<T>(keccak);
        let binary = CircuitWriter::new(&CB::new()).to_bytes(&compiled.circuit);
        let metadata = encode_links(&compiled.links);
        std::fs::write(bp, &binary).unwrap();
        std::fs::write(mp, &metadata).unwrap();
        (binary, metadata)
    };
    Archives {
        binary,
        keccak,
        backend,
        metadata,
        config: PolygeroConfig {
            k: 349,
            s: 12,
            n: 2443,
            t: 84,
        },
    }
}

fn encode_links(links: &[(Vec<usize>, Vec<usize>)]) -> Vec<u8> {
    let mut bytes = b"MLDPUB01".to_vec();
    bytes.extend(u32::try_from(links.len()).unwrap().to_le_bytes());
    for (a, b) in links {
        assert_eq!(a.len(), 1600);
        assert_eq!(b.len(), 1600);
        for &index in a.iter().chain(b) {
            bytes.extend(u32::try_from(index).unwrap().to_le_bytes());
        }
    }
    bytes
}
fn decode_links(bytes: &[u8]) -> Result<Vec<(Vec<usize>, Vec<usize>)>, String> {
    if bytes.get(..8) != Some(b"MLDPUB01") {
        return Err("public Keccak metadata version".into());
    }
    let count = usize::try_from(u32::from_le_bytes(
        bytes
            .get(8..12)
            .ok_or("public Keccak metadata header")?
            .try_into()
            .unwrap(),
    ))
    .unwrap();
    let size = count
        .checked_mul(3200)
        .and_then(|n| n.checked_mul(4))
        .and_then(|n| n.checked_add(12))
        .ok_or("public Keccak metadata size")?;
    if size != bytes.len() {
        return Err("public Keccak metadata size".into());
    }
    let mut links = Vec::with_capacity(count);
    for block in bytes[12..].as_chunks::<12800>().0 {
        let mut positions = block
            .as_chunks::<4>()
            .0
            .iter()
            .map(|b| u32::from_le_bytes(*b) as usize);
        links.push((positions.by_ref().take(1600).collect(), positions.collect()));
    }
    Ok(links)
}
