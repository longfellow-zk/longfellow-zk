// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Trusted hidden-key circuit metadata shared by compiler and proof roles.
use std::sync::Arc;

use crate::{
    core::proto::v2::{Circuit, CircuitReader},
    mldsa::{
        proto::{BinaryKeccak, HiddenArchive, KeccakBackend, Source, CLAIMS, HIDDEN_QUOTIENT_BITS},
        runtime::KeccakSource,
    },
    runtime::{
        algebra::{fp24_ext6::RuntimeFp24Ext6, gf2_128::Gf2_128Field},
        v2::{proto::polygero::PolygeroConfig, simd_sumcheck::Program, sumcheck},
    },
};
pub struct Circuits {
    /// The binary relation, archived at its natural width.
    pub binary: Circuit<Gf2_128Field>,
    /// The native sextic-extension relation; it has no commitment of its own.
    pub arithmetic: Circuit<RuntimeFp24Ext6>,
    pub keccak: BinaryKeccak,
    pub config: PolygeroConfig,
    /// Every stored native coordinate, in claim order.
    pub(crate) sources: Vec<Source>,
    /// Binary input position of every source bit, in source order. Shared
    /// values lie inside the binary relation; native-only words and pads lie
    /// in the reserved suffix after it.
    pub(crate) positions: Vec<usize>,
    pub(crate) simd: Option<Arc<KeccakSource>>,
    pub(crate) links: Vec<(Vec<usize>, Vec<usize>)>,
    pub(crate) base_private: usize,
    pub(crate) key_start: usize,
}
impl Circuits {
    /// Load trusted compiler bytes with independently implemented runtime fields.
    pub fn from_archive(archive: HiddenArchive, config: PolygeroConfig) -> Result<Self, String> {
        let f = Gf2_128Field::new();
        let native_field = RuntimeFp24Ext6::new();
        Self::from_archive_with_readers(
            archive,
            config,
            CircuitReader::new(&f),
            CircuitReader::new(&native_field),
        )
    }
    /// Offline preparation may provide readers with explicit trusted size limits.
    pub(crate) fn from_archive_with_readers(
        archive: HiddenArchive,
        config: PolygeroConfig,
        binary_reader: CircuitReader<'_, Gf2_128Field>,
        native_reader: CircuitReader<'_, RuntimeFp24Ext6>,
    ) -> Result<Self, String> {
        let backend = if archive.keccak.external_permutations {
            KeccakBackend::Permutations
        } else {
            KeccakBackend::Scalar
        };
        Self::from_archive_with_backend(archive, config, binary_reader, native_reader, backend)
    }
    pub(crate) fn from_archive_with_backend(
        archive: HiddenArchive,
        config: PolygeroConfig,
        binary_reader: CircuitReader<'_, Gf2_128Field>,
        native_reader: CircuitReader<'_, RuntimeFp24Ext6>,
        backend: KeccakBackend,
    ) -> Result<Self, String> {
        if archive.keccak.external_permutations != (backend != KeccakBackend::Scalar) {
            return Err("hidden Keccak backend mismatch".into());
        }
        let (binary, binary_tail) = binary_reader.from_bytes(&archive.binary)?;
        if !binary_tail.is_empty() {
            return Err("trailing hidden binary archive".into());
        }
        let (arithmetic, arithmetic_tail) = native_reader.from_bytes(&archive.arithmetic)?;
        if !arithmetic_tail.is_empty()
            || arithmetic.raw.npublic_input != 0
            || archive.sources.len() != arithmetic.raw.ninput
            || archive.positions.len() != archive.sources.iter().map(|s| s.width).sum::<usize>()
        {
            return Err("hidden arithmetic source archive".into());
        }
        let pads = sumcheck::circuit_geometry(&[&arithmetic])?.pad_count();
        let mut sources = archive.sources;
        let mut positions = archive.positions;
        let mut next = positions
            .iter()
            .copied()
            .max()
            .and_then(|i| i.checked_add(1))
            .ok_or("empty hidden source map")?
            .max(binary.raw.ninput);
        for value in arithmetic.raw.ninput..arithmetic.raw.ninput + pads {
            for coordinate in 0..CLAIMS {
                sources.push(Source {
                    value,
                    coordinate,
                    width: 23,
                });
                positions.extend(next..next + 23);
                next += 23;
            }
        }
        let simd = if archive.keccak.external_permutations {
            let committed = next
                .checked_add(CLAIMS * HIDDEN_QUOTIENT_BITS)
                .ok_or("hidden source overflow")?;
            Some(Arc::new(KeccakSource::new(
                backend,
                committed - binary.raw.npublic_input,
                archive
                    .links
                    .iter()
                    .map(|(initial, final_state)| {
                        let read = |v: &Vec<usize>| {
                            v.iter().map(|i| i - binary.raw.npublic_input).collect()
                        };
                        (read(initial), read(final_state))
                    })
                    .collect(),
            )?))
        } else {
            None
        };
        Ok(Self {
            binary,
            arithmetic,
            keccak: archive.keccak,
            config,
            sources,
            positions,
            simd,
            links: archive.links,
            base_private: archive.base_private,
            key_start: archive.key_start,
        })
    }

    /// Diagnostic layout/program bytes. This is not an archive loader.
    pub fn metadata_bytes(&self) -> Vec<u8> {
        let mut out = b"HIDMETA2".to_vec();
        out.extend(self.binary.id);
        out.extend(self.arithmetic.id);
        for n in [
            self.base_private,
            self.key_start,
            self.sources.len(),
            self.positions.len(),
            self.links.len(),
        ] {
            out.extend((n as u64).to_le_bytes());
        }
        fn delta(out: &mut Vec<u8>, previous: &mut i64, n: usize) {
            let d = n as i64 - *previous;
            *previous = n as i64;
            let mut encoded = ((d << 1) ^ (d >> 63)) as u64;
            while encoded >= 128 {
                out.push((encoded as u8 & 127) | 128);
                encoded >>= 7;
            }
            out.push(encoded as u8);
        }
        let mut previous = 0;
        for source in &self.sources {
            delta(&mut out, &mut previous, source.value);
            out.extend([source.coordinate as u8, source.width as u8]);
        }
        previous = 0;
        for &position in &self.positions {
            delta(&mut out, &mut previous, position);
        }
        if let Some(source) = &self.simd {
            out.extend(source.metadata_bytes());
        }
        out
    }
    pub fn simd_permutations(&self) -> usize {
        self.links.len()
    }
    pub fn simd_program(&self) -> Option<&Program> {
        self.simd.as_ref().map(|source| source.program())
    }
}
