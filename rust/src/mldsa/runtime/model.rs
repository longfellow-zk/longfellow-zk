// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Public-key relation layouts and application inputs, independent of proof roles.
use std::sync::Arc;

use super::KeccakSource;
use crate::{
    core::proto::v2::Circuit,
    mldsa::{
        proto::{
            public_widths, BinaryKeccak, KeccakBackend, MlDsaParams, CLAIMS, N,
            PUBLIC_QUOTIENT_BITS,
        },
        runtime::reference::{decode_public_key, PublicKey},
    },
    runtime::{
        algebra::{
            fp24_ext6::{RuntimeElement, RuntimeFp24Ext6},
            gf2_128::Gf2_128Field as BF,
        },
        v2::{
            foreign::{
                adapter::{
                    exact::{ExactClaims, ExactMode},
                    AdapterMode,
                },
                reserved::ReservedSuffix,
            },
            proto::polygero::PolygeroConfig,
            zk::storage::{Group, ModularClaim},
        },
    },
};

pub struct Circuits {
    pub binary: Circuit<BF>,
    pub keccak: BinaryKeccak,
    pub config: PolygeroConfig,
    pub source: Option<Arc<KeccakSource>>,
}
impl Circuits {
    /// Attach the trusted compiler's endpoint map and the chosen packed frontend.
    pub fn with_backend(
        mut self,
        backend: KeccakBackend,
        links: Vec<(Vec<usize>, Vec<usize>)>,
    ) -> Result<Self, String> {
        if self.keccak.external_permutations != (backend != KeccakBackend::Scalar) {
            return Err("Keccak backend does not match the binary circuit".into());
        }
        if backend == KeccakBackend::Scalar {
            if !links.is_empty() {
                return Err("scalar Keccak endpoint map".into());
            }
            self.source = None;
            return Ok(self);
        }
        if self.binary.raw.npublic_input != 0
            || links
                .iter()
                .flat_map(|(a, b)| a.iter().chain(b))
                .any(|&i| i >= self.binary.raw.ninput)
        {
            return Err("public Keccak endpoint map".into());
        }
        let private = self
            .binary
            .raw
            .ninput
            .checked_add(CLAIMS * PUBLIC_QUOTIENT_BITS)
            .ok_or("public Keccak source size")?;
        self.source = Some(Arc::new(KeccakSource::new(backend, private, links)?));
        Ok(self)
    }
}

pub(super) const QB: usize = PUBLIC_QUOTIENT_BITS;
type Mode = ExactMode<QB>;

/// Source bits of the claims, as absolute binary input positions. The binary
/// relation has no public inputs, so these are also witness offsets.
fn source_positions<P: MlDsaParams>() -> Vec<usize> {
    let z = P::L * N * P::Z_BITS;
    let kn = P::K * N;
    let raw = z + kn;
    let aux = raw + kn * P::R1_BITS;
    let positive = aux + kn * (P::r0_bits() + 1) + kn * P::R1_BITS;
    let mut out: Vec<_> = (0..z).chain(raw..raw + kn * P::R1_BITS).collect();
    for i in 0..kn {
        out.extend(aux + i * (P::r0_bits() + 1)..aux + i * (P::r0_bits() + 1) + P::r0_bits());
    }
    out.extend(positive..positive + 2 * N);
    out
}

/// The cross-field layout for one compiled binary relation: the claim's bit
/// groups, then the reserved suffix holding the adapter's quotient pads.
pub(super) struct Link {
    pub(super) groups: Vec<Group>,
    #[cfg_attr(not(feature = "prover"), allow(dead_code))]
    pub(super) suffix: ReservedSuffix,
    pub(super) mode: Mode,
}
impl Link {
    pub(super) fn new<P: MlDsaParams>(c: &Circuits) -> Result<Self, String> {
        if c.keccak.external_permutations != c.source.is_some() {
            return Err("missing or unexpected packed Keccak source".into());
        }
        if c.binary.raw.npublic_input != 0 {
            return Err("ML-DSA binary relation has public inputs".into());
        }
        let widths = public_widths::<P>();
        let positions = source_positions::<P>();
        let mut groups = Vec::with_capacity(widths.len());
        let mut at = 0;
        for &width in &widths {
            let bits = &positions[at..at + width];
            if bits.windows(2).any(|w| w[1] != w[0] + 1) || bits[width - 1] >= c.binary.raw.ninput {
                return Err("ML-DSA source words must be contiguous binary inputs".into());
            }
            groups.push(Group::new(bits[0], width)?);
            at += width;
        }
        let mut suffix = ReservedSuffix::new(c.binary.raw.ninput);
        let mode = Mode::new(widths, 0, &mut suffix)?;
        Ok(Self {
            groups,
            suffix,
            mode,
        })
    }
    /// The six projections as one claim over F_q^6 on the source words.
    pub(super) fn claim(
        &self,
        projections: ExactClaims,
        af: &RuntimeFp24Ext6,
    ) -> ModularClaim<RuntimeElement> {
        ModularClaim {
            terms: self
                .groups
                .iter()
                .zip(projections.weights)
                .map(|(g, w)| (*g, af.from_coefficients(w)))
                .collect(),
            target: af.from_coefficients(projections.targets),
        }
    }
}

pub(super) fn public_key<P: MlDsaParams>(encoded: &[u8]) -> Result<PublicKey, String> {
    decode_public_key::<P>(encoded).ok_or_else(|| "ML-DSA public key encoding".into())
}
