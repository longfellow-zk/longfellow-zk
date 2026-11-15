// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Foreign coordinate layout shared by the hidden-key proof roles.
use super::Circuits;
use crate::{
    mldsa::proto::HIDDEN_QUOTIENT_BITS,
    runtime::{
        algebra::{
            fp24_ext6::RuntimeFp24Ext6,
            gf2_128::Gf2_128Field,
            range_interpolation::{CrtInterpolatorFactory, EvaluationDomain},
        },
        v2::{
            foreign::{
                adapter::{exact::ExactMode, AdapterMode},
                reserved::ReservedSuffix,
            },
            zk::{
                coordinates::CoordinateMap,
                split::{pure::PureSplit, value_count},
                storage::Group,
            },
        },
    },
};

pub(super) const HQ: usize = HIDDEN_QUOTIENT_BITS;
type Mode = ExactMode<HQ>;

/// The cross-field layout for one compiled hidden-key relation.
pub(super) struct Link {
    pub(super) map: CoordinateMap,
    /// Bits of the native-only words and pads, at the start of the suffix.
    #[cfg_attr(not(feature = "prover"), allow(dead_code))]
    pub(super) native: Group,
    #[cfg_attr(not(feature = "prover"), allow(dead_code))]
    pub(super) suffix: ReservedSuffix,
    pub(super) mode: Mode,
}
impl Link {
    pub(super) fn new(c: &Circuits) -> Result<Self, String> {
        let width = c.binary.raw.ninput;
        let mut suffix = ReservedSuffix::new(width);
        // The compiler placed native-only words and pads right after the
        // binary relation; reserve them before the quotient pads.
        let native_bits = c.positions.iter().filter(|&&p| p >= width).count();
        let native = suffix.group(native_bits)?;
        let mut stored = Vec::with_capacity(c.sources.len());
        let mut at = 0;
        for s in &c.sources {
            let bits = c
                .positions
                .get(at..at + s.width)
                .ok_or("hidden source positions")?;
            if bits.windows(2).any(|w| w[1] != w[0] + 1)
                || (bits[0] >= width && bits[s.width - 1] >= native.end())
            {
                return Err("hidden source words must be contiguous binary inputs".into());
            }
            stored.push((s.value, s.coordinate, Group::new(bits[0], s.width)?));
            at += s.width;
        }
        let map = CoordinateMap::new(value_count(&c.arithmetic)?, CLAIMS, &stored)?;
        let mode = Mode::new(
            map.groups().map(|g| g.width()).collect(),
            c.binary.raw.npublic_input,
            &mut suffix,
        )?;
        Ok(Self {
            map,
            native,
            suffix,
            mode,
        })
    }
    /// The binary host: the relation and the adapter fragment.
    pub(super) fn host<D: EvaluationDomain<Gf2_128Field>>(
        &self,
        c: &Circuits,
        domain: &D,
    ) -> Result<super::super::binary::BinaryParticipant, String> {
        let host = super::super::binary::BinaryParticipant::new(
            &c.binary,
            self.mode.fragment(),
            self.mode.virtual_inputs(),
            c.config,
            domain,
        )?;
        if let Some(source) = &c.simd {
            host.with_simd(std::sync::Arc::clone(source), domain)
        } else {
            if c.keccak.external_permutations {
                return Err("missing SIMD source".into());
            }
            Ok(host)
        }
    }
    /// The native frontend, with pure-foreign coordinate storage.
    pub(super) fn native(
        &self,
        c: &Circuits,
        domain: &CrtInterpolatorFactory,
    ) -> Result<PureSplit<RuntimeFp24Ext6>, String> {
        PureSplit::new(&c.arithmetic, self.map.storage_map()?, c.config, domain)
    }
}
use crate::mldsa::proto::CLAIMS;

/// The basis `e_c` of F_q^6 over F_q, for the coordinate expansion.
pub(super) fn basis(
    af: &RuntimeFp24Ext6,
) -> Vec<crate::runtime::algebra::fp24_ext6::RuntimeElement> {
    use crate::runtime::algebra::packing::{prime24::Prime24Extension, PackingExtension};
    Prime24Extension.native_basis(af)
}
