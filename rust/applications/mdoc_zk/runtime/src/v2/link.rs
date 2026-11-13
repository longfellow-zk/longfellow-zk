// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! mdoc's use of the foreign storage layer.
//!
//! The signature circuit's first 768 private inputs (issuer digest, device x,
//! device y) are stored as bits of the hash witness. The rest of its inputs
//! and its pads are native P-256 cells. The mixed split's mask R and the two
//! quotient pads occupy a reserved suffix after the hash circuit's inputs,
//! followed by the adapter's virtual leaves.
use crate::{
    core::proto::v2::Circuit,
    mdoc::circuits::p256_adapter::{MASK_BITS, QUOTIENT_BITS, SHARED_BITS},
    runtime::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field},
        v2::foreign::{
            adapter::{self, p256::P256Plan, TreeShape},
            frontend,
            storage::{BitGroup, Group, ReservedSuffix, StorageMap},
        },
    },
};

pub(super) const Q: usize = QUOTIENT_BITS;
pub(super) type Plan = P256Plan<Q>;

/// Binary input positions of the shared values, in signature input order.
/// Between the issuer digest and the device coordinates are the padded MSO
/// preimage, its length, and the one-byte SHA block count. This is the
/// allocation order of `hash::allocate`, also used by the witness encoder.
fn shared_positions(npublic: usize, width: usize) -> Result<Vec<usize>, String> {
    use crate::mdoc::proto::hash::constants::{K_HASH_INDEX_BITS, K_MSO_PREIMAGE_LEN};
    let device = 256 + 8 * K_MSO_PREIMAGE_LEN + K_HASH_INDEX_BITS + 8;
    if npublic + device + 512 > width {
        return Err("hash circuit too narrow for the shared values".into());
    }
    Ok((0..256)
        .chain(device..device + 512)
        .map(|i| npublic + i)
        .collect())
}

/// The complete cross-field layout for one hash circuit shape.
pub(super) struct Link {
    shared: Vec<usize>,
    pub(super) mask: Group,
    pub(super) otp: [BitGroup<Q>; 2],
    #[cfg_attr(not(any(test, feature = "prover")), allow(dead_code))]
    pub(super) suffix: ReservedSuffix,
    pub(super) plan: Plan,
    pub(super) shape: TreeShape,
    pub(super) fragment: Circuit<Gf2_128Field>,
}
impl Link {
    pub(super) fn new(hash: &Circuit<Gf2_128Field>) -> Result<Self, String> {
        let npublic = hash.raw.npublic_input;
        let shared = shared_positions(npublic, hash.raw.ninput)?;
        let mut suffix = ReservedSuffix::new(hash.raw.ninput);
        let mask = suffix.group(MASK_BITS);
        let otp = [suffix.word::<Q>(), suffix.word::<Q>()];
        let mut widths = vec![1; SHARED_BITS];
        widths.push(MASK_BITS);
        let plan = Plan::new(widths)?;
        let shape = plan.shape();
        let fragment = adapter::fragment(npublic, suffix.end(), shape)?;
        Ok(Self {
            shared,
            mask,
            otp,
            suffix,
            plan,
            shape,
            fragment,
        })
    }
    /// Storage of the signature frontend's values `[private | pads]`.
    pub(super) fn storage(&self, signature: &Circuit<P256Field>) -> Result<StorageMap, String> {
        let foreign: Vec<_> = self
            .shared
            .iter()
            .enumerate()
            .map(|(i, &start)| (i, Group { start, width: 1 }))
            .collect();
        StorageMap::new(frontend::value_count(signature)?, &foreign)
    }
    pub(super) fn virtual_inputs(&self) -> usize {
        self.shape.virtual_inputs()
    }
}

#[cfg(test)]
#[path = "../../tests/v2_link.rs"]
mod tests;
