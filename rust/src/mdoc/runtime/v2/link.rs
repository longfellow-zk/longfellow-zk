// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! mdoc's composition: the hash circuit hosts the signature circuit's
//! shared values.
//!
//! The signature circuit's first 768 private inputs (issuer digest, device x,
//! device y) are stored as bits of the hash witness. The rest of its inputs
//! and its pads are native P-256 cells. The split mask R and the two quotient
//! pads occupy a reserved suffix after the hash circuit's inputs, followed by
//! the adapter's virtual leaves.
use crate::{
    core::proto::v2::Circuit,
    mdoc::{
        proto::{
            adapter::{MASK_BITS, QUOTIENT_BITS},
            layout,
        },
        v2::ZkSpecStruct,
    },
    runtime::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field, range_interpolation::EvaluationDomain},
        v2::{
            foreign::{
                adapter::{p256::P256Mode, AdapterMode},
                compose,
            },
            zk::{
                split,
                storage::{Group, StorageMap},
            },
        },
    },
};

type Mode = P256Mode<QUOTIENT_BITS>;
const _: () = assert!(<Mode as AdapterMode<P256Field>>::MASK_BITS == MASK_BITS);
pub(super) type Composition<'a, DH, DS> = compose::Composition<'a, P256Field, DH, DS, Mode>;
/// mdoc's composition statement under the identity message `I`.
pub(super) type Statement<'s, DH, DS, I> =
    compose::ComposedStatement<'s, P256Field, DH, DS, Mode, I>;

/// The shared values as (signature value, hash input) pairs, from the shared
/// layout table that the compilers and witness encoders also check against.
fn shared_positions(
    npublic: usize,
    width: usize,
) -> Result<impl Iterator<Item = (usize, usize)>, String> {
    if npublic + layout::hash::DEVICE_Y.end > width {
        return Err("hash circuit too narrow for the shared values".into());
    }
    Ok(layout::SHARED
        .into_iter()
        .flat_map(move |(sig, hash)| sig.zip(hash.map(move |h| npublic + h))))
}

/// mdoc's composition of its two trusted circuits.
pub(super) fn composition<'a, DH, DS>(
    spec: &ZkSpecStruct,
    signature: &'a Circuit<P256Field>,
    hash: &'a Circuit<Gf2_128Field>,
    domains: (&'a DH, &'a DS),
) -> Result<Composition<'a, DH, DS>, String>
where
    DH: EvaluationDomain<Gf2_128Field>,
    DS: EvaluationDomain<P256Field>,
{
    let foreign: Vec<_> = shared_positions(hash.raw.npublic_input, hash.raw.ninput)?
        .map(|(value, start)| Ok((value, Group::new(start, 1)?)))
        .collect::<Result<_, String>>()?;
    let storage = StorageMap::new(split::value_count(signature)?, &foreign)?;
    Composition::new(hash, signature, storage, spec.polygero, domains)
}

#[cfg(test)]
mod tests;
