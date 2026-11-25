// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Compare the installed and proof-size tuned joint profiles on a NEXT bundle.
use std::{
    fs::{self, File},
    io::Write,
    path::Path,
};

use longfellow_zk::{
    core::algebra::SerializableField,
    mdoc::{
        development_provider::{read_next, write_next_with_profile},
        v2::{decompress_circuits, find_zk_spec, proof_geometry, MDOC_JOINT_PROFILE, SYSTEM_ID},
    },
    runtime::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field},
        v2::proto::{composed::ComposedGeometry, Digest, NONCE_LEN},
    },
};
use num_bigint::BigInt;

use crate::{exact::Q, profiles::next_size_profile, require, Result};

pub(crate) fn run(input: &Path, output: &Path) -> Result<()> {
    let bundle = read_next(File::open(input)?)?;
    let mut spec = *bundle.spec();
    require(
        spec.polygero == MDOC_JOINT_PROFILE,
        "bundle must use the installed profile",
    )?;
    require(
        find_zk_spec(SYSTEM_ID, &spec.combined_hash).is_none(),
        "cannot retune a published spec",
    )?;

    let binary = Gf2_128Field::new();
    let prime = P256Field::new();
    let (signature, hash) = decompress_circuits(bundle.compressed(), &prime, &binary)?;
    let widths = [
        binary.serialized_size_bytes(),
        prime.serialized_size_bytes(),
    ];
    let before = expected_payload_bytes(&proof_geometry(&spec, &signature, &hash)?.body, widths);
    spec.polygero = next_size_profile()?;
    let after = expected_payload_bytes(&proof_geometry(&spec, &signature, &hash)?.body, widths);
    require(
        after < before,
        "the candidate does not reduce expected proof size for this bundle",
    )?;

    let mut encoded = Vec::new();
    write_next_with_profile(&mut encoded, &bundle, spec.polygero)?;
    let mut file = File::create_new(output)?;
    if let Err(error) = file.write_all(&encoded) {
        drop(file);
        let _ = fs::remove_file(output);
        return Err(error.into());
    }
    let p = spec.polygero;
    let savings = before.sub(&after).mul(&Q::int(100)).floor();
    println!(
        "k={} s={} n={} t={} saves {}.{:02} expected proof bytes",
        p.k,
        p.s,
        p.n,
        p.t,
        &savings / 100u32,
        &savings % 100u32
    );
    Ok(())
}

/// Fields that vary with the profile. The same circuit has the same
/// sumcheck, packing, fingerprint, adapter and seal lengths.
fn expected_payload_bytes(g: &ComposedGeometry, widths: [usize; 2]) -> Q {
    let p = g.config();
    let fixed: usize = g
        .polygero()
        .iter()
        .zip(widths)
        .map(|(field, width)| {
            (field.response_lengths().iter().sum::<usize>() + p.t * field.nrow()) * width
        })
        .sum::<usize>()
        + p.t * NONCE_LEN;
    let digest_bytes = Digest::default().data.len();
    Q::int(fixed).add(&expected_frontier(p.n, p.t).mul(&Q::int(digest_bytes)))
}

/// The runtime tree stores leaves at n..2n without padding. An internal
/// node contributes one digest when exactly one child contains an opening.
fn expected_frontier(n: usize, t: usize) -> Q {
    let mut choices = vec![BigInt::from(0); n + 1];
    choices[t] = BigInt::from(1);
    for m in t + 1..=n {
        choices[m] = &choices[m - 1] * m / (m - t);
    }
    let mut sizes = vec![1; 2 * n];
    let mut total = BigInt::from(0);
    for node in (1..n).rev() {
        let (l, r) = (sizes[2 * node], sizes[2 * node + 1]);
        sizes[node] = l + r;
        total += &choices[n - l] + &choices[n - r] - 2 * &choices[n - l - r];
    }
    Q::new(total, choices.pop().unwrap())
}

#[cfg(test)]
mod tests;
