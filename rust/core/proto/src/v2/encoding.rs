// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Identity and format selection for compiler-native v2 circuits.
use sha2::{Digest, Sha256};

use super::{RawCircuit, SerializableField, Stream};
use crate::core::proto::DigestBytes;

pub(crate) const MAGIC: &[u8; 4] = b"LFC3";
const ID_DOMAIN: &[u8] = b"LFC3-v2-segmented-id-v2";

fn size(write: &mut impl FnMut(&[u8]), n: usize) {
    write(
        &u64::try_from(n)
            .expect("circuit size exceeds u64")
            .to_le_bytes(),
    );
}

fn stream<T, W: FnMut(&[u8])>(write: &mut W, tag: u64, s: &Stream<T>, record: impl Fn(&mut W, &T)) {
    write(&tag.to_le_bytes());
    for n in [
        s.deltas.len(),
        s.segments.len(),
        s.segments.indices().len(),
        s.tokens.len(),
    ] {
        size(write, n);
    }
    for delta in &s.deltas {
        record(write, delta);
    }
    for segment in s.segments.iter() {
        size(write, segment.len());
    }
    for &index in s.segments.indices() {
        write(&u64::from(index).to_le_bytes());
    }
    for &token in &s.tokens {
        write(&u64::from(token).to_le_bytes());
    }
}

fn encode<F: SerializableField>(f: &F, raw: &RawCircuit<F>, mut write: impl FnMut(&[u8])) {
    write(ID_DOMAIN);
    size(&mut write, usize::from(f.is_binary()));
    size(&mut write, f.serialized_size_bytes());
    write(&f.serialized_mone());
    for n in [
        raw.noutput,
        raw.logv,
        raw.ninput,
        raw.npublic_input,
        raw.layers.len(),
        raw.constants.len(),
    ] {
        size(&mut write, n);
    }
    let mut coefficient = vec![0; f.serialized_size_bytes()];
    for k in &raw.constants {
        f.to_bytes_into(k, &mut coefficient);
        write(&coefficient);
    }
    for layer in &raw.layers {
        size(&mut write, layer.nw);
        size(&mut write, layer.logw);
        stream(&mut write, 0, &layer.quadratic, |write, t| {
            for n in [t.g, t.l, t.r] {
                write(&i64::from(n as i32).to_le_bytes());
            }
            write(&u64::from(t.k).to_le_bytes());
        });
        stream(&mut write, 1, &layer.linear, |write, t| {
            for n in [t.g, t.l] {
                write(&i64::from(n as i32).to_le_bytes());
            }
            write(&u64::from(t.k).to_le_bytes());
        });
        stream(&mut write, 2, &layer.constant, |write, t| {
            write(&i64::from(t.g as i32).to_le_bytes());
            write(&u64::from(t.k).to_le_bytes());
        });
    }
}

/// Identity of the complete stored segmented representation. No term expansion
/// is performed; dictionary and coefficient-table ordering affect the identity.
pub fn compute_id<F: SerializableField>(f: &F, raw: &RawCircuit<F>) -> DigestBytes {
    let mut h = Sha256::new();
    encode(f, raw, |bytes| h.update(bytes));
    h.finalize().into()
}

/// Capture the actual hasher input for Rust/Lean correspondence vectors.
#[cfg(test)]
fn id_bytes<F: SerializableField>(f: &F, raw: &RawCircuit<F>) -> Vec<u8> {
    let mut bytes = Vec::new();
    encode(f, raw, |part| bytes.extend_from_slice(part));
    bytes
}

#[cfg(test)]
#[path = "../../tests/v2_identity.rs"]
mod tests;
