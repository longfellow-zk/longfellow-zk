// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Identity and format selection for compiler-native v2 circuits.
use sha2::{Digest, Sha256};

use super::{RawCircuit, SerializableField};
use crate::core::proto::circuit::DigestBytes;

pub const MAGIC: &[u8; 4] = b"LFC3";
const ID_DOMAIN: &[u8] = b"LFC3-v2-three-streams-v1";

/// LFC3 identity, independent of dictionary compression.
pub fn compute_id<F: SerializableField>(f: &F, raw: &RawCircuit<F>) -> DigestBytes {
    super::validate_constants(f, &raw.constants)
        .expect("LFC3 requires canonical coefficient indices");
    let mut h = Sha256::new();
    h.update(ID_DOMAIN);
    let update = |h: &mut Sha256, n: usize| h.update((n as u64).to_le_bytes());
    update(&mut h, usize::from(f.is_binary()));
    update(&mut h, f.serialized_size_bytes());
    h.update(f.serialized_mone());
    for n in [
        raw.noutput,
        raw.logv,
        raw.ninput,
        raw.npublic_input,
        raw.subfield_boundary,
        raw.layers.len(),
    ] {
        update(&mut h, n);
    }
    for layer in &raw.layers {
        update(&mut h, layer.nw);
        update(&mut h, layer.logw);
        update(&mut h, 0);
        update(&mut h, layer.quadratic.num_terms());
        layer.quadratic.for_each(|term| {
            update(&mut h, term.g as usize);
            update(&mut h, term.l as usize);
            update(&mut h, term.r as usize);
            h.update(f.to_bytes(&raw.constants[term.k as usize]));
        });
        update(&mut h, 1);
        update(&mut h, layer.linear.num_terms());
        layer.linear.for_each(|term| {
            update(&mut h, term.g as usize);
            update(&mut h, term.l as usize);
            h.update(f.to_bytes(&raw.constants[term.k as usize]));
        });
        update(&mut h, 2);
        update(&mut h, layer.constant.num_terms());
        layer.constant.for_each(|term| {
            update(&mut h, term.g as usize);
            h.update(f.to_bytes(&raw.constants[term.k as usize]));
        });
    }
    h.finalize().into()
}
