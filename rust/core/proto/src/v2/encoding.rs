// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Identity and format selection for compiler-native v2 circuits.
use sha2::{Digest, Sha256};

use super::{RawCircuit, SerializableField};
use crate::core::proto::{circuit::DigestBytes, fixed::CoefficientClasses};

pub const MAGIC: &[u8; 4] = b"LFC3";
const ID_DOMAIN: &[u8] = b"LFC3-v2-streams-v1";

/// LFC3 identity, independent of dictionary compression.
pub fn compute_id<F: SerializableField>(
    f: &F,
    raw: &RawCircuit<F>,
    classes: CoefficientClasses,
) -> DigestBytes {
    let mut h = Sha256::new();
    h.update(ID_DOMAIN);
    let update = |h: &mut Sha256, n: usize| h.update((n as u64).to_le_bytes());
    update(&mut h, classes.bits());
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
        macro_rules! general {
            ($degree:expr, $stream:expr, $($coordinate:ident),+) => {{
                update(&mut h, $degree);
                update(&mut h, $stream.num_terms());
                $stream.for_each(|term| {
                    $(update(&mut h, term.$coordinate as usize);)+
                    h.update(f.to_bytes(&raw.constants[term.k as usize]));
                });
            }};
        }
        macro_rules! coordinates {
            ($stream:expr, $($coordinate:ident),+) => {{
                update(&mut h, $stream.num_terms());
                $stream.for_each(|term| { $(update(&mut h, term.$coordinate as usize);)+ });
            }};
        }
        general!(0, layer.quadratic, g, l, r);
        coordinates!(layer.quadratic_one, g, l, r);
        coordinates!(layer.quadratic_minus_one, g, l, r);
        coordinates!(layer.quadratic_assertions, g, l, r);
        general!(1, layer.linear, g, l);
        coordinates!(layer.linear_one, g, l);
        coordinates!(layer.linear_minus_one, g, l);
        coordinates!(layer.linear_assertions, g, l);
        general!(2, layer.constant, g);
        coordinates!(layer.constant_one, g);
        coordinates!(layer.constant_minus_one, g);
    }
    h.finalize().into()
}
