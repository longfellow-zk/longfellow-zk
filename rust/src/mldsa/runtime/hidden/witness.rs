// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    core::algebra::fp24::Q,
    mldsa::{
        proto::{BinaryKeccak, MlDsaParams, REJ_NTT_BYTES},
        runtime::reference::{decode_public_key, shake128_witness},
    },
};
fn push_bits(out: &mut Vec<bool>, x: u32, width: usize) {
    out.extend((0..width).map(|r| x >> r & 1 != 0));
}
pub(crate) fn key_witness<P: MlDsaParams>(
    encoded: &[u8],
    keccak: BinaryKeccak,
) -> Result<Vec<bool>, String> {
    let key = decode_public_key::<P>(encoded).ok_or("hidden key decoding")?;
    let mut out = Vec::new();
    for &x in key.a_hat.iter().flatten().flatten() {
        push_bits(&mut out, x, 23);
    }
    for &x in key.t1.iter().flatten() {
        push_bits(&mut out, x, 10);
    }
    for &byte in &encoded[..32] {
        out.extend((0..8).map(|r| byte >> r & 1 != 0));
    }
    for row in 0..P::K {
        for col in 0..P::L {
            let mut seed = encoded[..32].to_vec();
            seed.extend([col as u8, row as u8]);
            let (bytes, trace) = shake128_witness(&seed, REJ_NTT_BYTES);
            out.extend(trace.bits_with_keccak(keccak));
            let mut count = 0u32;
            for chunk in bytes.as_chunks::<3>().0 {
                let x = u32::from(chunk[0])
                    | (u32::from(chunk[1]) << 8)
                    | (u32::from(chunk[2] & 127) << 16);
                count += u32::from(x < Q);
                out.extend((0..9).map(|r| count >> r & 1 != 0));
            }
            if count < 256 {
                return Err("hidden key expansion exhausted".into());
            }
        }
    }
    Ok(out)
}
