// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
pub fn verify<P: MlDsaParams>(
    c: &Circuits,
    key: &[u8],
    context: &[u8],
    bytes: &[u8],
) -> Result<(), String> {
    packed::verify::<P>(c, key, context, bytes)
}
