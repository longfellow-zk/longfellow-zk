// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{mldsa::runtime::reference::ConcreteInstance, runtime::random::PrivateRandom};
pub fn prove<P: MlDsaParams>(
    c: &Circuits,
    key: &[u8],
    instance: &ConcreteInstance<P>,
    context: &[u8],
    rng: &mut impl PrivateRandom,
) -> Result<Vec<u8>, String> {
    packed::prove(c, key, instance, context, rng)
}
