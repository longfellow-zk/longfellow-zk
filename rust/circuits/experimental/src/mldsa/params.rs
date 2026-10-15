// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! ML-DSA-44 and ML-DSA-65 parameters from FIPS 204.

use super::algebra::Q;

pub const N: usize = 256;
pub const D: usize = 13;

pub trait MlDsaParams: Copy + Clone + Default + 'static {
    const K: usize;
    const L: usize;
    const TAU: usize;
    const OMEGA: usize;
    const C_TILDE_BYTES: usize;
    const GAMMA1: u32;
    const GAMMA2: u32;
    /// The ML-DSA rejection bound `tau * eta`; unrelated to the extension-field beta.
    const REJECTION_BOUND: u32;
    const Z_BITS: usize;
    const R1_BITS: usize;
    const W1_BYTES: usize;

    fn z_coefficient_bits() -> usize {
        (2 * Self::GAMMA1 - 1).ilog2() as usize + 1
    }

    fn r0_bits() -> usize {
        if Self::GAMMA2 == 95_232 {
            18
        } else {
            19
        }
    }

    fn use_hint_modulus() -> u32 {
        (Q - 1) / (2 * Self::GAMMA2)
    }

    fn public_key_bytes() -> usize {
        32 + 320 * Self::K
    }

    fn signature_bytes() -> usize {
        Self::C_TILDE_BYTES + Self::L * 32 * Self::z_coefficient_bits() + Self::OMEGA + Self::K
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MlDsa44;

impl MlDsaParams for MlDsa44 {
    const K: usize = 4;
    const L: usize = 4;
    const TAU: usize = 39;
    const OMEGA: usize = 80;
    const C_TILDE_BYTES: usize = 32;
    const GAMMA1: u32 = 131_072;
    const GAMMA2: u32 = 95_232;
    const REJECTION_BOUND: u32 = 78;
    const Z_BITS: usize = 19;
    const R1_BITS: usize = 6;
    const W1_BYTES: usize = 192;
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MlDsa65;

impl MlDsaParams for MlDsa65 {
    const K: usize = 6;
    const L: usize = 5;
    const TAU: usize = 49;
    const OMEGA: usize = 55;
    const C_TILDE_BYTES: usize = 48;
    const GAMMA1: u32 = 524_288;
    const GAMMA2: u32 = 261_888;
    const REJECTION_BOUND: u32 = 196;
    const Z_BITS: usize = 20;
    const R1_BITS: usize = 4;
    const W1_BYTES: usize = 128;
}
