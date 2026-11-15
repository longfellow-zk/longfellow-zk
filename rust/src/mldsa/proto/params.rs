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

use crate::core::algebra::fp24::Q;

pub const N: usize = 256;
pub const D: usize = 13;
/// FIPS 204 Appendix C, Table 3: minimum allowed bounded XOF outputs.
pub const SAMPLE_IN_BALL_BYTES: usize = 221;
pub const REJ_NTT_BYTES: usize = 894;

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
    /// Width of the shifted norm witness in [0, 2*(GAMMA1-REJECTION_BOUND)-2].
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
    // The maximum shifted coefficient is 261986, strictly below 2^18.
    const Z_BITS: usize = 18;
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

pub const ZETAS: [u32; N] = [
    1, 4808194, 3765607, 3761513, 5178923, 5496691, 5234739, 5178987, 7778734, 3542485, 2682288,
    2129892, 3764867, 7375178, 557458, 7159240, 5010068, 4317364, 2663378, 6705802, 4855975,
    7946292, 676590, 7044481, 5152541, 1714295, 2453983, 1460718, 7737789, 4795319, 2815639,
    2283733, 3602218, 3182878, 2740543, 4793971, 5269599, 2101410, 3704823, 1159875, 394148,
    928749, 1095468, 4874037, 2071829, 4361428, 3241972, 2156050, 3415069, 1759347, 7562881,
    4805951, 3756790, 6444618, 6663429, 4430364, 5483103, 3192354, 556856, 3870317, 2917338,
    1853806, 3345963, 1858416, 3073009, 1277625, 5744944, 3852015, 4183372, 5157610, 5258977,
    8106357, 2508980, 2028118, 1937570, 4564692, 2811291, 5396636, 7270901, 4158088, 1528066,
    482649, 1148858, 5418153, 7814814, 169688, 2462444, 5046034, 4213992, 4892034, 1987814,
    5183169, 1736313, 235407, 5130263, 3258457, 5801164, 1787943, 5989328, 6125690, 3482206,
    4197502, 7080401, 6018354, 7062739, 2461387, 3035980, 621164, 3901472, 7153756, 2925816,
    3374250, 1356448, 5604662, 2683270, 5601629, 4912752, 2312838, 7727142, 7921254, 348812,
    8052569, 1011223, 6026202, 4561790, 6458164, 6143691, 1744507, 1753, 6444997, 5720892, 6924527,
    2660408, 6600190, 8321269, 2772600, 1182243, 87208, 636927, 4415111, 4423672, 6084020, 5095502,
    4663471, 8352605, 822541, 1009365, 5926272, 6400920, 1596822, 4423473, 4620952, 6695264,
    4969849, 2678278, 4611469, 4829411, 635956, 8129971, 5925040, 4234153, 6607829, 2192938,
    6653329, 2387513, 4768667, 8111961, 5199961, 3747250, 2296099, 1239911, 4541938, 3195676,
    2642980, 1254190, 8368000, 2998219, 141835, 8291116, 2513018, 7025525, 613238, 7070156,
    6161950, 7921677, 6458423, 4040196, 4908348, 2039144, 6500539, 7561656, 6201452, 6757063,
    2105286, 6006015, 6346610, 586241, 7200804, 527981, 5637006, 6903432, 1994046, 2491325,
    6987258, 507927, 7192532, 7655613, 6545891, 5346675, 8041997, 2647994, 3009748, 5767564,
    4148469, 749577, 4357667, 3980599, 2569011, 6764887, 1723229, 1665318, 2028038, 1163598,
    5011144, 3994671, 8368538, 7009900, 3020393, 3363542, 214880, 545376, 7609976, 3105558,
    7277073, 508145, 7826699, 860144, 3430436, 140244, 6866265, 6195333, 3123762, 2358373, 6187330,
    5365997, 6663603, 2926054, 7987710, 8077412, 3531229, 4405932, 4606686, 1900052, 7598542,
    1054478, 7648983,
];
