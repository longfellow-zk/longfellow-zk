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

//! Native ML-DSA arithmetic used to construct and check circuit witnesses.

use super::{
    sample::sample_in_ball,
    shake::{shake128, shake256_witness},
    Polynomial,
};
use crate::{
    core::algebra::fp24::Q,
    mldsa::proto::{MlDsaParams, D, N, REJ_NTT_BYTES, ZETAS},
    runtime::algebra::fp24_ext6::{add_base as add, mul_base as mul, sub_base as sub},
};

pub fn ntt(a: &mut Polynomial) {
    let mut k = 1;
    let mut len = 128;
    while len >= 1 {
        for start in (0..N).step_by(2 * len) {
            let zeta = ZETAS[k];
            k += 1;
            for j in start..start + len {
                let t = mul(zeta, a[j + len]);
                a[j + len] = sub(a[j], t);
                a[j] = add(a[j], t);
            }
        }
        len >>= 1;
    }
    debug_assert_eq!(k, N);
}

pub fn inverse_ntt(a: &mut Polynomial) {
    let mut k = N - 1;
    let mut len = 1;
    while len < N {
        for start in (0..N).step_by(2 * len) {
            let zeta = if ZETAS[k] == 0 { 0 } else { Q - ZETAS[k] };
            k -= 1;
            for j in start..start + len {
                let t = a[j];
                a[j] = add(t, a[j + len]);
                a[j + len] = mul(sub(t, a[j + len]), zeta);
            }
        }
        len <<= 1;
    }
    debug_assert_eq!(k, 0);
    for coefficient in a {
        *coefficient = mul(*coefficient, 8_347_681);
    }
}

pub fn pointwise_mul(a: &Polynomial, b: &Polynomial) -> Polynomial {
    std::array::from_fn(|i| mul(a[i], b[i]))
}

pub fn ring_mul(a: &Polynomial, b: &Polynomial) -> Polynomial {
    let mut a_ntt = *a;
    let mut b_ntt = *b;
    ntt(&mut a_ntt);
    ntt(&mut b_ntt);
    let mut result = pointwise_mul(&a_ntt, &b_ntt);
    inverse_ntt(&mut result);
    result
}

pub fn decompose<P: MlDsaParams>(r: i32) -> (i32, i32) {
    let r_plus = r.rem_euclid(Q as i32);
    let alpha = (2 * P::GAMMA2) as i32;
    let mut r0 = r_plus % alpha;
    if r0 > alpha / 2 {
        r0 -= alpha;
    }
    if r_plus - r0 == Q as i32 - 1 {
        (0, r0 - 1)
    } else {
        ((r_plus - r0) / alpha, r0)
    }
}

pub fn use_hint<P: MlDsaParams>(hint: bool, r: i32) -> u32 {
    let (r1, r0) = decompose::<P>(r);
    let modulus = P::use_hint_modulus() as i32;
    match (hint, r0 > 0) {
        (true, true) => ((r1 + 1) % modulus) as u32,
        (true, false) => (r1 - 1).rem_euclid(modulus) as u32,
        (false, _) => r1 as u32,
    }
}

pub fn simple_bit_unpack(bytes: &[u8], upper_bound: u32) -> Option<Polynomial> {
    let bits = (u32::BITS - upper_bound.leading_zeros()) as usize;
    if bytes.len() != 32 * bits {
        return None;
    }
    Some(std::array::from_fn(|i| {
        let bit_offset = i * bits;
        let byte_offset = bit_offset / 8;
        let shift = bit_offset % 8;
        let mut value = 0u32;
        for k in 0..2 {
            if let Some(&byte) = bytes.get(byte_offset + k) {
                value |= u32::from(byte) << (8 * k);
            }
        }
        (value >> shift) & ((1 << bits) - 1)
    }))
}

pub fn simple_bit_pack(coefficients: &Polynomial, upper_bound: u32) -> Option<Vec<u8>> {
    if coefficients
        .iter()
        .any(|&coefficient| coefficient > upper_bound)
    {
        return None;
    }
    let bits = (u32::BITS - upper_bound.leading_zeros()) as usize;
    let mut result = vec![0u8; 32 * bits];
    for (i, &coefficient) in coefficients.iter().enumerate() {
        let bit_offset = i * bits;
        for bit in 0..bits {
            result[(bit_offset + bit) / 8] |=
                (((coefficient >> bit) & 1) as u8) << ((bit_offset + bit) % 8);
        }
    }
    Some(result)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicKey {
    pub a_hat: Vec<Vec<Polynomial>>,
    pub t1: Vec<Polynomial>,
    pub tr: [u8; 64],
}

impl PublicKey {
    /// Expand the rounded key coefficients into the representation checked by
    /// the circuit: NTT(2^D * t1), independently of any signature or witness.
    pub fn ntt_t1(&self) -> Vec<Polynomial> {
        self.t1
            .iter()
            .map(|polynomial| {
                let mut result = polynomial.map(|coefficient| mul(coefficient, 1 << D));
                ntt(&mut result);
                result
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub c_tilde: Vec<u8>,
    pub z: Vec<Polynomial>,
    pub h: Vec<[bool; N]>,
}

pub fn rejection_sample_ntt_polynomial(seed: &[u8]) -> Option<Polynomial> {
    let output = shake128(seed, REJ_NTT_BYTES);
    let mut result = [0u32; N];
    let mut accepted = 0;
    for bytes in output.as_chunks::<3>().0 {
        let candidate =
            u32::from(bytes[0]) | (u32::from(bytes[1]) << 8) | (u32::from(bytes[2] & 0x7f) << 16);
        if candidate < Q {
            result[accepted] = candidate;
            accepted += 1;
            if accepted == N {
                return Some(result);
            }
        }
    }
    None
}

pub fn expand_a<P: MlDsaParams>(rho: &[u8]) -> Option<Vec<Vec<Polynomial>>> {
    if rho.len() != 32 {
        return None;
    }
    (0..P::K)
        .map(|row| {
            (0..P::L)
                .map(|column| {
                    let mut seed = rho.to_vec();
                    seed.extend([column as u8, row as u8]);
                    rejection_sample_ntt_polynomial(&seed)
                })
                .collect()
        })
        .collect()
}

fn bit_unpack(bytes: &[u8], upper: u32, center: u32, bits: usize) -> Option<Polynomial> {
    if bytes.len() != 32 * bits {
        return None;
    }
    let mut result = [0u32; N];
    for (i, coefficient) in result.iter_mut().enumerate() {
        let bit_offset = i * bits;
        let byte_offset = bit_offset / 8;
        let shift = bit_offset % 8;
        let mut value = 0u32;
        for k in 0..4 {
            if let Some(&byte) = bytes.get(byte_offset + k) {
                value |= u32::from(byte) << (8 * k);
            }
        }
        value = (value >> shift) & ((1 << bits) - 1);
        if value > upper + center {
            return None;
        }
        *coefficient = if center >= value {
            center - value
        } else {
            Q - (value - center)
        };
    }
    Some(result)
}

fn unpack_hint<P: MlDsaParams>(bytes: &[u8]) -> Option<Vec<[bool; N]>> {
    if bytes.len() != P::OMEGA + P::K {
        return None;
    }
    let mut result = vec![[false; N]; P::K];
    let mut index = 0;
    for (polynomial, hint) in result.iter_mut().enumerate() {
        let limit = usize::from(bytes[P::OMEGA + polynomial]);
        if limit < index || limit > P::OMEGA {
            return None;
        }
        let mut previous = None;
        while index < limit {
            let coefficient = usize::from(bytes[index]);
            if previous.is_some_and(|value| coefficient <= value) {
                return None;
            }
            hint[coefficient] = true;
            previous = Some(coefficient);
            index += 1;
        }
    }
    if bytes[index..P::OMEGA].iter().any(|&byte| byte != 0) {
        return None;
    }
    Some(result)
}

pub fn decode_signature<P: MlDsaParams>(bytes: &[u8]) -> Option<Signature> {
    if bytes.len() != P::signature_bytes() {
        return None;
    }
    let mut offset = 0;
    let c_tilde = bytes[..P::C_TILDE_BYTES].to_vec();
    offset += P::C_TILDE_BYTES;
    let packed_z_bytes = 32 * P::z_coefficient_bits();
    let mut z = Vec::with_capacity(P::L);
    for _ in 0..P::L {
        z.push(bit_unpack(
            &bytes[offset..offset + packed_z_bytes],
            P::GAMMA1 - 1,
            P::GAMMA1,
            P::z_coefficient_bits(),
        )?);
        offset += packed_z_bytes;
    }
    let h = unpack_hint::<P>(&bytes[offset..offset + P::OMEGA + P::K])?;
    Some(Signature { c_tilde, z, h })
}

pub fn decode_public_key<P: MlDsaParams>(bytes: &[u8]) -> Option<PublicKey> {
    if bytes.len() != P::public_key_bytes() {
        return None;
    }
    let rho = &bytes[..32];
    let a_hat = expand_a::<P>(rho)?;
    let mut t1 = Vec::with_capacity(P::K);
    for packed in bytes[32..P::public_key_bytes()].as_chunks::<320>().0 {
        t1.push(simple_bit_unpack(packed, 1023)?);
    }
    let hash = shake256_witness(bytes, 64).0;
    Some(PublicKey {
        a_hat,
        t1,
        tr: hash.try_into().unwrap(),
    })
}

pub fn preprocess_message(message: &[u8], context: &[u8]) -> Option<Vec<u8>> {
    if context.len() > u8::MAX as usize {
        return None;
    }
    let mut result = Vec::with_capacity(message.len() + context.len() + 2);
    result.extend([0, context.len() as u8]);
    result.extend(context);
    result.extend(message);
    Some(result)
}

pub fn encode_w1<P: MlDsaParams>(w1: &[Polynomial]) -> Option<Vec<u8>> {
    if w1.len() != P::K {
        return None;
    }
    let upper_bound = P::use_hint_modulus() - 1;
    let mut result = Vec::with_capacity(P::K * P::W1_BYTES);
    for polynomial in w1 {
        result.extend(simple_bit_pack(polynomial, upper_bound)?);
    }
    Some(result)
}

pub fn verify<P: MlDsaParams>(
    public_key_bytes: &[u8],
    signature_bytes: &[u8],
    message: &[u8],
    context: &[u8],
) -> bool {
    let Some(public_key) = decode_public_key::<P>(public_key_bytes) else {
        return false;
    };
    let Some(signature) = decode_signature::<P>(signature_bytes) else {
        return false;
    };
    let Some(preprocessed) = preprocess_message(message, context) else {
        return false;
    };
    let mut mu_input = public_key.tr.to_vec();
    mu_input.extend(preprocessed);
    let mu = shake256_witness(&mu_input, 64).0;

    let bound = P::GAMMA1 - P::REJECTION_BOUND;
    if signature.z.iter().flatten().any(|&coefficient| {
        let signed = if coefficient > Q / 2 {
            i64::from(coefficient) - i64::from(Q)
        } else {
            i64::from(coefficient)
        };
        signed.unsigned_abs() >= u64::from(bound)
    }) {
        return false;
    }
    let Some((mut challenge_ntt, _)) = sample_in_ball::<P>(&signature.c_tilde) else {
        return false;
    };
    ntt(&mut challenge_ntt);
    let mut z_ntt = signature.z.clone();
    for polynomial in &mut z_ntt {
        ntt(polynomial);
    }
    let t1_ntt = public_key.ntt_t1();

    let mut w1 = vec![[0u32; N]; P::K];
    for (row, t1_ntt_row) in t1_ntt.iter().enumerate().take(P::K) {
        let mut approximation_ntt = [0u32; N];
        for (column, z_ntt_column) in z_ntt.iter().enumerate().take(P::L) {
            for i in 0..N {
                approximation_ntt[i] = add(
                    approximation_ntt[i],
                    mul(public_key.a_hat[row][column][i], z_ntt_column[i]),
                );
            }
        }
        for i in 0..N {
            approximation_ntt[i] = sub(approximation_ntt[i], mul(challenge_ntt[i], t1_ntt_row[i]));
        }
        inverse_ntt(&mut approximation_ntt);
        for i in 0..N {
            w1[row][i] = use_hint::<P>(signature.h[row][i], approximation_ntt[i] as i32);
        }
    }
    if signature.h.iter().flatten().filter(|&&hint| hint).count() > P::OMEGA {
        return false;
    }
    let Some(encoded_w1) = encode_w1::<P>(&w1) else {
        return false;
    };
    let mut challenge_input = mu;
    challenge_input.extend(encoded_w1);
    shake256_witness(&challenge_input, P::C_TILDE_BYTES).0 == signature.c_tilde
}
