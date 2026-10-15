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

//! Integrated ML-DSA verifier circuit and native witness generation.

use std::marker::PhantomData;

use circuits_bitvec::{BitvecIO, BitvecLogic, V8};
use circuits_boolean::{Bitw, BooleanIO};
use compile_logic::{Logic, LogicIO};
use core_algebra::SupportsU64Conversions;

use super::{
    algebra::Q,
    circuit::{MlDsaCircuit, PolynomialW},
    params::{MlDsaParams, N},
    reference::{
        decode_public_key, decode_signature, decompose, encode_w1, inverse_ntt, ntt,
        preprocess_message, use_hint, Polynomial, PublicKey, Signature,
    },
    sample::{
        allocate_witness as allocate_sample_witness, assert_sample_in_ball, sample_in_ball,
        ConcreteSampleInBallWitness, SampleInBallWitness,
    },
    shake::{
        allocate_witness as allocate_shake_witness, shake256_witness, ConcreteShake256Witness,
        Shake256, Shake256Witness,
    },
};

pub type BitDecompositions<L> = Vec<Vec<Vec<Bitw<L>>>>;

fn input_bytes<L: LogicIO>(bitvec: &BitvecLogic<L>, position: &mut usize, n: usize) -> Vec<V8<L>> {
    let io = BitvecIO::new(bitvec);
    (0..n).map(|_| io.next(position)).collect()
}

fn input_bits<L: LogicIO>(logic: &L, position: &mut usize, n: usize) -> Vec<Bitw<L>> {
    let io = BooleanIO::new(logic);
    (0..n).map(|_| io.next(position)).collect()
}

fn input_polynomials<L: LogicIO>(logic: &L, position: &mut usize, n: usize) -> Vec<PolynomialW<L>> {
    (0..n)
        .map(|_| PolynomialW::input(logic, position))
        .collect()
}

fn input_decompositions<L: LogicIO>(
    logic: &L,
    position: &mut usize,
    polynomials: usize,
    width: usize,
) -> BitDecompositions<L> {
    (0..polynomials)
        .map(|_| (0..N).map(|_| input_bits(logic, position, width)).collect())
        .collect()
}

pub struct PublicKeyW<L: Logic> {
    pub a_hat: Vec<Vec<PolynomialW<L>>>,
    pub ntt_t1: Vec<PolynomialW<L>>,
}

impl<L: LogicIO> PublicKeyW<L> {
    pub fn input<P: MlDsaParams>(logic: &L, bitvec: &BitvecLogic<L>, position: &mut usize) -> Self {
        let a_hat = (0..P::K)
            .map(|_| input_polynomials(logic, position, P::L))
            .collect();
        let ntt_t1 = input_polynomials(logic, position, P::K);
        let _ = bitvec;
        Self { a_hat, ntt_t1 }
    }
}

pub struct SignatureW<L: Logic> {
    pub c_tilde: Vec<V8<L>>,
    pub z: Vec<PolynomialW<L>>,
    pub z_bits: BitDecompositions<L>,
    pub h: Vec<PolynomialW<L>>,
}

impl<L: LogicIO> SignatureW<L> {
    pub fn input<P: MlDsaParams>(logic: &L, bitvec: &BitvecLogic<L>, position: &mut usize) -> Self {
        Self {
            c_tilde: input_bytes(bitvec, position, P::C_TILDE_BYTES),
            z: input_polynomials(logic, position, P::L),
            z_bits: input_decompositions(logic, position, P::L, P::Z_BITS),
            h: input_polynomials(logic, position, P::K),
        }
    }
}

pub struct VerificationWitness<L: Logic> {
    pub sample: SampleInBallWitness<L>,
    pub c: PolynomialW<L>,
    pub approximation: Vec<PolynomialW<L>>,
    pub raw_high: Vec<PolynomialW<L>>,
    pub raw_high_bits: BitDecompositions<L>,
    pub hint_auxiliary_bits: BitDecompositions<L>,
    pub hinted_high: Vec<PolynomialW<L>>,
    pub hinted_high_bits: BitDecompositions<L>,
    pub ntt_z: Vec<PolynomialW<L>>,
    pub ntt_c: PolynomialW<L>,
    pub encoded_w1: Vec<V8<L>>,
    pub challenge_hash: Shake256Witness<L>,
    pub hint_sum_bits: Vec<Bitw<L>>,
}

impl<L: LogicIO> VerificationWitness<L> {
    pub fn input<P: MlDsaParams>(logic: &L, bitvec: &BitvecLogic<L>, position: &mut usize) -> Self {
        let sample = allocate_sample_witness::<_, P>(bitvec, position);
        let c = PolynomialW::input(logic, position);
        let mut approximation = Vec::with_capacity(P::K);
        let mut raw_high = Vec::with_capacity(P::K);
        let mut raw_high_bits = Vec::with_capacity(P::K);
        let mut hint_auxiliary_bits = Vec::with_capacity(P::K);
        let mut hinted_high = Vec::with_capacity(P::K);
        let mut hinted_high_bits = Vec::with_capacity(P::K);
        for _ in 0..P::K {
            approximation.push(PolynomialW::input(logic, position));
            raw_high.push(PolynomialW::input(logic, position));
            raw_high_bits.push(
                (0..N)
                    .map(|_| input_bits(logic, position, P::R1_BITS))
                    .collect(),
            );
            hint_auxiliary_bits.push(
                (0..N)
                    .map(|_| input_bits(logic, position, P::r0_bits() + 1))
                    .collect(),
            );
            hinted_high.push(PolynomialW::input(logic, position));
            hinted_high_bits.push(
                (0..N)
                    .map(|_| input_bits(logic, position, P::R1_BITS))
                    .collect(),
            );
        }
        let ntt_z = input_polynomials(logic, position, P::L);
        let ntt_c = PolynomialW::input(logic, position);
        let encoded_w1 = input_bytes(bitvec, position, P::K * P::W1_BYTES);
        let challenge_hash =
            allocate_shake_witness(bitvec, position, 64 + P::K * P::W1_BYTES, P::C_TILDE_BYTES);
        let hint_sum_bits = input_bits(
            logic,
            position,
            (usize::BITS - P::OMEGA.leading_zeros()) as usize,
        );
        Self {
            sample,
            c,
            approximation,
            raw_high,
            raw_high_bits,
            hint_auxiliary_bits,
            hinted_high,
            hinted_high_bits,
            ntt_z,
            ntt_c,
            encoded_w1,
            challenge_hash,
            hint_sum_bits,
        }
    }
}

pub struct MlDsaVerifier<'a, L: Logic, P: MlDsaParams> {
    logic: &'a L,
    bitvec: BitvecLogic<'a, L>,
    arithmetic: MlDsaCircuit<'a, L, P>,
    _params: PhantomData<P>,
}

impl<'a, L, P> MlDsaVerifier<'a, L, P>
where
    L: Logic,
    L::F: SupportsU64Conversions,
    P: MlDsaParams,
{
    pub fn new(logic: &'a L) -> Self {
        Self {
            logic,
            bitvec: BitvecLogic::new(logic),
            arithmetic: MlDsaCircuit::new(logic),
            _params: PhantomData,
        }
    }

    /// Checks the signature against an expanded public key and a supplied 64-byte mu.
    /// Key expansion and message-to-mu hashing are performed outside this circuit;
    /// the caller is responsible for binding these inputs to its intended statement.
    pub fn assert_valid_signature_on_mu(
        &self,
        public_key: &PublicKeyW<L>,
        signature: &SignatureW<L>,
        mu: &[V8<L>],
        witness: &VerificationWitness<L>,
    ) -> L::Assertions {
        assert_eq!(mu.len(), 64);
        let sample = assert_sample_in_ball::<_, P>(
            self.logic,
            &signature.c_tilde,
            &witness.c,
            &witness.sample,
        );
        let approximation = self.arithmetic.assert_w_approximation(
            &public_key.a_hat,
            &public_key.ntt_t1,
            &signature.z,
            &witness.c,
            &witness.ntt_z,
            &witness.ntt_c,
            &witness.approximation,
        );
        let hints = self.arithmetic.assert_use_hint(
            &signature.h,
            &witness.approximation,
            &witness.raw_high,
            &witness.raw_high_bits,
            &witness.hint_auxiliary_bits,
            &witness.hinted_high,
            &witness.hinted_high_bits,
            &witness.hint_sum_bits,
        );
        let encoding = self
            .arithmetic
            .assert_w1_encode(&witness.hinted_high_bits, &witness.encoded_w1);
        let norm = self.arithmetic.assert_infinity_norm(
            "z_norm",
            &signature.z,
            &signature.z_bits,
            P::Z_BITS,
            P::GAMMA1 - P::REJECTION_BOUND,
        );

        let mut hash_input = mu.to_vec();
        hash_input.extend(witness.encoded_w1.iter().cloned());
        let shake = Shake256::new(self.logic);
        let (computed_challenge, hash_assertions) =
            shake.assert_hash(&hash_input, P::C_TILDE_BYTES, &witness.challenge_hash);
        let challenge_equality =
            self.logic
                .assert_mapi("challenge_hash", 0..P::C_TILDE_BYTES, |i| {
                    self.bitvec
                        .assert_eq("byte", &computed_challenge[i], &signature.c_tilde[i])
                });
        self.logic.assert_all(
            "mldsa_verify",
            &[
                sample,
                approximation,
                hints,
                encoding,
                norm,
                hash_assertions,
                challenge_equality,
            ],
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcretePublicKey {
    pub a_hat: Vec<Vec<Polynomial>>,
    pub ntt_t1: Vec<Polynomial>,
    pub tr: [u8; 64],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteSignature {
    pub c_tilde: Vec<u8>,
    pub z: Vec<Polynomial>,
    pub z_bits: Vec<Vec<u64>>,
    pub h: Vec<Polynomial>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteVerificationWitness {
    pub sample: ConcreteSampleInBallWitness,
    pub c: Polynomial,
    pub approximation: Vec<Polynomial>,
    pub raw_high: Vec<Polynomial>,
    pub raw_high_bits: Vec<Vec<u64>>,
    pub hint_auxiliary_bits: Vec<Vec<u64>>,
    pub hinted_high: Vec<Polynomial>,
    pub hinted_high_bits: Vec<Vec<u64>>,
    pub ntt_z: Vec<Polynomial>,
    pub ntt_c: Polynomial,
    pub encoded_w1: Vec<u8>,
    pub challenge_hash: ConcreteShake256Witness,
    pub hint_sum: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteInstance<P: MlDsaParams> {
    pub public_key: ConcretePublicKey,
    pub signature: ConcreteSignature,
    pub witness: ConcreteVerificationWitness,
    pub mu: [u8; 64],
    _params: PhantomData<P>,
}

#[inline]
fn q_add(a: u32, b: u32) -> u32 {
    let sum = a + b;
    if sum >= Q {
        sum - Q
    } else {
        sum
    }
}

#[inline]
fn q_sub(a: u32, b: u32) -> u32 {
    if a >= b {
        a - b
    } else {
        a + Q - b
    }
}

#[inline]
fn q_mul(a: u32, b: u32) -> u32 {
    (u64::from(a) * u64::from(b) % u64::from(Q)) as u32
}

fn make_ntt_t1(public_key: &PublicKey) -> Vec<Polynomial> {
    public_key
        .t1
        .iter()
        .map(|polynomial| {
            let mut result = polynomial.map(|coefficient| q_mul(coefficient, 1 << 13));
            ntt(&mut result);
            result
        })
        .collect()
}

fn make_signature<P: MlDsaParams>(signature: &Signature) -> ConcreteSignature {
    let bound = P::GAMMA1 - P::REJECTION_BOUND;
    let z_bits = signature
        .z
        .iter()
        .map(|polynomial| {
            polynomial
                .iter()
                .map(|&coefficient| {
                    let signed = if coefficient > Q / 2 {
                        i64::from(coefficient) - i64::from(Q)
                    } else {
                        i64::from(coefficient)
                    };
                    (signed + i64::from(bound - 1)) as u64
                })
                .collect()
        })
        .collect();
    let h = signature
        .h
        .iter()
        .map(|polynomial| polynomial.map(u32::from))
        .collect();
    ConcreteSignature {
        c_tilde: signature.c_tilde.clone(),
        z: signature.z.clone(),
        z_bits,
        h,
    }
}

impl<P: MlDsaParams> ConcreteInstance<P> {
    pub fn new(
        public_key_bytes: &[u8],
        signature_bytes: &[u8],
        message: &[u8],
        context: &[u8],
    ) -> Option<Self> {
        let public_key = decode_public_key::<P>(public_key_bytes)?;
        let signature = decode_signature::<P>(signature_bytes)?;
        let ntt_t1 = make_ntt_t1(&public_key);
        let mut mu_input = public_key.tr.to_vec();
        mu_input.extend(preprocess_message(message, context)?);
        let mu: [u8; 64] = shake256_witness(&mu_input, 64).0.try_into().unwrap();
        let (c, sample) = sample_in_ball::<P>(&signature.c_tilde)?;
        let mut ntt_c = c;
        ntt(&mut ntt_c);
        let mut ntt_z = signature.z.clone();
        for polynomial in &mut ntt_z {
            ntt(polynomial);
        }

        let mut approximation = Vec::with_capacity(P::K);
        let mut raw_high = Vec::with_capacity(P::K);
        let mut raw_high_bits = Vec::with_capacity(P::K);
        let mut hint_auxiliary_bits = Vec::with_capacity(P::K);
        let mut hinted_high = Vec::with_capacity(P::K);
        let mut hinted_high_bits = Vec::with_capacity(P::K);
        for (row, ntt_t1_row) in ntt_t1.iter().enumerate().take(P::K) {
            let mut approximate = [0u32; N];
            for (column, ntt_z_column) in ntt_z.iter().enumerate().take(P::L) {
                for i in 0..N {
                    approximate[i] = q_add(
                        approximate[i],
                        q_mul(public_key.a_hat[row][column][i], ntt_z_column[i]),
                    );
                }
            }
            for i in 0..N {
                approximate[i] = q_sub(approximate[i], q_mul(ntt_c[i], ntt_t1_row[i]));
            }
            inverse_ntt(&mut approximate);
            let mut raw = [0u32; N];
            let mut aux = Vec::with_capacity(N);
            let mut hinted = [0u32; N];
            for i in 0..N {
                let (r1, r0) = decompose::<P>(approximate[i] as i32);
                raw[i] = r1 as u32;
                hinted[i] = use_hint::<P>(signature.h[row][i], approximate[i] as i32);
                aux.push((r0 + P::GAMMA2 as i32) as u64 | (u64::from(r0 <= 0) << P::r0_bits()));
            }
            approximation.push(approximate);
            raw_high_bits.push(raw.iter().map(|&value| u64::from(value)).collect());
            hint_auxiliary_bits.push(aux);
            hinted_high_bits.push(hinted.iter().map(|&value| u64::from(value)).collect());
            raw_high.push(raw);
            hinted_high.push(hinted);
        }
        let encoded_w1 = encode_w1::<P>(&hinted_high)?;
        let mut challenge_input = mu.to_vec();
        challenge_input.extend(&encoded_w1);
        let (computed_challenge, challenge_hash) =
            shake256_witness(&challenge_input, P::C_TILDE_BYTES);
        if computed_challenge != signature.c_tilde {
            return None;
        }
        let hint_sum = signature.h.iter().flatten().filter(|&&hint| hint).count() as u64;
        Some(Self {
            public_key: ConcretePublicKey {
                a_hat: public_key.a_hat,
                ntt_t1,
                tr: public_key.tr,
            },
            signature: make_signature::<P>(&signature),
            witness: ConcreteVerificationWitness {
                sample,
                c,
                approximation,
                raw_high,
                raw_high_bits,
                hint_auxiliary_bits,
                hinted_high,
                hinted_high_bits,
                ntt_z,
                ntt_c,
                encoded_w1,
                challenge_hash,
                hint_sum,
            },
            mu,
            _params: PhantomData,
        })
    }
}

#[cfg(feature = "mldsa-runtime")]
fn push_polynomial<const W: usize, F>(
    field: &F,
    polynomial: &Polynomial,
    destination: &mut Vec<F::E>,
) where
    F: runtime_algebra::RuntimeField<W> + core_algebra::SupportsU64Conversions,
{
    destination.extend(
        polynomial
            .iter()
            .map(|&coefficient| field.u64_to_element(u64::from(coefficient))),
    );
}

#[cfg(feature = "mldsa-runtime")]
fn push_bytes<const W: usize, F: runtime_algebra::RuntimeField<W>>(
    field: &F,
    bytes: &[u8],
    destination: &mut Vec<F::E>,
) {
    for &byte in bytes {
        circuits_bitvec::concrete::push_bitvec_u64(field, u64::from(byte), 8, destination);
    }
}

#[cfg(feature = "mldsa-runtime")]
fn push_bits<const W: usize, F>(field: &F, value: u64, width: usize, destination: &mut Vec<F::E>)
where
    F: runtime_algebra::RuntimeField<W>,
{
    circuits_bitvec::concrete::push_bitvec_u64(field, value, width, destination);
}

#[cfg(feature = "mldsa-runtime")]
impl<P: MlDsaParams> ConcreteInstance<P> {
    pub fn push_wires<
        F: runtime_algebra::RuntimeField<W> + SupportsU64Conversions + core_algebra::HasLookupPoints,
        const W: usize,
    >(
        &self,
        field: &F,
        destination: &mut Vec<F::E>,
    ) {
        for row in &self.public_key.a_hat {
            for polynomial in row {
                push_polynomial(field, polynomial, destination);
            }
        }
        for polynomial in &self.public_key.ntt_t1 {
            push_polynomial(field, polynomial, destination);
        }
        push_bytes(field, &self.signature.c_tilde, destination);
        for polynomial in &self.signature.z {
            push_polynomial(field, polynomial, destination);
        }
        for polynomial in &self.signature.z_bits {
            for &value in polynomial {
                push_bits(field, value, P::Z_BITS, destination);
            }
        }
        for polynomial in &self.signature.h {
            push_polynomial(field, polynomial, destination);
        }

        self.witness.sample.push_wires(field, destination);
        push_polynomial(field, &self.witness.c, destination);
        for row in 0..P::K {
            push_polynomial(field, &self.witness.approximation[row], destination);
            push_polynomial(field, &self.witness.raw_high[row], destination);
            for &value in &self.witness.raw_high_bits[row] {
                push_bits(field, value, P::R1_BITS, destination);
            }
            for &value in &self.witness.hint_auxiliary_bits[row] {
                push_bits(field, value, P::r0_bits() + 1, destination);
            }
            push_polynomial(field, &self.witness.hinted_high[row], destination);
            for &value in &self.witness.hinted_high_bits[row] {
                push_bits(field, value, P::R1_BITS, destination);
            }
        }
        for polynomial in &self.witness.ntt_z {
            push_polynomial(field, polynomial, destination);
        }
        push_polynomial(field, &self.witness.ntt_c, destination);
        push_bytes(field, &self.witness.encoded_w1, destination);
        self.witness.challenge_hash.push_wires(field, destination);
        circuits_bitvec::concrete::push_bitvec_u64(
            field,
            self.witness.hint_sum,
            (usize::BITS - P::OMEGA.leading_zeros()) as usize,
            destination,
        );
        push_bytes(field, &self.mu, destination);
    }
}
