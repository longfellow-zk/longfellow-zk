// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Native ML-DSA arithmetic and witness generation; independent of the compiler.

mod model;
pub use model::Polynomial;

mod algorithm;
pub use algorithm::{
    decode_public_key, decode_signature, decompose, encode_w1, expand_a, inverse_ntt, ntt,
    pointwise_mul, preprocess_message, rejection_sample_ntt_polynomial, ring_mul, simple_bit_pack,
    simple_bit_unpack, use_hint, verify, PublicKey, Signature,
};
mod instance;
pub use instance::{
    ConcreteInstance, ConcretePublicKey, ConcreteSignature, ConcreteVerificationWitness,
};
mod sample;
pub use sample::{sample_in_ball, ConcreteSampleInBallWitness};
mod shake;
pub use shake::{shake128, shake128_witness, shake256_witness, ConcreteShake256Witness};
