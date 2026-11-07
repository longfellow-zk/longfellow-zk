// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
// Explicit test-only replay helpers; none are compiled into proof-role builds.
impl Transcript {
    pub(crate) fn round_count_for_test(&self) -> u64 {
        self.core.rounds
    }
    pub(crate) fn fork_for_test(&self) -> Self {
        Self {
            core: Core {
                hash: self.core.hash.clone(),
                rounds: self.core.rounds,
            },
        }
    }
    pub(crate) fn bytes(&mut self, n: usize) -> Vec<u8> {
        self.round(RoundLabel::Statement, |w| {
            let mut r = w.begin_squeeze();
            let x = r.bytes(n);
            r.end_round(x)
        })
    }
    pub(crate) fn u128(&mut self) -> u128 {
        u128::from_le_bytes(self.bytes(16).try_into().unwrap())
    }
}
impl TranscriptRef<'_> {
    pub(crate) fn round_count_for_test(&self) -> u64 {
        self.core.rounds
    }
    pub(crate) fn fork_for_test(&self) -> Transcript {
        Transcript {
            core: Core {
                hash: self.core.hash.clone(),
                rounds: self.core.rounds,
            },
        }
    }
    pub(crate) fn bytes(&mut self, n: usize) -> Vec<u8> {
        self.round(RoundLabel::Statement, |w| {
            let mut reader = w.begin_squeeze();
            let bytes = reader.bytes(n);
            reader.end_round(bytes)
        })
    }
    pub(crate) fn u128(&mut self) -> u128 {
        u128::from_le_bytes(self.bytes(16).try_into().unwrap())
    }
}
#[test]
fn empty_rounds_are_distinct_and_reproducible() {
    let mut a = Transcript::new(b"rounds");
    let mut b = Transcript::new(b"rounds");
    let x = a.bytes(32);
    let y = a.bytes(32);
    assert_ne!(x, y);
    assert_eq!(x, b.bytes(32));
    assert_eq!(y, b.bytes(32));
}
#[test]
fn final_seal_binds_body_context_and_rounds() {
    let mut a = Transcript::new(b"seal");
    a.bytes(1);
    let mut b = Transcript::new(b"seal");
    b.bytes(1);
    let encoded = a.append_final_seal(vec![1, 2, 3]).into_bytes();
    assert!(b.verify_final_seal(&encoded).is_ok());
    assert!(Transcript::new(b"seal")
        .verify_final_seal(&encoded)
        .is_err());
    let mut changed = encoded;
    changed[0] ^= 1;
    let mut c = Transcript::new(b"seal");
    c.bytes(1);
    assert!(c.verify_final_seal(&changed).is_err());
}

#[test]
fn independent_direct_shake256_vector_and_chunking() {
    let mut t = Transcript::new(b"vector");
    let bytes = t.round(RoundLabel::Sumcheck, |mut w| {
        w.write_bytes(b"message");
        let mut r = w.begin_squeeze();
        let mut bytes = r.bytes(3);
        bytes.extend(r.bytes(157));
        r.end_round(bytes)
    });
    assert_eq!(hex::encode(bytes),"d4a691d93c48c8d9a5b7b0b1bd10059fa9adb266fdf720c6af9abd813e83c5320e47b37dedb6c5d02c0610e13fe2bdd37bb1f1d1d6c292d8651a3e02d65db57b368aff95a676c49cc5e99b6f741af9b3a44a4a5f232c83f6074172b46c47ba5a0d9b38ec91870f3036b999505b8c3b91419f4277bbbbc8a06ba4062d7b09827438fb853263ad988fedbc9b5ed1d28b02ae6bb36c5f115d2cdda3e2461c7317ac");
    let sealed = t.append_final_seal(vec![1, 2, 3]).into_bytes();
    assert_eq!(
        hex::encode(&sealed[3..]),
        "037b774106e001430e0d19cf138e646f66900fe683da81adcad7a9d3a8ff5062"
    );
}
#[test]
fn distinct_labels_and_terminal_authentication_are_bound() {
    let run = |label| {
        let mut t = Transcript::new(b"roles");
        t.round(label, |w| w.begin_squeeze().end_round(()));
        t.append_final_seal(vec![9]).into_bytes()
    };
    assert_ne!(run(RoundLabel::Sumcheck), run(RoundLabel::Packing));
    let mut bytes = run(RoundLabel::Sumcheck);
    bytes[0] ^= 1;
    let mut t = Transcript::new(b"roles");
    t.round(RoundLabel::Sumcheck, |w| w.begin_squeeze().end_round(()));
    assert!(t.verify_final_seal(&bytes).is_err());
}

#[test]
fn feedback_and_round_number_match_independent_two_round_vector() {
    let mut t = Transcript::new(b"feedback");
    assert_eq!(
        hex::encode(t.bytes(32)),
        "ec902d18d749e457c2920657ee43a4c0f29b6fc24fb16322999ef7999a096a32"
    );
    assert_eq!(
        hex::encode(t.bytes(32)),
        "8d37245124c02ea239e27bdb53d363577355659b31625a39109c2ebf6d0e2b04"
    );
    assert_eq!(t.core.rounds, 2);
}
#[test]
fn large_blocks_extend_the_same_xof_answer() {
    let mut a = Transcript::new(b"large");
    let mut b = a.fork_for_test();
    let whole = a.round(RoundLabel::Packing, |w| {
        let mut r = w.begin_squeeze();
        let x = r.bytes(65537);
        r.end_round(x)
    });
    let parts = b.round(RoundLabel::Packing, |w| {
        let mut r = w.begin_squeeze();
        let mut x = Vec::new();
        for n in [0, 1, 135, 136, 137, 4096, 60896, 136] {
            x.extend(r.bytes(n));
        }
        r.end_round(x)
    });
    assert_eq!(whole, parts);
    assert_eq!(
        a.append_final_seal(vec![]).into_bytes(),
        b.append_final_seal(vec![]).into_bytes()
    );
}
#[test]
fn field_rejection_keeps_one_round_and_preserves_the_xof_cursor() {
    use crate::{
        core::algebra::SupportsU64Conversions,
        runtime::algebra::{fp_generic::FpGenericField, LIMBS_PER_U64},
    };
    let f = FpGenericField::<1, { LIMBS_PER_U64 }, { 3 * LIMBS_PER_U64 }, ()>::new_generic([17]);
    for seed in 0u8..64 {
        let mut actual = Transcript::new(&[seed]);
        let mut reference = actual.fork_for_test();
        let (expected, tail, attempts) = reference.round(RoundLabel::Conversion, |w| {
            let mut r = w.begin_squeeze();
            let mut attempts = 0;
            let expected = loop {
                attempts += 1;
                let x = r.bytes(1)[0] & 31;
                if x < 17 {
                    break f.u64_to_element(x as u64);
                }
            };
            let tail = r.bytes(32);
            r.end_round((expected, tail, attempts))
        });
        if attempts > 1 {
            let (value, remaining) = actual.round(RoundLabel::Conversion, |w| {
                let mut r = w.begin_squeeze();
                let value = r.elt_field(&f);
                let tail = r.bytes(32);
                r.end_round((value, tail))
            });
            assert_eq!(value, expected);
            assert_eq!(remaining, tail);
            assert_eq!(actual.core.rounds, 1);
            return;
        }
    }
    panic!("fixed test seeds must include a rejected field sample");
}
