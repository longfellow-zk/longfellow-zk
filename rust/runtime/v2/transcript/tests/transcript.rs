// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::v2::proto::RoundLabel;
const TEST_ROUND: u8 = 6;
// Explicit test-only replay helpers; none are compiled into proof-role builds.
impl Transcript {
    pub(crate) fn round_count_for_test(&self) -> u64 {
        self._round_count.0
    }
    pub(crate) fn fork_for_test(&self) -> Self {
        Self {
            strand: self.strand.clone_for_test(),
            _round_count: RoundCount(self._round_count.0),
        }
    }
    pub(crate) fn bytes(&mut self, n: usize) -> Vec<u8> {
        self.round(TEST_ROUND, |w| {
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
        self.session._round_count.0
    }
    pub(crate) fn fork_for_test(&self) -> Transcript {
        Transcript {
            strand: self.session.strand.clone_for_test(),
            _round_count: RoundCount(self.session._round_count.0),
        }
    }
    pub(crate) fn bytes(&mut self, n: usize) -> Vec<u8> {
        self.round(TEST_ROUND, |w| {
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
fn final_seal_binds_body_context_and_parent_chain() {
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
fn final_seal_rejects_wrong_context_altered_seals_and_short_proofs() {
    let encoded = Transcript::new(b"seal rejection")
        .append_final_seal(vec![1, 2, 3])
        .into_bytes();
    assert!(Transcript::new(b"other context")
        .verify_final_seal(&encoded)
        .is_err());
    for i in 3..encoded.len() {
        let mut changed = encoded.clone();
        changed[i] ^= 1;
        assert!(Transcript::new(b"seal rejection")
            .verify_final_seal(&changed)
            .is_err());
    }
    for len in 0..32 {
        assert_eq!(
            Transcript::new(b"seal rejection").verify_final_seal(&encoded[..len]),
            Err("missing final seal")
        );
    }
}

#[test]
fn independent_sha256_strand_vector_and_chunking() {
    let mut t = Transcript::new(b"vector");
    let bytes = t.round(RoundLabel::Sumcheck, |mut w| {
        w.write_bytes(b"message");
        let mut r = w.begin_squeeze();
        let mut bytes = r.bytes(3);
        bytes.extend(r.bytes(157));
        r.end_round(bytes)
    });
    assert_eq!(hex::encode(bytes),"cc4be31d3e4ce600a56f63b0236f5bd211296be33e4834da3901ac4cf6a21917cea71d8ea3d647fcd070d43cd99882e7a0dbd2fa8ba63cbda4c02faa62ca0e75f64ac6bf13764a0c35b5ab88807bb6ccf4691cff1b290f394e1a73967547636cbb22bb613f288b3d81730ff2a766791935efbd9ea70229a36ec2f6047f5ea9d01b3e847e50a6f6d83102e05c3b8d7b056e8c727d3431027447e00f55ef7501cc");
    let sealed = t.append_final_seal(vec![1, 2, 3]).into_bytes();
    assert_eq!(
        hex::encode(&sealed[3..]),
        "bdd3990dff3dfdd410ab8ec8e2ffe1f2f738908e29fc83fe9054fd2e4d7ea44c"
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
fn parent_chain_matches_independent_two_round_vector() {
    let mut t = Transcript::new(b"feedback");
    assert_eq!(
        hex::encode(t.bytes(32)),
        "0e5adbfa0ab03fef54b0925af4c171995fe070e0e024d6a23b64fc6758300dca"
    );
    assert_eq!(
        hex::encode(t.bytes(32)),
        "b3a4f9b134d29d6110d15e195d477269e289dcf201cf39238cbdb626b014fe8d"
    );
    assert_eq!(t._round_count.0, 2);
}
#[test]
fn large_reads_extend_the_same_prf_stream() {
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
fn field_rejection_keeps_one_round_and_preserves_the_prf_cursor() {
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
                let actual_tail = r.bytes(32);
                r.end_round((value, actual_tail))
            });
            assert_eq!(value, expected);
            assert_eq!(remaining, tail);
            assert_eq!(actual._round_count.0, 1);
            return;
        }
    }
    panic!("fixed test seeds must include a rejected field sample");
}

#[test]
fn power_of_two_indices_consume_only_the_required_bytes() {
    for bits in 0..usize::BITS {
        let n = 1usize << bits;
        let mut actual = Transcript::new(b"index bytes");
        let mut reference = actual.fork_for_test();
        let (expected, tail) = reference.round(RoundLabel::Opening, |w| {
            let mut r = w.begin_squeeze();
            let values: Vec<_> = (0..32)
                .map(|_| {
                    let mut bytes = [0; size_of::<usize>()];
                    let len = bits.div_ceil(8) as usize;
                    bytes[..len].copy_from_slice(&r.bytes(len));
                    usize::from_le_bytes(bytes) & (n - 1)
                })
                .collect();
            let tail = r.bytes(32);
            r.end_round((values, tail))
        });
        let sampled = actual.round(RoundLabel::Opening, |w| {
            let mut r = w.begin_squeeze();
            let values: Vec<_> = (0..32).map(|_| r.nat(n)).collect();
            let remaining = r.bytes(32);
            r.end_round((values, remaining))
        });
        assert_eq!(sampled, (expected, tail), "bound {n}");
        assert_eq!(actual.round_count_for_test(), 1);
    }
}

#[test]
fn index_rejection_matches_the_same_prf_stream() {
    let mut saw_rejection = false;
    for (n, mask, len) in [
        (3, 3, 1),
        (17, 31, 1),
        (255, 255, 1),
        (257, 511, 2),
        (2443, 4095, 2),
        (usize::MAX, usize::MAX, size_of::<usize>()),
    ] {
        let mut actual = Transcript::new(b"index rejection");
        let mut reference = actual.fork_for_test();
        let (expected, tail, rejected) = reference.round(RoundLabel::Opening, |w| {
            let mut r = w.begin_squeeze();
            let mut rejected = false;
            let values: Vec<_> = (0..64)
                .map(|_| loop {
                    let mut bytes = [0; size_of::<usize>()];
                    bytes[..len].copy_from_slice(&r.bytes(len));
                    let value = usize::from_le_bytes(bytes) & mask;
                    if value < n {
                        break value;
                    }
                    rejected = true;
                })
                .collect();
            let tail = r.bytes(32);
            r.end_round((values, tail, rejected))
        });
        saw_rejection |= rejected;
        let sampled = actual.round(RoundLabel::Opening, |w| {
            let mut r = w.begin_squeeze();
            let values: Vec<_> = (0..64).map(|_| r.nat(n)).collect();
            let actual_tail = r.bytes(32);
            r.end_round((values, actual_tail))
        });
        assert_eq!(sampled, (expected, tail), "bound {n}");
    }
    assert!(saw_rejection);
}
