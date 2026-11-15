// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::algebra::{
        AlgebraicField, BareField, FieldID, SerializableField, SupportsU64Conversions,
    },
    runtime::{
        algebra::p256::P256Field,
        v2::{
            proto::tags::Tag,
            transcript::{
                message::ZkStatement, Encoder, Event, Message, ProverMessage, TestMessage,
            },
        },
    },
};
// Explicit test-only replay helpers; none are compiled into proof-role builds.
impl Transcript {
    /// A copy of this session's state with a fresh identity: a fork is
    /// another session, so multi-call states reject it.
    pub(crate) fn fork_for_test(&self) -> Self {
        Self {
            strand: self.strand.clone_for_test(),
            position: self.position,
            session: SessionStamp::fresh(),
            stream: self.stream.as_ref().map(Reader::clone_for_test),
            trace: self.trace.clone(),
        }
    }
    pub(crate) fn round_count_for_test(&self) -> u64 {
        self.trace.boundaries()
    }
    /// Send a test message.
    pub(crate) fn send_for_test(&mut self, bytes: &[u8]) {
        self.borrow().send(&TestMessage(bytes));
    }
    pub(crate) fn bytes(&mut self, n: usize) -> Vec<u8> {
        self.draw(|r| r.bytes(n))
    }
    pub(crate) fn u128(&mut self) -> u128 {
        u128::from_le_bytes(self.bytes(16).try_into().unwrap())
    }
}
impl TranscriptRef<'_> {
    pub(crate) fn fork_for_test(&self) -> Transcript {
        self.session.fork_for_test()
    }
}
fn le(x: u64) -> [u8; 8] {
    x.to_le_bytes()
}

/// The root node of `Transcript::for_test(b"vector")` with profile 1..4,
/// one test message and the ROUND terminator, built by hand from the byte
/// grammar.
fn vector_root() -> Vec<u8> {
    let mut v = Vec::new();
    v.extend(1u32.to_le_bytes());
    v.extend(le(0));
    v.extend(0u32.to_le_bytes());
    v.extend(le(17));
    for b in [&b"longfellow/v2/zk/transcript/v2"[..], b"vector"] {
        v.extend(le(0));
        v.extend(le(b.len() as u64));
        v.extend(b);
    }
    v.extend(le(1));
    v.extend(le(4));
    for x in 1..=4 {
        v.extend(le(x));
    }
    v.extend(le(32));
    v.extend(le(0));
    v.extend(le(7));
    v.extend(b"message");
    v.extend(le(0));
    v
}

/// The vectors are SHA-256 over the documented strand, PRF and message
/// encodings, computed outside this crate.
#[test]
fn independent_node_and_seal_vectors() {
    let mut t = Transcript::new(&ZkStatement {
        context: b"vector",
        profile: [1, 2, 3, 4],
    });
    t.send_for_test(b"message");
    let mut bytes = t.bytes(3);
    bytes.extend(t.bytes(157));
    assert_eq!(t.trace.nodes, [vector_root()]);
    assert_eq!(
        hex::encode(&bytes),
        concat!(
            "76265e7061a1ce11f409d9f1a1beef535d096e0f6d6620253b2f95ca8ed859f0",
            "b8c225b5d45d9e672a6c94da295d587fe21b2ce3ff0b50ac1e60dcc348c27767",
            "dd10df42992a32686279530768dff2ff5a564a9ffb423c1185ab223da4b8b92e",
            "982804442425be57d03dc621fef24997ac3c87a0d457ed604bbc4c7026cc37f0",
            "8f7dcaba5a72fae79789082e2372628df2a2bd67a70f1adb60833cc5c9ebfd7d"
        )
    );
    let sealed = t.append_final_seal(vec![1, 2, 3]).into_bytes();
    assert_eq!(
        hex::encode(&sealed[3..]),
        "c2506de2fade51d35c5a84653259bb5961a4c5238167e2960cf46e347aa3d83e"
    );
}

#[test]
fn draws_without_messages_are_distinct_and_reproducible() {
    let mut a = Transcript::for_test(b"rounds");
    let mut b = Transcript::for_test(b"rounds");
    let x = a.bytes(32);
    let y = a.bytes(32);
    assert_ne!(x, y);
    assert_eq!(x, b.bytes(32));
    assert_eq!(y, b.bytes(32));
    // The statement is the only message: one boundary.
    assert_eq!(a.round_count_for_test(), 1);
}
#[test]
fn final_seal_binds_body_context_and_parent_chain() {
    let mut a = Transcript::for_test(b"seal");
    a.bytes(1);
    let mut b = Transcript::for_test(b"seal");
    b.bytes(1);
    let encoded = a.append_final_seal(vec![1, 2, 3]).into_bytes();
    assert!(b.verify_final_seal(&encoded).is_ok());
    assert!(Transcript::for_test(b"seal")
        .verify_final_seal(&encoded)
        .is_err());
    let mut changed = encoded;
    changed[0] ^= 1;
    let mut c = Transcript::for_test(b"seal");
    c.bytes(1);
    assert!(c.verify_final_seal(&changed).is_err());
}

#[test]
fn final_seal_rejects_wrong_context_altered_seals_and_short_proofs() {
    let encoded = Transcript::for_test(b"seal rejection")
        .append_final_seal(vec![1, 2, 3])
        .into_bytes();
    assert!(Transcript::for_test(b"other context")
        .verify_final_seal(&encoded)
        .is_err());
    for i in 3..encoded.len() {
        let mut changed = encoded.clone();
        changed[i] ^= 1;
        assert!(Transcript::for_test(b"seal rejection")
            .verify_final_seal(&changed)
            .is_err());
    }
    for len in 0..32 {
        assert_eq!(
            Transcript::for_test(b"seal rejection").verify_final_seal(&encoded[..len]),
            Err("missing final seal")
        );
    }
}

#[test]
fn the_seal_node_holds_the_seal_message_and_terminator() {
    let mut t = Transcript::for_test(b"seal node");
    t.bytes(1);
    let proof = t.append_final_seal(vec![5, 6]);
    let trace = proof.trace_for_test();
    let node = trace.nodes.last().unwrap();
    let mut tail = le(112).to_vec();
    tail.extend(le(0));
    tail.extend(le(2));
    tail.extend([5, 6]);
    tail.extend(le(1));
    // Header: STRAND, id 1, one parent and its 32-byte digest.
    assert_eq!(node.len(), 4 + 8 + 4 + 32 + tail.len());
    assert!(node.ends_with(&tail));
    assert_eq!(trace.events.last(), Some(&Event::Seal));
}

#[test]
fn a_draw_without_a_message_continues_the_stream() {
    // Two draws with no message between them read one stream: the same
    // bytes as one draw that reads both, with nothing written between.
    let mut split = Transcript::for_test(b"continue");
    let mut whole = split.fork_for_test();
    split.send_for_test(b"claims");
    let first = split.bytes(5);
    let position = split.position();
    let second = split.bytes(40);
    assert!(split.position() == position);
    whole.send_for_test(b"claims");
    let both = whole.bytes(45);
    assert_eq!([first, second].concat(), both);
    assert_eq!(split.round_count_for_test(), 1);
    assert_eq!(split.bytes(32), whole.bytes(32));
    // A message ends the stream: the next draw ends the node.
    split.send_for_test(b"next");
    whole.send_for_test(b"next");
    assert_eq!(split.bytes(32), whole.bytes(32));
    assert_eq!(split.round_count_for_test(), 2);
}

#[test]
fn large_reads_extend_the_same_prf_stream() {
    let mut a = Transcript::for_test(b"large");
    let mut b = a.fork_for_test();
    let whole = a.bytes(65537);
    let parts = b.draw(|r| {
        let mut x = Vec::new();
        for n in [0, 1, 135, 136, 137, 4096, 60896, 136] {
            x.extend(r.bytes(n));
        }
        x
    });
    assert_eq!(whole, parts);
    assert_eq!(
        a.append_final_seal(vec![]).into_bytes(),
        b.append_final_seal(vec![]).into_bytes()
    );
}

/// The bytes one message adds to its node.
fn encoded(m: &impl Message) -> Vec<u8> {
    let mut t = Transcript::for_test(b"encoding");
    let before = t.strand.preimage.len();
    t.send_message(m);
    t.strand.preimage[before..].to_vec()
}

struct Values<'a> {
    bytes: &'a [u8],
    nats: &'a [u64],
    elements: &'a [<P256Field as BareField>::E],
    bits: &'a [bool],
}
impl Message for Values<'_> {
    const TAG: Tag = Tag::Seal;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bytes(self.bytes);
        e.nats(self.nats);
        e.elements(&P256Field::new(), self.elements);
        e.bits(self.bits.iter().copied());
    }
}
impl ProverMessage for Values<'_> {}

#[test]
fn each_value_kind_has_its_documented_encoding() {
    let p = P256Field::new();
    let elements = [p.one(), p.u64_to_element(7)];
    let bits = [
        true, false, true, true, false, false, false, false, true, true,
    ];
    let mut expected = le(112).to_vec();
    expected.extend(le(0));
    expected.extend(le(3));
    expected.extend(b"abc");
    expected.extend(le(1));
    expected.extend(le(2));
    expected.extend(le(5));
    expected.extend(le(u64::MAX));
    expected.extend(le(2));
    expected.extend(le(FieldID::P256 as u64));
    expected.extend(le(2));
    for x in &elements {
        expected.extend(p.to_bytes(x));
    }
    expected.extend(le(3));
    expected.extend(le(10));
    expected.extend([0b0000_1101, 0b0000_0011]);
    let m = Values {
        bytes: b"abc",
        nats: &[5, u64::MAX],
        elements: &elements,
        bits: &bits,
    };
    assert_eq!(encoded(&m), expected);
    // The recorded payload drops every header.
    let mut t = Transcript::for_test(b"payload");
    t.borrow().send(&m);
    let recorded = t.trace.messages().last().unwrap().clone();
    assert_eq!(recorded.tag, 112);
    assert_eq!(recorded.schema, [(0, 3), (1, 2), (2, 2), (3, 10)]);
    let mut payload = b"abc".to_vec();
    payload.extend(le(5));
    payload.extend(le(u64::MAX));
    for x in &elements {
        payload.extend(p.to_bytes(x));
    }
    payload.extend([0b0000_1101, 0b0000_0011]);
    assert_eq!(recorded.payload, payload);
}

struct Bits(Vec<bool>);
impl Message for Bits {
    const TAG: Tag = Tag::P256AdapterQuotients;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bits(self.0.iter().copied());
    }
}
impl ProverMessage for Bits {}

#[test]
fn bits_pack_least_significant_first_with_zero_padding() {
    for count in [0usize, 1, 7, 8, 9, 4095, 4096, 4097, 9000] {
        let bits: Vec<bool> = (0..count).map(|j| (j * 7 + j / 3) % 5 < 2).collect();
        let mut expected = le(65).to_vec();
        expected.extend(le(3));
        expected.extend(le(count as u64));
        let mut packed = vec![0u8; count.div_ceil(8)];
        for (j, &b) in bits.iter().enumerate() {
            packed[j / 8] |= u8::from(b) << (j % 8);
        }
        expected.extend(packed);
        assert_eq!(encoded(&Bits(bits)), expected, "{count} bits");
    }
}

#[test]
fn every_message_counts_and_only_a_draw_after_one_ends_a_node() {
    let mut t = Transcript::for_test(b"count");
    let start = t.position();
    t.bytes(1);
    t.bytes(1);
    t.send_for_test(b"a");
    t.send_for_test(b"b");
    assert_eq!(t.position.messages, start.messages + 2);
    t.bytes(1);
    assert_eq!(t.round_count_for_test(), 2);
    let kinds: Vec<_> = t
        .trace
        .events
        .iter()
        .map(|e| match e {
            Event::Message(m) => m.tag,
            Event::Boundary => 0,
            Event::Draws(_, n) => 1000 + n,
            Event::Seal => 1,
        })
        .collect();
    assert_eq!(kinds, [17, 0, 1002, 32, 32, 0, 1001]);
}

#[test]
fn sealed_and_verified_proofs_record_their_round_count() {
    let run = |t: &mut Transcript| {
        t.bytes(32);
        t.bytes(32);
        t.send_for_test(b"message");
        t.bytes(32);
    };
    let mut prover = Transcript::for_test(b"round count");
    run(&mut prover);
    let encoded = prover.append_final_seal(vec![1, 2, 3]);
    assert_eq!(encoded.round_count_for_test(), 2);
    let mut verifier = Transcript::for_test(b"round count");
    run(&mut verifier);
    let verified = verifier.verify_final_seal(encoded.as_bytes()).unwrap();
    assert_eq!(verified.round_count_for_test(), 2);
    assert_eq!(encoded.trace_for_test(), verified.trace_for_test());
}

#[test]
fn field_rejection_keeps_one_round_and_preserves_the_prf_cursor() {
    use crate::{
        core::algebra::SupportsU64Conversions,
        runtime::algebra::{fp_generic::FpGenericField, limb::LIMBS_PER_U64},
    };
    let f = FpGenericField::<1, { LIMBS_PER_U64 }, { 3 * LIMBS_PER_U64 }, ()>::new_generic([17]);
    for seed in 0u8..64 {
        let mut actual = Transcript::for_test(&[seed]);
        let mut reference = actual.fork_for_test();
        let (expected, tail, attempts) = reference.draw(|r| {
            let mut attempts = 0;
            let expected = loop {
                attempts += 1;
                let x = r.bytes(1)[0] & 31;
                if x < 17 {
                    break f.u64_to_element(x as u64);
                }
            };
            let tail = r.bytes(32);
            (expected, tail, attempts)
        });
        if attempts > 1 {
            let (value, remaining) = actual.draw(|r| {
                let value = r.elt_field(&f);
                let actual_tail = r.bytes(32);
                (value, actual_tail)
            });
            assert_eq!(value, expected);
            assert_eq!(remaining, tail);
            assert_eq!(actual.round_count_for_test(), 1);
            return;
        }
    }
    panic!("fixed test seeds must include a rejected field sample");
}
#[test]
fn power_of_two_indices_consume_only_the_required_bytes() {
    for bits in 0..usize::BITS {
        let n = 1usize << bits;
        let mut actual = Transcript::for_test(b"index bytes");
        let mut reference = actual.fork_for_test();
        let (expected, tail) = reference.draw(|r| {
            let values: Vec<_> = (0..32)
                .map(|_| {
                    let mut bytes = [0; size_of::<usize>()];
                    let len = bits.div_ceil(8) as usize;
                    bytes[..len].copy_from_slice(&r.bytes(len));
                    usize::from_le_bytes(bytes) & (n - 1)
                })
                .collect();
            let tail = r.bytes(32);
            (values, tail)
        });
        let sampled = actual.draw(|r| {
            let values: Vec<_> = (0..32).map(|_| r.nat(n)).collect();
            let remaining = r.bytes(32);
            (values, remaining)
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
        let mut actual = Transcript::for_test(b"index rejection");
        let mut reference = actual.fork_for_test();
        let (expected, tail, rejected) = reference.draw(|r| {
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
            (values, tail, rejected)
        });
        saw_rejection |= rejected;
        let sampled = actual.draw(|r| {
            let values: Vec<_> = (0..64).map(|_| r.nat(n)).collect();
            let actual_tail = r.bytes(32);
            (values, actual_tail)
        });
        assert_eq!(sampled, (expected, tail), "bound {n}");
    }
    assert!(saw_rejection);
}

/// P-256 arithmetic advertised with a wider encoding: the element's 32 bytes
/// fill the end of the buffer, after `bytes - 32` zeros.
struct WideEncoding {
    field: P256Field,
    bytes: usize,
}
impl BareField for WideEncoding {
    type E = <P256Field as BareField>::E;
}
impl SerializableField for WideEncoding {
    fn is_binary(&self) -> bool {
        false
    }
    fn serialized_size_bytes(&self) -> usize {
        self.bytes
    }
    fn to_bytes_into(&self, e: &Self::E, dst: &mut [u8]) {
        assert_eq!(dst.len(), self.bytes);
        dst.fill(0);
        let tail = dst.len() - 32;
        self.field.to_bytes_into(e, &mut dst[tail..]);
    }
    fn bytes_to_element(&self, _: &[u8]) -> Result<Self::E, String> {
        unreachable!("absorption never decodes")
    }
    fn serialized_mone(&self) -> Vec<u8> {
        unreachable!("absorption never encodes constants")
    }
    fn field_id(&self) -> FieldID {
        FieldID::None
    }
}

#[test]
fn absorption_accepts_encodings_wider_than_the_stack_buffer() {
    let base = P256Field::new();
    for bytes in [32, STAGE_BYTES, STAGE_BYTES + 1, 4 * STAGE_BYTES] {
        let f = WideEncoding {
            field: P256Field::new(),
            bytes,
        };
        let challenge = |e: &<WideEncoding as BareField>::E| {
            let mut t = Transcript::for_test(b"wide field");
            t.borrow().send(&Wide(&f, e));
            t.u128()
        };
        // The element's bytes sit at the end, so differing elements show that
        // the whole encoding is absorbed, not just a stack-sized prefix.
        assert_ne!(
            challenge(&base.one()),
            challenge(&base.u64_to_element(2)),
            "width {bytes}"
        );
    }
}
/// One element of a wide test encoding.
struct Wide<'a>(&'a WideEncoding, &'a <WideEncoding as BareField>::E);
impl Message for Wide<'_> {
    const TAG: Tag = Tag::PublicInputs;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.0, std::slice::from_ref(self.1));
    }
}
impl ProverMessage for Wide<'_> {}
/// The encoder's staging buffer size.
const STAGE_BYTES: usize = 512;
impl Transcript {
    /// The bytes the current node has hashed so far, its header included.
    pub(crate) fn preimage_for_test(&self) -> &[u8] {
        &self.strand.preimage
    }
}
