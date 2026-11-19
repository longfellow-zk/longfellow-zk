// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::algebra::{
        AlgebraicField, BareField, FieldID, RegisteredField, Sealed, SerializableField,
        SupportsU64Conversions,
    },
    runtime::{
        algebra::p256::P256Field,
        v2::{
            proto::tags::Tag,
            transcript::{
                message::ZkStatement, Encoder, Event, Message, ProverMessage, TestMessage,
                REGISTERED_FIELDS,
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
            session: SessionStamp::fresh(),
            stream: self.stream.as_ref().map(Reader::clone_for_test),
            trace: self.trace.clone(),
        }
    }
    pub(crate) fn round_count_for_test(&self) -> u64 {
        self.trace.boundaries()
    }
    /// Where the session stands: its boundary count and its message count.
    fn position(&self) -> (u64, usize) {
        let messages = self
            .trace
            .events
            .iter()
            .filter(|e| matches!(e, Event::Message(_)))
            .count();
        (self.round_count_for_test(), messages)
    }
    /// This session's identity, for test systems derived on it.
    pub(crate) fn session_for_test(&self) -> SessionStamp {
        self.session()
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

/// The root node of `Transcript::for_test(b"vector")` with one test message
/// and the ROUND terminator, built by hand from the byte grammar.
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
    let mut t = Transcript::new(&ZkStatement { context: b"vector" });
    t.send_for_test(b"message");
    let mut bytes = t.bytes(3);
    bytes.extend(t.bytes(157));
    assert_eq!(t.trace.nodes, [vector_root()]);
    assert_eq!(
        hex::encode(&bytes),
        concat!(
            "36a420811a898f44127afeeaf36abc10030b132315e76a61100442f0ab5ae579",
            "8bcf7193e9a64cc665ebcebc91d3df4dff8303497d2e30b3c821d803c86d7cff",
            "7d24b0661d1f3fb1b98286d69cba7447d153f88c3da9b7758dd0925d186ad80d",
            "5e4a81bae077e37cc107f00d88ca2ffc0717bd5a57ac7a129093697d0af4c034",
            "08d4ca0c98f81fb0f4d76335dcefdb27735d3544bf8825f6f41798397b8a4790"
        )
    );
    let sealed = t.append_final_seal(vec![1, 2, 3]).into_bytes();
    assert_eq!(
        hex::encode(&sealed[3..]),
        "0a3dee3652ae0c7401b80478db87ec4a8d25256d59e4aaab0822a27e478297e2"
    );
}

/// A statement: the identity, then `geometry` messages.
struct Opening<'a> {
    identity: ZkStatement<'a>,
    geometry: usize,
}
struct Geometry;
impl Message for Geometry {
    const TAG: Tag = Tag::JointGeometry;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.nats(&[8, 2, 64, 2]);
    }
}
impl SetupMessage for Geometry {}
impl<'a> Statement for Opening<'a> {
    type Identity = ZkStatement<'a>;
    fn identity(&self) -> &ZkStatement<'a> {
        &self.identity
    }
    fn write(&self, h: &mut Header<'_>) {
        for _ in 0..self.geometry {
            h.send(&Geometry);
        }
    }
}

/// The transcript writes a statement's identity before its other
/// messages, so the root node starts with it even when the statement
/// writes nothing else (transcript I1).
#[test]
fn a_statement_opens_with_its_identity() {
    for geometry in [0, 2] {
        let t = Transcript::new(&Opening {
            identity: ZkStatement {
                context: b"opening",
            },
            geometry,
        });
        let tags: Vec<u64> = t.trace.messages().map(|m| m.tag).collect();
        let mut expected = vec![17];
        expected.resize(1 + geometry, 20);
        assert_eq!(tags, expected);
    }
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
    let trace = &proof.trace;
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

/// A panic in a draw's closure keeps the stream: the next draw continues
/// after the bytes the closure read, at the same boundary, as if the
/// closure had returned.
#[test]
fn a_caught_panic_in_a_draw_keeps_the_stream() {
    for read in [0, 5] {
        let mut panicked = Transcript::for_test(b"panic");
        let mut control = Transcript::for_test(b"panic");
        assert_eq!(panicked.bytes(5), control.bytes(5));
        let before = panicked.position();
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            panicked.draw::<()>(|r| {
                r.bytes(read);
                panic!("draw callback")
            })
        }));
        assert!(caught.is_err());
        assert!(panicked.position() == before);
        control.bytes(read);
        assert_eq!(panicked.bytes(16), control.bytes(16));
        assert!(panicked.position() == control.position());
        assert_eq!(panicked.round_count_for_test(), 1);
    }
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

/// Each registered field has the ID and width the registry lists, which is
/// all a reader needs to parse its Elements (transcript I5).
#[test]
fn registered_fields_have_the_registry_id_and_width() {
    use crate::runtime::algebra::gf2_128::Gf2_128Field;
    fn entry<F: RegisteredField>(f: &F) -> (FieldID, usize) {
        assert_eq!(f.field_id(), F::ID);
        assert_eq!(f.serialized_size_bytes(), F::BYTES);
        assert_eq!(f.serialized_mone().len(), F::BYTES);
        (F::ID, F::BYTES)
    }
    let fields = [entry(&P256Field::new()), entry(&Gf2_128Field::new())];
    let registry: Vec<_> = REGISTERED_FIELDS
        .iter()
        .map(|&(id, w, _)| (id, w))
        .collect();
    assert_eq!(registry, fields);
    assert!(fields.iter().all(|(id, _)| *id != FieldID::None));
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
    assert_eq!(t.position().1, start.1 + 2);
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
    assert_eq!(encoded.trace, verified.trace);
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
/// `nonzero` and `elements` read exactly what repeated `elt_field` reads,
/// and `choose` is Fisher-Yates in the caller's scratch, whatever the
/// scratch held.
#[test]
fn draw_kinds_match_their_element_and_index_definitions() {
    use crate::runtime::algebra::{fp_generic::FpGenericField, limb::LIMBS_PER_U64};
    let f = FpGenericField::<1, { LIMBS_PER_U64 }, { 3 * LIMBS_PER_U64 }, ()>::new_generic([3]);
    let mut actual = Transcript::for_test(b"draw kinds");
    let mut reference = actual.fork_for_test();
    let drawn = actual.draw(|r| {
        let nonzero: Vec<_> = (0..16).map(|_| r.nonzero(&f)).collect();
        let elements: Vec<_> = r.elements(&f, 16).collect();
        let mut indices = [0; 5];
        let mut scratch = [usize::MAX; 12];
        r.choose(&mut indices, 9, &mut scratch);
        (nonzero, elements, indices)
    });
    let expected = reference.draw(|r| {
        let nonzero: Vec<_> = (0..16)
            .map(|_| loop {
                let x = r.elt_field(&f);
                if !f.is_zero(&x) {
                    break x;
                }
            })
            .collect();
        let elements: Vec<_> = (0..16).map(|_| r.elt_field(&f)).collect();
        let mut a: Vec<usize> = (0..9).collect();
        let mut indices = [0; 5];
        for (i, out) in indices.iter_mut().enumerate() {
            a.swap(i, i + r.nat(9 - i));
            *out = a[i];
        }
        (nonzero, elements, indices)
    });
    assert_eq!(drawn, expected);
    assert!(expected.0.iter().all(|x| !f.is_zero(x)));
    let mut distinct = expected.2.to_vec();
    distinct.sort();
    distinct.dedup();
    assert_eq!(distinct.len(), 5);
    assert_eq!(actual.bytes(32), reference.bytes(32));
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

/// P-256 arithmetic advertised with a `BYTES`-wide encoding: the element's
/// 32 bytes fill the end of the buffer, after `BYTES - 32` zeros.
struct WideEncoding<const BYTES: usize> {
    field: P256Field,
}
impl<const BYTES: usize> BareField for WideEncoding<BYTES> {
    type E = <P256Field as BareField>::E;
}
impl<const BYTES: usize> Sealed for WideEncoding<BYTES> {}
/// Test-only: encodings of other widths under `FieldID::None`.
impl<const BYTES: usize> RegisteredField for WideEncoding<BYTES> {
    const ID: FieldID = FieldID::None;
    const BYTES: usize = BYTES;
}
impl<const BYTES: usize> SerializableField for WideEncoding<BYTES> {
    fn is_binary(&self) -> bool {
        false
    }
    fn serialized_size_bytes(&self) -> usize {
        BYTES
    }
    fn to_bytes_into(&self, e: &Self::E, dst: &mut [u8]) {
        assert_eq!(dst.len(), BYTES);
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

/// Every element is absorbed whole, in order, across the stage buffer's
/// chunks: widths that divide the buffer and widths that do not, up to the
/// whole buffer, with vectors longer than one chunk.
#[test]
fn absorption_stages_every_element_whole() {
    fn check<const BYTES: usize>() {
        let f = WideEncoding::<BYTES> {
            field: P256Field::new(),
        };
        let count = 2 * STAGE_BYTES / BYTES + 1;
        let xs: Vec<_> = (1..=count as u64)
            .map(|i| f.field.u64_to_element(i))
            .collect();
        let mut t = Transcript::for_test(b"wide field");
        t.borrow().send(&Wide(&f, &xs));
        let recorded = t.trace.messages().last().unwrap().clone();
        assert_eq!(recorded.schema, [(2, count as u64)], "width {BYTES}");
        let expected: Vec<u8> = xs.iter().flat_map(|x| f.to_bytes(x)).collect();
        assert_eq!(recorded.payload, expected, "width {BYTES}");
    }
    check::<32>();
    check::<48>();
    check::<{ STAGE_BYTES / 2 }>();
    check::<{ STAGE_BYTES - 1 }>();
    check::<STAGE_BYTES>();
}
/// A vector of a wide test encoding.
struct Wide<'a, const BYTES: usize>(
    &'a WideEncoding<BYTES>,
    &'a [<WideEncoding<BYTES> as BareField>::E],
);
impl<const BYTES: usize> Message for Wide<'_, BYTES> {
    const TAG: Tag = Tag::PublicInputs;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.0, self.1);
    }
}
impl<const BYTES: usize> ProverMessage for Wide<'_, BYTES> {}
/// The encoder's staging buffer size.
const STAGE_BYTES: usize = 512;
impl Transcript {
    /// The bytes the current node has hashed so far, its header included.
    pub(crate) fn preimage_for_test(&self) -> &[u8] {
        &self.strand.preimage
    }
}

/// A nonzero draw is traced as its own kind, so a role that draws a plain
/// element where the other draws a nonzero one has another trace even when
/// both read the same nonzero value; index draws record their values
/// (transcript I9).
#[test]
fn nonzero_draws_and_index_values_are_traced() {
    use super::super::trace::Draw;
    let f = P256Field::new();
    let mut plain = Transcript::for_test(b"draw kinds");
    let mut nonzero = Transcript::for_test(b"draw kinds");
    let x = plain.borrow().draw(|r| r.elt_field(&f));
    let y = nonzero.borrow().draw(|r| r.nonzero(&f));
    assert!(x == y && !f.is_zero(&x));
    assert_eq!(
        plain.trace.events.last(),
        Some(&Event::Draws(Draw::Element, 1))
    );
    assert_eq!(
        nonzero.trace.events.last(),
        Some(&Event::Draws(Draw::Nonzero, 1))
    );
    assert_ne!(plain.trace, nonzero.trace);
    let (mut out, mut scratch) = ([0; 3], [0; 10]);
    plain
        .borrow()
        .draw(|r| r.choose(&mut out, 10, &mut scratch));
    assert_eq!(plain.trace.indices, [out.to_vec()]);
}
