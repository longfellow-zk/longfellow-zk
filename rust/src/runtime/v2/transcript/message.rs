// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The one transcript encoding (transcript I5, I6).
//!
//! A message is a u64 tag from the registry followed by a fixed list of
//! values. Every value is a vector with its length, of one of four kinds:
//!
//! ```text
//! ; every integer is u64 little endian
//! value := 0  count byte{count}            ; Bytes
//!        | 1  count u64{count}             ; Nats
//!        | 2  field count elem{count}      ; Elements: FieldID, canonical serializations
//!        | 3  count byte{ceil(count/8)}    ; Bits: least significant first, zero padding
//! ```
//!
//! There is no scalar kind and no raw write: `Encoder` is the only writer.
//! Setup messages (`SetupMessage`) can be written only by a `Statement`
//! (`session.rs`), through the `Header` that exists only while
//! `Transcript::new` runs (transcript I1, I3); every other message is a
//! `ProverMessage`.
use super::strand::Strand;
#[cfg(test)]
use crate::core::algebra::FieldID;
use crate::{core::algebra::RegisteredField, runtime::v2::proto::tags::Tag};

/// Value kinds of the byte grammar.
const BYTES: u64 = 0;
const NATS: u64 = 1;
const ELEMENTS: u64 = 2;
const BITS: u64 = 3;

/// The registered fields: each FieldID an Elements value may carry, with the
/// width of its canonical serialization and its name. With this table and
/// the tag registry a reader parses every node. `RegisteredField` is
/// implemented exactly for these fields.
#[cfg(test)]
pub(crate) const REGISTERED_FIELDS: [(FieldID, usize, &str); 2] = [
    (FieldID::P256, 32, "P256"),
    (FieldID::Gf2_128, 16, "GF2_128"),
];

/// Serialized values are staged through a stack buffer of this many bytes,
/// so a long vector costs few strand writes. A wider field element uses a
/// heap buffer, so encoding accepts every field.
const STAGE_BYTES: usize = 512;

/// A transcript message: a tag with a fixed schema, and its values. The
/// schema of each tag is documented next to it in `proto::tags` and next to
/// each implementation.
pub trait Message {
    const TAG: Tag;
    /// Write the values, in schema order. Each call to the encoder writes
    /// exactly one value.
    fn encode(&self, e: &mut Encoder<'_>);
}
/// A message the prover sends after the statement. Each is absorbed exactly
/// once, where it is sent (transcript I4).
pub trait ProverMessage: Message {}
/// A statement message: identity, geometry or public inputs. Only a
/// `Statement` writes them, before any prover message (transcript I1, I3).
pub trait SetupMessage: Message {}

/// Test-only record of one message: its value kinds and counts, and its
/// payload without headers (tag, kind, field ID, count).
#[cfg(test)]
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Recorded {
    pub(crate) tag: u64,
    pub(crate) schema: Vec<(u64, u64)>,
    pub(crate) payload: Vec<u8>,
}

/// The only way to write a message's values (transcript I5).
pub struct Encoder<'a> {
    strand: &'a mut Strand,
    #[cfg(test)]
    record: &'a mut Recorded,
}
impl<'a> Encoder<'a> {
    #[cfg(not(test))]
    pub(super) fn new(strand: &'a mut Strand) -> Self {
        Self { strand }
    }
    #[cfg(test)]
    pub(super) fn new(strand: &'a mut Strand, record: &'a mut Recorded) -> Self {
        Self { strand, record }
    }
    fn header(&mut self, kind: u64, count: usize) {
        self.strand.write(&kind.to_le_bytes());
        self.strand.write(&(count as u64).to_le_bytes());
        #[cfg(test)]
        self.record.schema.push((kind, count as u64));
    }
    fn payload(&mut self, bytes: &[u8]) {
        self.strand.write(bytes);
        #[cfg(test)]
        self.record.payload.extend_from_slice(bytes);
    }
    /// A byte string.
    pub fn bytes(&mut self, b: &[u8]) {
        self.header(BYTES, b.len());
        self.payload(b);
    }
    /// A vector of integers, each u64 little endian.
    pub fn nats(&mut self, xs: &[u64]) {
        self.header(NATS, xs.len());
        let mut stage = [0u8; STAGE_BYTES];
        for chunk in xs.chunks(STAGE_BYTES / 8) {
            for (out, x) in stage.as_chunks_mut::<8>().0.iter_mut().zip(chunk) {
                *out = x.to_le_bytes();
            }
            self.payload(&stage[..8 * chunk.len()]);
        }
    }
    /// A vector of elements of `f`, after `f`'s FieldID. Only a registered
    /// field qualifies, so the ID identifies the field and its encoding.
    pub fn elements<F: RegisteredField>(&mut self, f: &F, xs: &[F::E]) {
        self.strand.write(&ELEMENTS.to_le_bytes());
        self.strand.write(&(f.field_id() as u64).to_le_bytes());
        self.strand.write(&(xs.len() as u64).to_le_bytes());
        #[cfg(test)]
        self.record.schema.push((ELEMENTS, xs.len() as u64));
        let n = f.serialized_size_bytes();
        if n == 0 || n > STAGE_BYTES {
            let mut buf = vec![0u8; n];
            for x in xs {
                f.to_bytes_into(x, &mut buf);
                self.payload(&buf);
            }
            return;
        }
        let mut stage = [0u8; STAGE_BYTES];
        for chunk in xs.chunks(STAGE_BYTES / n) {
            for (out, x) in stage.chunks_exact_mut(n).zip(chunk) {
                f.to_bytes_into(x, out);
            }
            self.payload(&stage[..n * chunk.len()]);
        }
    }
    /// A vector of bits, packed least significant first with zero padding.
    pub fn bits(&mut self, bits: impl ExactSizeIterator<Item = bool>) {
        self.header(BITS, bits.len());
        let mut stage = [0u8; STAGE_BYTES];
        // Bytes staged so far; the last one may be partial.
        let mut filled = 0;
        for (j, bit) in bits.enumerate() {
            if j % 8 == 0 {
                if filled == STAGE_BYTES {
                    self.payload(&stage);
                    filled = 0;
                }
                stage[filled] = 0;
                filled += 1;
            }
            stage[filled - 1] |= u8::from(bit) << (j % 8);
        }
        self.payload(&stage[..filled]);
    }
}

/// The protocol ID of `ZkStatement`.
pub const ZK_PROTOCOL_ID: &[u8] = b"longfellow/v2/zk/transcript/v2";

/// The identity message of a standalone statement: Bytes protocol ID
/// (`ZK_PROTOCOL_ID`), Bytes context. Alone it is the whole statement of a
/// bare transcript (tests, tools), which has no Polygero profile; a
/// standalone ZK proof follows it with its circuit and geometry messages,
/// whose `JointGeometry` holds the profile, and its public inputs.
pub struct ZkStatement<'a> {
    pub context: &'a [u8],
}
impl Message for ZkStatement<'_> {
    const TAG: Tag = Tag::ZkStatement;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bytes(ZK_PROTOCOL_ID);
        e.bytes(self.context);
    }
}
impl SetupMessage for ZkStatement<'_> {}

/// The last message of every proof: Bytes, every proof byte before the
/// seal block, the magic included (transcript I10).
pub(super) struct Seal<'a>(pub(super) &'a [u8]);
impl Message for Seal<'_> {
    const TAG: Tag = Tag::Seal;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bytes(self.0);
    }
}
