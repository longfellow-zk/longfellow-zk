// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! A test decoder of the statement (transcript I1, I3).
//!
//! It reads the statement messages back from the bytes a transcript hashed,
//! with the byte grammar and the tag registry alone: no geometry, circuit or
//! layout object. The round-trip tests rebuild every value the verifier uses
//! from what it returns and compare the result with the verifier's own
//! values, so a value the verifier relies on that the statement does not
//! carry makes them fail.
use std::ops::Range;

use crate::runtime::v2::{
    proto::{
        polygero::PolygeroConfig,
        tags::{Kind, Tag},
    },
    transcript::{Trace, REGISTERED_FIELDS},
};

/// One value of a message, as the grammar writes it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Value {
    Bytes(Vec<u8>),
    Nats(Vec<u64>),
    /// The FieldID, then each element's canonical serialization.
    Elements(u64, Vec<Vec<u8>>),
    /// The bit count, then the bits packed least significant first.
    Bits(u64, Vec<u8>),
}

/// One decoded message and the bytes it occupies in its node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Decoded {
    pub(crate) tag: Tag,
    pub(crate) values: Vec<Value>,
    pub(crate) span: Range<usize>,
}

/// A decoded strand node: its header, its messages and its terminator, if
/// the bytes reach it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Node {
    pub(crate) id: u64,
    pub(crate) parent: Option<[u8; 32]>,
    pub(crate) messages: Vec<Decoded>,
    pub(crate) end: Option<u64>,
}

/// The width of a registered field's canonical serialization.
pub(crate) fn field_width(field: u64) -> usize {
    REGISTERED_FIELDS
        .iter()
        .find(|(id, ..)| *id as u64 == field)
        .unwrap_or_else(|| panic!("field {field} is not registered"))
        .1
}

struct Cursor<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Cursor<'a> {
    fn take(&mut self, n: usize) -> &'a [u8] {
        let end = self.at.checked_add(n).expect("length overflow");
        assert!(end <= self.bytes.len(), "value runs past the node");
        let s = &self.bytes[self.at..end];
        self.at = end;
        s
    }
    fn u32(&mut self) -> u32 {
        u32::from_le_bytes(self.take(4).try_into().unwrap())
    }
    fn u64(&mut self) -> u64 {
        u64::from_le_bytes(self.take(8).try_into().unwrap())
    }
    fn count(&mut self) -> usize {
        usize::try_from(self.u64()).unwrap()
    }
}

/// Decode a node's SHA-256 preimage, or a prefix of it that ends between
/// messages (the statement of a session that has not drawn yet). Every
/// value must have its tag's kind and fixed count, every field must be
/// registered, padding bits must be zero, and a terminator ends the node
/// exactly.
pub(crate) fn decode_node(node: &[u8]) -> Node {
    let mut c = Cursor { bytes: node, at: 0 };
    assert_eq!(c.u32(), 1, "node type is STRAND");
    let id = c.u64();
    let parent = match c.u32() {
        0 => None,
        1 => Some(c.take(32).try_into().unwrap()),
        n => panic!("{n} parents"),
    };
    assert_eq!(parent.is_none(), id == 0, "only the root has no parent");
    let mut messages = Vec::new();
    let mut end = None;
    while c.at < node.len() {
        let start = c.at;
        let word = c.u64();
        if word < 16 {
            assert!(word <= 1, "reserved terminator {word}");
            end = Some(word);
            break;
        }
        let tag = Tag::from_value(word).unwrap_or_else(|| panic!("tag {word} is not registered"));
        let mut values = Vec::new();
        for (i, &(kind, fixed)) in tag.schema().iter().enumerate() {
            assert_eq!(c.u64(), kind.value(), "{tag:?} value {i} kind");
            let value = match kind {
                Kind::Bytes => {
                    let n = c.count();
                    Value::Bytes(c.take(n).to_vec())
                }
                Kind::Nats => {
                    let n = c.count();
                    Value::Nats((0..n).map(|_| c.u64()).collect())
                }
                Kind::Elements => {
                    let field = c.u64();
                    let width = field_width(field);
                    let n = c.count();
                    Value::Elements(field, (0..n).map(|_| c.take(width).to_vec()).collect())
                }
                Kind::Bits => {
                    let n = c.u64();
                    let packed = c.take(usize::try_from(n.div_ceil(8)).unwrap()).to_vec();
                    if !n.is_multiple_of(8) {
                        assert_eq!(packed.last().unwrap() >> (n % 8), 0, "padding bits");
                    }
                    Value::Bits(n, packed)
                }
            };
            let count = match &value {
                Value::Bytes(b) => b.len() as u64,
                Value::Nats(xs) => xs.len() as u64,
                Value::Elements(_, xs) => xs.len() as u64,
                Value::Bits(n, _) => *n,
            };
            assert!(
                fixed.is_none_or(|n| n == count),
                "{tag:?} value {i} count {count}"
            );
            values.push(value);
        }
        messages.push(Decoded {
            tag,
            values,
            span: start..c.at,
        });
    }
    if end.is_some() {
        assert_eq!(c.at, node.len(), "the terminator ends the node");
    }
    Node {
        id,
        parent,
        messages,
        end,
    }
}

/// The identity message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Identity {
    Mdoc {
        protocol: Vec<u8>,
        session: Vec<u8>,
        combined_hash: [u8; 32],
        version: u64,
        attributes: u64,
    },
    Zk {
        protocol: Vec<u8>,
        context: Vec<u8>,
    },
}

/// A `CommitmentLayout` message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Layout {
    pub(crate) field: u64,
    pub(crate) private: u64,
    pub(crate) pads: u64,
    pub(crate) masks: u64,
    pub(crate) descriptor: Vec<u8>,
    /// `(first value, count, first cell)` triples.
    pub(crate) native: Vec<[u64; 3]>,
    /// `(first value, count, first bit, bits per value)` quadruples.
    pub(crate) stored: Vec<[u64; 4]>,
    /// The split mask R's bits: (start, width).
    pub(crate) mask: [u64; 2],
}

/// The packing descriptor, split into its parts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Descriptor {
    pub(crate) packing: Vec<u8>,
    pub(crate) embedding: Vec<u8>,
    pub(crate) degree: u64,
    pub(crate) basis: Vec<Vec<u8>>,
}

impl Layout {
    /// The descriptor's parts: the domain separator, three length-prefixed
    /// parts (field packing ID, embedding ID, u64 degree), then the basis,
    /// `degree` elements of the layout's field.
    pub(crate) fn descriptor(&self) -> Descriptor {
        const PREFIX: &[u8] = b"longfellow/packing-extension/v1";
        let mut c = Cursor {
            bytes: &self.descriptor,
            at: 0,
        };
        assert_eq!(c.take(PREFIX.len()), PREFIX, "descriptor prefix");
        let mut part = || {
            let n = c.count();
            c.take(n).to_vec()
        };
        let (packing, embedding, degree_bytes) = (part(), part(), part());
        let degree = u64::from_le_bytes(degree_bytes.try_into().expect("u64 degree"));
        let width = field_width(self.field);
        let basis = (0..degree).map(|_| c.take(width).to_vec()).collect();
        assert_eq!(c.at, self.descriptor.len(), "descriptor consumed exactly");
        Descriptor {
            packing,
            embedding,
            degree,
            basis,
        }
    }
    /// The native cells the runs cover.
    pub(crate) fn native_cells(&self) -> u64 {
        self.native.iter().map(|r| r[1]).sum()
    }
    /// The values the runs cover: private inputs and pads.
    pub(crate) fn values(&self) -> u64 {
        self.native_cells() + self.stored.iter().map(|r| r[1]).sum::<u64>()
    }
}

/// An `AdapterLayout` message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Adapter {
    pub(crate) mode: Vec<u8>,
    pub(crate) q: u64,
    pub(crate) trees: u64,
    pub(crate) leaves: u64,
    /// (start, width) of each quotient pad.
    pub(crate) pads: Vec<[u64; 2]>,
}

/// A `PublicInputs` message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Public {
    pub(crate) field: u64,
    pub(crate) elements: Vec<Vec<u8>>,
}

/// A statement as the transcript absorbed it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Statement {
    pub(crate) identity: Identity,
    pub(crate) circuits: Vec<[u8; 32]>,
    pub(crate) layouts: Vec<Layout>,
    pub(crate) adapters: Vec<Adapter>,
    /// (k, s, n, t).
    pub(crate) joint: [u64; 4],
    pub(crate) public: Vec<Public>,
}

fn bytes(v: &Value) -> &[u8] {
    match v {
        Value::Bytes(b) => b,
        _ => panic!("not Bytes: {v:?}"),
    }
}
fn nats(v: &Value) -> &[u64] {
    match v {
        Value::Nats(xs) => xs,
        _ => panic!("not Nats: {v:?}"),
    }
}
fn tuples<const N: usize>(v: &Value) -> Vec<[u64; N]> {
    let (chunks, rest) = nats(v).as_chunks::<N>();
    assert!(rest.is_empty(), "a run list of {N}-tuples");
    chunks.to_vec()
}

impl Statement {
    /// Decode the statement from the first messages of `messages`, in the
    /// one fixed order: the identity, one or more `Circuit`, one or more
    /// `CommitmentLayout`, any `AdapterLayout`, one `JointGeometry`, one or
    /// more `PublicInputs`. Returns the statement and how many messages it
    /// spans.
    pub(crate) fn decode(messages: &[Decoded]) -> (Self, usize) {
        let mut it = messages.iter().peekable();
        let first = it.next().expect("an identity message");
        let identity = match first.tag {
            Tag::MdocStatement => {
                let v = &first.values;
                let n = nats(&v[3]);
                Identity::Mdoc {
                    protocol: bytes(&v[0]).to_vec(),
                    session: bytes(&v[1]).to_vec(),
                    combined_hash: bytes(&v[2]).try_into().unwrap(),
                    version: n[0],
                    attributes: n[1],
                }
            }
            Tag::ZkStatement => Identity::Zk {
                protocol: bytes(&first.values[0]).to_vec(),
                context: bytes(&first.values[1]).to_vec(),
            },
            tag => panic!("the statement opens with {tag:?}"),
        };
        let mut take = |tag: Tag| {
            let mut out = Vec::new();
            while let Some(m) = it.next_if(|m| m.tag == tag) {
                out.push(m.values.clone());
            }
            out
        };
        let circuits: Vec<[u8; 32]> = take(Tag::Circuit)
            .iter()
            .map(|v| bytes(&v[0]).try_into().unwrap())
            .collect();
        let layouts: Vec<Layout> = take(Tag::CommitmentLayout)
            .iter()
            .map(|v| {
                let head = nats(&v[0]);
                let mask = nats(&v[4]);
                Layout {
                    field: head[0],
                    private: head[1],
                    pads: head[2],
                    masks: head[3],
                    descriptor: bytes(&v[1]).to_vec(),
                    native: tuples::<3>(&v[2]),
                    stored: tuples::<4>(&v[3]),
                    mask: [mask[0], mask[1]],
                }
            })
            .collect();
        let adapters: Vec<Adapter> = take(Tag::AdapterLayout)
            .iter()
            .map(|v| {
                let shape = nats(&v[1]);
                Adapter {
                    mode: bytes(&v[0]).to_vec(),
                    q: shape[0],
                    trees: shape[1],
                    leaves: shape[2],
                    pads: tuples::<2>(&v[2]),
                }
            })
            .collect();
        let joints = take(Tag::JointGeometry);
        assert_eq!(joints.len(), 1, "one JointGeometry");
        let joint: [u64; 4] = nats(&joints[0][0]).try_into().unwrap();
        let public: Vec<Public> = take(Tag::PublicInputs)
            .iter()
            .map(|v| match &v[0] {
                Value::Elements(field, elements) => Public {
                    field: *field,
                    elements: elements.clone(),
                },
                other => panic!("not Elements: {other:?}"),
            })
            .collect();
        assert!(!circuits.is_empty() && !layouts.is_empty() && !public.is_empty());
        assert_eq!(
            layouts.len(),
            public.len(),
            "one layout and one input vector per field"
        );
        let spanned = messages.len() - it.count();
        (
            Self {
                identity,
                circuits,
                layouts,
                adapters,
                joint,
                public,
            },
            spanned,
        )
    }

    /// Decode the statement from the bytes a session's first node holds
    /// right after it opened: the node header, then exactly the statement.
    pub(crate) fn from_statement_bytes(bytes: &[u8]) -> Self {
        let node = decode_node(bytes);
        assert_eq!((node.id, node.end), (0, None), "an open root node");
        let (statement, spanned) = Self::decode(&node.messages);
        assert_eq!(spanned, node.messages.len(), "only statement messages");
        statement
    }

    /// The Polygero profile of `JointGeometry`.
    pub(crate) fn config(&self) -> PolygeroConfig {
        let [k, s, n, t] = self.joint.map(|x| usize::try_from(x).unwrap());
        PolygeroConfig { k, s, n, t }
    }

    /// Decode the statement a complete transcript opened with, from its first
    /// node's bytes. The statement must be followed in that node by a
    /// prover message, and no statement tag may occur anywhere after it in
    /// the trace (transcript I1).
    pub(crate) fn from_trace(trace: &Trace) -> Self {
        let node = decode_node(&trace.nodes[0]);
        let (statement, spanned) = Self::decode(&node.messages);
        assert!(
            spanned < node.messages.len(),
            "a prover message ends the first node"
        );
        let setup = |tag: u64| (16..32).contains(&tag);
        assert!(!setup(node.messages[spanned].tag.value()));
        assert_eq!(
            trace.messages().filter(|m| setup(m.tag)).count(),
            spanned,
            "statement messages only at the start"
        );
        statement
    }
}
