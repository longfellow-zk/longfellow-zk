// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0

use crate::{
    circuits::{
        bitvec::{Bitvec, BitvecIO, BitvecLogic, V8},
        boolean::Boolean,
        routing::Routing,
    },
    compile::logic::{Logic, LogicIO},
    mdoc::{
        circuits::{
            cbor_lexer::{self, CborLexer},
            cbor_parser::{self, CborParser, Span},
            mso_attribute::{AttrSlice, FieldLocator},
            MdocHashCompileField,
        },
        proto::{
            hash::constants::{
                K_HASH_INDEX_BITS, K_MSO_MAX_BYTES, K_MSO_OFFSET,
                K_STRUCTURE_ATTR_BITS as ATTR_BITS, K_STRUCTURE_ATTR_CAPACITY as ATTR_CAPACITY,
                K_STRUCTURE_BITS,
            },
            mso_attribute::constants::K_ATTR_PREIMAGE_LEN,
        },
    },
};
type Index<L> = Bitvec<L, K_STRUCTURE_BITS>;

pub struct AttributeWitness<L: Logic> {
    pub lexer: cbor_lexer::Witness<L, ATTR_BITS>,
    pub rank: cbor_parser::RankWitness<L, ATTR_BITS>,
    pub map: cbor_parser::Witness<L, ATTR_BITS>,
}

pub struct Witness<L: Logic> {
    pub lexer: cbor_lexer::Witness<L, K_STRUCTURE_BITS>,
    pub rank: cbor_parser::RankWitness<L, K_STRUCTURE_BITS>,
    /// MSO, validityInfo, valueDigests, namespace digest map.
    pub maps: [cbor_parser::Witness<L, K_STRUCTURE_BITS>; 4],
    /// docType, deviceKeyInfo, validityInfo, valueDigests.
    pub root_values: [Span<L, K_STRUCTURE_BITS>; 4],
    pub validity_key: Index<L>,
    pub namespace: Span<L, K_STRUCTURE_BITS>,
    pub digest_keys: Vec<Index<L>>,
    pub attributes: Vec<AttributeWitness<L>>,
}

impl<L: LogicIO> Witness<L> {
    pub fn allocate(logic: &L, attrs: usize, pos: &mut usize) -> Self {
        let bv = BitvecLogic::new(logic);
        let io = BitvecIO::new(&bv);
        let lexer = cbor_lexer::Witness::allocate(logic, K_MSO_MAX_BYTES, pos);
        let rank = cbor_parser::RankWitness::allocate(logic, K_MSO_MAX_BYTES, pos);
        let maps =
            std::array::from_fn(|_| cbor_parser::Witness::allocate(logic, K_MSO_MAX_BYTES, pos));
        let root_values = std::array::from_fn(|_| Span {
            start: io.next(pos),
            end: io.next(pos),
        });
        let validity_key = io.next(pos);
        let namespace = Span {
            start: io.next(pos),
            end: io.next(pos),
        };
        let digest_keys = (0..attrs).map(|_| io.next(pos)).collect();
        let attributes = (0..attrs)
            .map(|_| AttributeWitness {
                lexer: cbor_lexer::Witness::allocate(logic, ATTR_CAPACITY, pos),
                rank: cbor_parser::RankWitness::allocate(logic, ATTR_CAPACITY, pos),
                map: cbor_parser::Witness::allocate(logic, ATTR_CAPACITY, pos),
            })
            .collect();
        Self {
            lexer,
            rank,
            maps,
            root_values,
            validity_key,
            namespace,
            digest_keys,
            attributes,
        }
    }
}

fn narrow<L: Logic, const FROM: usize, const TO: usize>(
    logic: &L,
    name: &str,
    value: &Bitvec<L, FROM>,
) -> (Bitvec<L, TO>, L::Assertions) {
    const {
        assert!(TO <= FROM && FROM <= 64);
    }
    let bv = BitvecLogic::new(logic);
    let upper = u64::MAX.checked_shl(TO as u32).unwrap_or(0);
    let fits = Boolean::new(logic).assert_true(name, &bv.eqmask(value, 0, upper));
    (bv.from_fn(|i| value[i].clone()), fits)
}

fn relative<L: Logic>(
    logic: &L,
    index: &Bitvec<L, K_HASH_INDEX_BITS>,
) -> (Index<L>, L::Assertions) {
    let bv = BitvecLogic::new(logic);
    let (relative_offset, subtract) = bv.checked_sub(index, &bv.of_u64(K_MSO_OFFSET as u64));
    let (offset, bounds) = narrow(logic, "offset_bits", &relative_offset);
    (
        offset,
        logic.assert_all("relative_index", &[subtract, bounds]),
    )
}

fn uint<L: Logic, const N: usize>(
    logic: &L,
    bytes: &[V8<L>],
    start: &Bitvec<L, N>,
) -> (Bitvec<L, 64>, L::Assertions) {
    let bv = BitvecLogic::new(logic);
    let b = Boolean::new(logic);
    let data = Routing::new(logic).shift_bitvec(3, start, 9, bytes, &bv.of_u8(0));
    let info = bv.from_fn::<5, _>(|i| data[0][i].clone());
    let small = bv.lt(&info, &bv.of_u64(24));
    let extended = bv.eqmask(&info, 24, 28);
    let read = |size: usize| {
        bv.from_fn::<64, _>(|i| {
            if i / 8 < size {
                data[size - i / 8][i % 8].clone()
            } else {
                b.falseb()
            }
        })
    };
    let lower = bv.select(&info[0], &read(2), &read(1));
    let upper = bv.select(&info[0], &read(8), &read(4));
    let wide = bv.select(&info[1], &upper, &lower);
    let value = bv.select(&small, &bv.zext::<5, 64>(&info), &wide);
    let checks = logic.assert_all(
        "unsigned_id",
        &[
            b.assert_true("major", &bv.eqmask(&data[0], 0, 0xe0)),
            b.assert_true("argument", &b.orb(&small, &extended)),
        ],
    );
    (value, checks)
}

/// Attribute wire view needed to bind its map structure and digest identifier.
pub struct AttributeInput<'a, L: Logic> {
    pub digest_offset: &'a Bitvec<L, K_HASH_INDEX_BITS>,
    pub preimage: &'a AttrSlice<L, K_ATTR_PREIMAGE_LEN>,
    pub locator: &'a FieldLocator<L>,
}
/// Borrowed presentation wires; deliberately independent of the hash-circuit model.
pub struct Input<'a, L: Logic> {
    pub preimage: &'a [V8<L>],
    pub len: &'a Bitvec<L, K_HASH_INDEX_BITS>,
    /// docType, deviceKeyInfo, valueDigests, namespace, validFrom, validUntil.
    pub keys: [&'a Bitvec<L, K_HASH_INDEX_BITS>; 6],
    pub attributes: Vec<AttributeInput<'a, L>>,
    pub witness: &'a Witness<L>,
}

pub fn assert_structure<L: LogicIO>(logic: &L, given: &Input<'_, L>) -> L::Assertions
where L::F: MdocHashCompileField {
    let bv = BitvecLogic::new(logic);
    let b = Boolean::new(logic);
    let parser = CborParser::new(logic);
    let routing = Routing::new(logic);
    let w = given.witness;
    let base = K_MSO_OFFSET;
    let raw = &given.preimage[base..base + K_MSO_MAX_BYTES];
    let (raw_len, len_check) = bv.checked_sub(given.len, &bv.of_u64(base as u64));
    let mut checks = vec![
        len_check,
        b.assert_true(
            "mso_capacity",
            &bv.leq(&raw_len, &bv.of_u64(K_MSO_MAX_BYTES as u64)),
        ),
    ];
    let len: Index<L> = bv.from_fn(|i| raw_len[i].clone());
    let stream = CborLexer::new(logic).lex(raw, &len, &w.lexer);
    let parsed = parser.parse(stream, &w.rank);
    let [root_witness, validity_witness, digests_witness, namespace_witness] = &w.maps;
    let [doc_value, device_value, validity_value, digests_value] = &w.root_values;
    let root = parser.root_map(&parsed, root_witness);
    let [doc_key, device_key, digests_key, namespace_key, from_key, until_key] =
        given.keys.map(|k| {
            let (index, check) = relative(logic, k);
            checks.push(check);
            index
        });
    let doc = parser.entry(&root, &doc_key, doc_value);
    let device = parser.entry(&root, &device_key, device_value);
    let validity = parser.entry(&root, &w.validity_key, validity_value);
    let digests = parser.entry(&root, &digests_key, digests_value);
    checks.extend([doc.assertions(), device.assertions()]);
    // These two names need unconditional checks: docType matching may otherwise
    // be suppressed, and validityInfo had no previous byte-occurrence assertion.
    for (key, name) in [
        (&doc_key, b"docType".as_slice()),
        (&w.validity_key, b"validityInfo".as_slice()),
    ] {
        let bytes = routing.shift_bitvec(3, key, name.len() + 1, raw, &bv.of_u8(0));
        checks.push(bv.assert_eq(
            "map_key_header",
            &bytes[0],
            &bv.of_u8(0x60 + name.len() as u8),
        ));
        for (i, byte) in name.iter().enumerate() {
            checks.push(bv.assert_eq("map_key_byte", &bytes[i + 1], &bv.of_u8(*byte)));
        }
    }
    let validity_map = parser.item_map(&validity.value, validity_witness);
    for (key, key_len, total_len) in [(&from_key, 10, 32), (&until_key, 11, 33)] {
        let (start, cs) = bv.checked_add(key, &bv.of_u64(key_len));
        let (end, ce) = bv.checked_add(key, &bv.of_u64(total_len));
        checks.extend([
            cs,
            ce,
            parser
                .entry(&validity_map, key, &Span { start, end })
                .assertions(),
        ]);
    }
    let digests_map = parser.item_map(&digests.value, digests_witness);
    let namespace = parser.entry(&digests_map, &namespace_key, &w.namespace);
    let namespace_map = parser.item_map(&namespace.value, namespace_witness);
    checks.push(namespace_map.assertions());
    for (i, attr) in given.attributes.iter().enumerate() {
        let (value, value_check) = relative(logic, attr.digest_offset);
        let (end, end_check) = bv.checked_add(&value, &bv.of_u64(34));
        let entry = parser.entry(
            &namespace_map,
            &w.digest_keys[i],
            &Span { start: value, end },
        );
        let (digest_id, digest_check) = uint(logic, raw, &w.digest_keys[i]);
        checks.extend([value_check, end_check, entry.assertions(), digest_check]);

        let attr_len: Bitvec<L, ATTR_BITS> = bv.from_fn(|j| attr.preimage.len[j].clone());
        checks.push(b.assert_true(
            "attribute_capacity",
            &bv.leq(&attr.preimage.len, &bv.of_u64(ATTR_CAPACITY as u64)),
        ));
        let attr_stream = CborLexer::new(logic).lex_range(
            &attr.preimage.data,
            &bv.of_u64(4),
            &attr_len,
            &w.attributes[i].lexer,
        );
        let attr_parsed = parser.parse(attr_stream, &w.attributes[i].rank);
        let attr_map = parser.root_map(&attr_parsed, &w.attributes[i].map);
        let mut issuer_id = None;
        for (field, key_length) in [9, 7, 18, 13].into_iter().enumerate() {
            let slot = &attr.locator.permutation[field];
            let key = routing.shift_bitvec(2, slot, 1, &attr.locator.slot_position, &bv.of_u64(0))
                [0]
            .clone();
            let size =
                routing.shift_bitvec(2, slot, 1, &attr.locator.length, &bv.of_u64(0))[0].clone();
            let (field_value, vc) = bv.checked_add(&key, &bv.of_u64(key_length));
            let (field_end, ec) = bv.checked_add(&key, &size);
            let (key8, kc) = narrow::<_, _, ATTR_BITS>(logic, "attribute_offset_bits", &key);
            let (start, sc) = narrow(logic, "attribute_value_bits", &field_value);
            let (attribute_end, attribute_end_check) =
                narrow(logic, "attribute_end_bits", &field_end);
            checks.extend([vc, ec, kc, sc, attribute_end_check]);
            let span = Span {
                start,
                end: attribute_end,
            };
            checks.push(parser.entry(&attr_map, &key8, &span).assertions());
            if field == 0 {
                let (id, check) = uint(logic, &attr.preimage.data, &span.start);
                checks.push(check);
                issuer_id = Some(id);
            }
        }
        checks.push(bv.assert_eq("digest_id_binding", &digest_id, &issuer_id.unwrap()));
    }
    logic.assert_all("mdoc_structure", &checks)
}
