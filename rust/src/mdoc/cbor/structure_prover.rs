// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::mdoc::{
    cbor::{
        lexer_prover::ConcreteWitness as Lexer,
        parse::{CborElement, CborParser, CborValue},
        parser_prover::{ConcreteRankWitness, ConcreteWitness as Parser},
    },
    proto::hash::constants::{
        K_MSO_MAX_BYTES, K_MSO_OFFSET, K_STRUCTURE_ATTR_BITS as ATTR_BITS,
        K_STRUCTURE_ATTR_CAPACITY as ATTR_CAPACITY, K_STRUCTURE_BITS,
    },
};

#[derive(Clone, Debug)]
pub struct ConcreteAttributeWitness {
    pub lexer: Lexer,
    pub rank: ConcreteRankWitness,
    pub map: Parser,
}

impl ConcreteAttributeWitness {
    fn zero() -> Self {
        Self {
            lexer: Lexer::derive(&[0; ATTR_CAPACITY], 0).unwrap(),
            rank: ConcreteRankWitness {
                rank: vec![0; ATTR_CAPACITY],
            },
            map: Parser {
                threshold: vec![0; ATTR_CAPACITY],
            },
        }
    }
}

#[derive(Clone, Debug)]
pub struct ConcreteWitness {
    pub lexer: Lexer,
    pub rank: ConcreteRankWitness,
    pub maps: [Parser; 4],
    /// docType, deviceKeyInfo, validityInfo, valueDigests, in that order.
    pub root_values: [(usize, usize); 4],
    pub validity_key: usize,
    pub namespace: (usize, usize),
    pub digest_keys: Vec<usize>,
    pub attributes: Vec<ConcreteAttributeWitness>,
}

fn entries(item: &CborElement) -> Result<&[(CborElement, CborElement)], &'static str> {
    if let CborValue::Map(items) = &item.value {
        Ok(items)
    } else {
        Err("expected map")
    }
}

fn entry<'a>(
    item: &'a CborElement,
    name: &str,
) -> Result<(&'a CborElement, &'a CborElement), &'static str> {
    let mut matches = entries(item)?
        .iter()
        .filter(|(k, _)| matches!(&k.value, CborValue::Text(text) if text == name));
    let found = matches.next().ok_or("missing structural field")?;
    if matches.next().is_some() {
        return Err("duplicate structural field");
    }
    Ok((&found.0, &found.1))
}

impl ConcreteWitness {
    /// Invalid test inputs still need an assignment so circuit rejection can be
    /// tested. Production witness construction uses the fallible derive method.
    pub fn zero(attrs: usize) -> Self {
        let lexer = Lexer::derive(&vec![0; K_MSO_MAX_BYTES], 0).unwrap();
        let map = Parser {
            threshold: vec![0; K_MSO_MAX_BYTES],
        };
        let attr = ConcreteAttributeWitness::zero();
        Self {
            lexer,
            rank: ConcreteRankWitness {
                rank: vec![0; K_MSO_MAX_BYTES],
            },
            maps: std::array::from_fn(|_| map.clone()),
            root_values: [(0, 0); 4],
            validity_key: 0,
            namespace: (0, 0),
            digest_keys: vec![0; attrs],
            attributes: vec![attr; attrs],
        }
    }

    pub fn derive(
        signed: &[u8],
        namespace_key: usize,
        attributes: &[(usize, &[u8])],
    ) -> Result<Self, &'static str> {
        Self::derive_slots(
            signed,
            namespace_key,
            &attributes.iter().copied().map(Some).collect::<Vec<_>>(),
        )
    }

    /// Preserve public slot positions, leaving disabled slots unconstrained.
    pub fn derive_slots(
        signed: &[u8],
        namespace_key: usize,
        attributes: &[Option<(usize, &[u8])>],
    ) -> Result<Self, &'static str> {
        let raw = signed.get(K_MSO_OFFSET..).ok_or("MSO envelope")?;
        if raw.len() > K_MSO_MAX_BYTES {
            return Err("MSO exceeds circuit capacity");
        }
        let root = CborParser::new(raw)
            .parse_exact()
            .map_err(|_| "MSO parsing")?;
        let doc = entry(&root, "docType")?.1;
        let device = entry(&root, "deviceKeyInfo")?.1;
        let (validity_key, validity) = entry(&root, "validityInfo")?;
        let digests = entry(&root, "valueDigests")?.1;
        let namespace = entries(digests)?
            .iter()
            .find(|(k, _)| k.start == namespace_key)
            .ok_or("namespace map")?;
        let mut padded = raw.to_vec();
        padded.resize(K_MSO_MAX_BYTES, 0);
        let lexer = Lexer::derive(&padded, raw.len())?;
        let rank = ConcreteRankWitness::derive(&lexer)?;
        let mut maps = Vec::new();
        for map in [&root, validity, digests, &namespace.1] {
            maps.push(Parser::derive(&lexer, &rank, map.start, map.end)?);
        }
        let mut digest_keys = Vec::new();
        let mut attr_witnesses = Vec::new();
        for attribute in attributes {
            let Some((digest_offset, preimage)) = attribute else {
                digest_keys.push(0);
                attr_witnesses.push(ConcreteAttributeWitness::zero());
                continue;
            };
            let digest = entries(&namespace.1)?
                .iter()
                .find(|(_, v)| v.start == *digest_offset)
                .ok_or("digest outside namespace")?;
            digest_keys.push(digest.0.start);
            if preimage.len() > ATTR_CAPACITY {
                return Err("attribute too large");
            }
            let mut padded_attribute = preimage.to_vec();
            padded_attribute.resize(ATTR_CAPACITY, 0);
            let lexical = Lexer::derive_range(&padded_attribute, 4, preimage.len())?;
            let attribute_rank = ConcreteRankWitness::derive(&lexical)?;
            let map = Parser::derive(&lexical, &attribute_rank, 4, preimage.len())?;
            attr_witnesses.push(ConcreteAttributeWitness {
                lexer: lexical,
                rank: attribute_rank,
                map,
            });
        }
        Ok(Self {
            lexer,
            rank,
            maps: maps.try_into().unwrap(),
            root_values: [doc, device, validity, digests].map(|v| (v.start, v.end)),
            validity_key: validity_key.start,
            namespace: (namespace.1.start, namespace.1.end),
            digest_keys,
            attributes: attr_witnesses,
        })
    }

    /// Same input order as circuit::Witness::allocate. Shared by the prover and
    /// compiled circuit tests, including the precise counter widths.
    pub fn push(&self, mut push: impl FnMut(u64, usize)) {
        for n in &self.lexer.remaining {
            push(*n, K_STRUCTURE_BITS);
        }
        for n in &self.rank.rank {
            push(*n, K_STRUCTURE_BITS);
        }
        for map in &self.maps {
            for n in &map.threshold {
                push(*n, K_STRUCTURE_BITS);
            }
        }
        for (start, end) in self.root_values {
            push(start as u64, K_STRUCTURE_BITS);
            push(end as u64, K_STRUCTURE_BITS);
        }
        push(self.validity_key as u64, K_STRUCTURE_BITS);
        push(self.namespace.0 as u64, K_STRUCTURE_BITS);
        push(self.namespace.1 as u64, K_STRUCTURE_BITS);
        for key in &self.digest_keys {
            push(*key as u64, K_STRUCTURE_BITS);
        }
        for attr in &self.attributes {
            for n in &attr.lexer.remaining {
                push(*n, ATTR_BITS);
            }
            for n in &attr.rank.rank {
                push(*n, ATTR_BITS);
            }
            for n in &attr.map.threshold {
                push(*n, ATTR_BITS);
            }
        }
    }
}
