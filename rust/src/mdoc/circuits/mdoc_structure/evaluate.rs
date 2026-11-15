// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Test-only conversion of native structural witnesses to constant circuit wires.
use super::{AttributeWitness, Witness};
use crate::{
    circuits::bitvec::BitvecLogic,
    compile::logic::Logic,
    mdoc::{
        cbor::structure_prover::ConcreteWitness,
        circuits::{cbor_lexer, cbor_parser, cbor_parser::Span},
    },
};
impl<L: Logic> Witness<L> {
    pub fn constant(logic: &L, value: &ConcreteWitness) -> Self {
        let bv = BitvecLogic::new(logic);
        let span = |(start, end): (usize, usize)| Span {
            start: bv.of_u64(start as u64),
            end: bv.of_u64(end as u64),
        };
        Self {
            lexer: cbor_lexer::Witness::constant(logic, &value.lexer.remaining),
            rank: cbor_parser::RankWitness::constant(logic, &value.rank.rank),
            maps: std::array::from_fn(|i| {
                cbor_parser::Witness::constant(logic, &value.maps[i].threshold)
            }),
            root_values: std::array::from_fn(|i| span(value.root_values[i])),
            validity_key: bv.of_u64(value.validity_key as u64),
            namespace: span(value.namespace),
            digest_keys: value
                .digest_keys
                .iter()
                .map(|key| bv.of_u64(*key as u64))
                .collect(),
            attributes: value
                .attributes
                .iter()
                .map(|a| AttributeWitness {
                    lexer: cbor_lexer::Witness::constant(logic, &a.lexer.remaining),
                    rank: cbor_parser::RankWitness::constant(logic, &a.rank.rank),
                    map: cbor_parser::Witness::constant(logic, &a.map.threshold),
                })
                .collect(),
        }
    }
}
