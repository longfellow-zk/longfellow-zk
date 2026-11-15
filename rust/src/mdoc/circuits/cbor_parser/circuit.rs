// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    circuits::{
        bitvec::{Bitvec, BitvecIO, BitvecLogic},
        boolean::{Bitw, Boolean},
        routing::Routing,
    },
    compile::logic::{Eltw, Logic, LogicIO},
    mdoc::circuits::cbor_lexer::{counter::Counter, Lexed},
};

pub struct Span<L: Logic, const N: usize> {
    pub start: Bitvec<L, N>,
    pub end: Bitvec<L, N>,
}

impl<L: Logic, const N: usize> Clone for Span<L, N> {
    fn clone(&self) -> Self {
        Self {
            start: self.start.clone(),
            end: self.end.clone(),
        }
    }
}

/// Global pending slots after each byte. One trace is shared by every map.
pub struct RankWitness<L: Logic, const N: usize> {
    pub rank: Vec<Bitvec<L, N>>,
}

/// Threshold after each byte for one selected map.
pub struct Witness<L: Logic, const N: usize> {
    pub threshold: Vec<Bitvec<L, N>>,
}

impl<L: Logic, const N: usize> RankWitness<L, N> {
    pub fn constant(logic: &L, rank: &[u64]) -> Self {
        let bv = BitvecLogic::new(logic);
        Self {
            rank: rank.iter().map(|n| bv.of_u64(*n)).collect(),
        }
    }
}

impl<L: LogicIO, const N: usize> RankWitness<L, N> {
    pub fn allocate(logic: &L, capacity: usize, pos: &mut usize) -> Self {
        let bv = BitvecLogic::new(logic);
        let io = BitvecIO::new(&bv);
        Self {
            rank: (0..capacity).map(|_| io.next(pos)).collect(),
        }
    }
}

impl<L: Logic, const N: usize> Witness<L, N> {
    pub fn constant(logic: &L, threshold: &[u64]) -> Self {
        let bv = BitvecLogic::new(logic);
        Self {
            threshold: threshold.iter().map(|n| bv.of_u64(*n)).collect(),
        }
    }
}

impl<L: LogicIO, const N: usize> Witness<L, N> {
    pub fn allocate(logic: &L, capacity: usize, pos: &mut usize) -> Self {
        let bv = BitvecLogic::new(logic);
        let io = BitvecIO::new(&bv);
        Self {
            threshold: (0..capacity).map(|_| io.next(pos)).collect(),
        }
    }
}

#[must_use = "include the tree assertions or check maps in this parse"]
pub struct Parsed<L: Logic, const N: usize> {
    lexed: Lexed<L, N>,
    rank_before: Vec<Bitvec<L, N>>,
    encoded_rank: Vec<Eltw<L>>,
    checks: L::Assertions,
}

impl<L: Logic, const N: usize> Parsed<L, N> {
    pub fn assertions(&self) -> L::Assertions {
        self.checks.clone()
    }
}

#[must_use = "include the map assertions or use it in an entry assertion"]
pub struct CheckedMap<'s, L: Logic, const N: usize> {
    parsed: &'s Parsed<L, N>,
    span: Span<L, N>,
    boundaries: Vec<Bitw<L>>,
    threshold_before: Vec<Eltw<L>>,
    odd_before: Vec<Bitw<L>>,
    end_odd: Bitw<L>,
    checks: L::Assertions,
}

impl<L: Logic, const N: usize> CheckedMap<'_, L, N> {
    pub fn assertions(&self) -> L::Assertions {
        self.checks.clone()
    }
    pub fn span(&self) -> &Span<L, N> {
        &self.span
    }
}

#[must_use = "include the item assertions or refine it into a map"]
pub struct CheckedItem<'s, L: Logic, const N: usize> {
    parsed: &'s Parsed<L, N>,
    span: Span<L, N>,
    checks: L::Assertions,
}

impl<L: Logic, const N: usize> CheckedItem<'_, L, N> {
    pub fn assertions(&self) -> L::Assertions {
        self.checks.clone()
    }
    pub fn span(&self) -> &Span<L, N> {
        &self.span
    }
}

#[must_use = "include the entry assertions or use its checked items"]
pub struct Entry<'s, L: Logic, const N: usize> {
    pub key: CheckedItem<'s, L, N>,
    pub value: CheckedItem<'s, L, N>,
}

impl<L: Logic, const N: usize> Entry<'_, L, N> {
    pub fn assertions(&self) -> L::Assertions {
        self.value.assertions()
    }
}

pub struct CborParser<'a, L: Logic> {
    logic: &'a L,
    bv: BitvecLogic<'a, L>,
    boolean: Boolean<'a, L>,
}

impl<'a, L: Logic> CborParser<'a, L> {
    pub fn new(logic: &'a L) -> Self {
        Self {
            logic,
            bv: BitvecLogic::new(logic),
            boolean: Boolean::new(logic),
        }
    }

    /// Certify one complete ordered tree. A header consumes one pending slot
    /// and adds its arity. A live-rank check forbids a second root even when
    /// its arity could make the net update nonnegative.
    pub fn parse<const N: usize>(
        &self,
        lexed: Lexed<L, N>,
        witness: &RankWitness<L, N>,
    ) -> Parsed<L, N> {
        let bv = &self.bv;
        let b = &self.boolean;
        let counter = Counter::new(self.logic, N);
        let zero = counter.constant(0);
        assert_eq!(lexed.tokens.len(), witness.rank.len());
        let mut rank_before = Vec::with_capacity(witness.rank.len() + 1);
        rank_before.push(bv.of_u64::<N>(1));
        rank_before.extend(witness.rank.iter().cloned());
        let encoded_rank: Vec<_> = rank_before.iter().map(|r| counter.encode(r)).collect();
        let mut checks = vec![lexed.checks.clone()];
        for (i, token) in lexed.tokens.iter().enumerate() {
            let children = counter.select(&token.header, &token.arity, &zero);
            checks.push(self.logic.assert_all(
                &format!("byte.{i}"),
                &[
                    b.assert_false(
                        "live_rank",
                        &b.andb(&token.header, &bv.is_zero(&rank_before[i])),
                    ),
                    self.logic.assert_eq(
                        "rank",
                        &counter.add(&encoded_rank[i], &children),
                        &counter.increment(&encoded_rank[i + 1], &token.header),
                    ),
                ],
            ));
        }
        checks.push(
            self.logic
                .assert_eq("complete_tree", encoded_rank.last().unwrap(), &zero),
        );
        Parsed {
            lexed,
            rank_before,
            encoded_rank,
            checks: self.logic.assert_all("cbor_tree", &checks),
        }
    }

    /// The parsed root must be a map.
    pub fn root_map<'s, const N: usize>(
        &self,
        parsed: &'s Parsed<L, N>,
        witness: &Witness<L, N>,
    ) -> CheckedMap<'s, L, N> {
        self.scan_map(
            parsed,
            Span {
                start: parsed.lexed.start.clone(),
                end: parsed.lexed.end.clone(),
            },
            parsed.checks.clone(),
            witness,
            true,
        )
    }

    /// Refine a previously selected complete item into a map, retaining ancestry.
    pub fn item_map<'s, const N: usize>(
        &self,
        item: &CheckedItem<'s, L, N>,
        witness: &Witness<L, N>,
    ) -> CheckedMap<'s, L, N> {
        self.scan_map(
            item.parsed,
            item.span.clone(),
            item.checks.clone(),
            witness,
            false,
        )
    }

    fn scan_map<'s, const N: usize>(
        &self,
        parsed: &'s Parsed<L, N>,
        span: Span<L, N>,
        inherited: L::Assertions,
        witness: &Witness<L, N>,
        whole_stream: bool,
    ) -> CheckedMap<'s, L, N> {
        let b = &self.boolean;
        let bv = &self.bv;
        let counter = Counter::new(self.logic, N);
        let czero = counter.constant(0);
        let lexed = &parsed.lexed;
        let capacity = lexed.tokens.len();
        assert_eq!(witness.threshold.len(), capacity);
        let encoded: Vec<_> = witness
            .threshold
            .iter()
            .map(|t| counter.encode(t))
            .collect();
        let zero = bv.of_u64::<N>(0);
        // Only root_map and item_map call this method. The root's endpoints
        // are lexer boundaries; a selected item's endpoints were certified by
        // entry. In both cases the inherited assertions retain that proof.
        let mut checks = vec![inherited];
        let mut boundaries = Vec::with_capacity(capacity + 1);
        let mut threshold_before = Vec::with_capacity(capacity + 1);
        let mut odd_before = Vec::with_capacity(capacity + 1);
        let mut map_headers = b.falseb();
        for (i, token) in lexed.tokens.iter().enumerate() {
            let threshold = if i == 0 {
                &zero
            } else {
                &witness.threshold[i - 1]
            };
            let previous = if i == 0 { &czero } else { &encoded[i - 1] };
            let index = bv.of_u64::<N>(i as u64);
            let root = bv.eqb(&span.start, &index);
            map_headers = b.or_assuming_at_most_one_true(
                &map_headers,
                &b.andb(&root, &b.andb(&token.header, &token.map)),
            );
            // For a root map, the lexer already gates every header to this
            // exact range. Nested maps still need their tighter end bound.
            let body_header = if whole_stream {
                token.header.clone()
            } else {
                b.andb(&token.header, &bv.lt(&index, &span.end))
            };
            // Before the map header the threshold is zero, whereas the
            // complete-tree live-rank check makes rank_before nonzero at
            // every genuine header (including this map's own header).
            // Equality below therefore excludes those positions without a
            // second per-byte comparison against span.start.
            // Starting a child lowers the threshold immediately. Every node
            // in that child's subtree then has rank strictly above it until
            // the subtree completes. Genuine headers gate payload bytes out.
            let boundary = b.andb(&body_header, &bv.eqb(&parsed.rank_before[i], threshold));
            let target = counter.select(&root, &parsed.encoded_rank[i + 1], previous);
            checks.push(self.logic.assert_all(
                &format!("byte.{i}"),
                &[self.logic.assert_eq(
                    "threshold",
                    &target,
                    &counter.increment(&encoded[i], &boundary),
                )],
            ));
            boundaries.push(boundary);
            threshold_before.push(previous.clone());
            odd_before.push(threshold[0].clone());
        }
        boundaries.push(b.falseb());
        threshold_before.push(encoded.last().cloned().unwrap_or_else(|| czero.clone()));
        odd_before.push(
            witness
                .threshold
                .last()
                .map(|r| r[0].clone())
                .unwrap_or_else(|| b.falseb()),
        );
        checks.push(b.assert_true("map_header", &map_headers));
        // The global parse certifies the root's end; entry certifies each
        // nested item's exact end. Inductively, all direct children therefore
        // finish at span.end, so the final threshold is its rank baseline.
        // Reusing its low bit avoids routing the global rank to every map end.
        let end_odd = odd_before.last().unwrap().clone();
        CheckedMap {
            parsed,
            span,
            boundaries,
            threshold_before,
            odd_before,
            end_odd,
            checks: self.logic.assert_all("cbor_parser", &checks),
        }
    }

    /// Prove that `key_start` and `value` form one immediate entry in `map`.
    /// The returned spans cover complete encoded items. Compare their contents
    /// separately; existence of an entry does not establish key uniqueness.
    pub fn entry<'s, const N: usize>(
        &self,
        map: &CheckedMap<'s, L, N>,
        key_start: &Bitvec<L, N>,
        value: &Span<L, N>,
    ) -> Entry<'s, L, N> {
        let bv = &self.bv;
        let b = &self.boolean;
        let routing = Routing::new(self.logic);
        let counter = Counter::new(self.logic, N);
        let czero = counter.constant(0);
        let select_count = |index: &Bitvec<L, N>| {
            routing.shifte(6, index, 1, &map.threshold_before, &czero)[0].clone()
        };
        let select_odd = |index: &Bitvec<L, N>| {
            routing.shiftb(6, index, 1, &map.odd_before, &b.falseb())[0].clone()
        };
        let select_boundary = |index: &Bitvec<L, N>| {
            routing.shiftb(6, index, 1, &map.boundaries, &b.falseb())[0].clone()
        };
        let ck = select_count(key_start);
        let cv = select_count(&value.start);
        let ce = select_count(&value.end);
        // Each direct-child boundary has a strictly decreasing threshold.
        // Consecutive thresholds therefore prove ordering and adjacency.
        // Relative to the rank at map end, an even threshold is a key.
        // The end must be the next child boundary or this map's certified end.
        let checks = self.logic.assert_all(
            "map_entry",
            &[
                map.checks.clone(),
                b.assert_true("key_boundary", &select_boundary(key_start)),
                b.assert_eq("key_parity", &select_odd(key_start), &map.end_odd),
                b.assert_true("value_boundary", &select_boundary(&value.start)),
                b.assert_true(
                    "value_end_boundary",
                    &b.orb(
                        &bv.eqb(&value.end, &map.span.end),
                        &select_boundary(&value.end),
                    ),
                ),
                self.logic.assert_eq(
                    "key_value_adjacent",
                    &ck,
                    &counter.add(&cv, &counter.constant(1)),
                ),
                self.logic.assert_eq(
                    "value_end_adjacent",
                    &cv,
                    &counter.add(&ce, &counter.constant(1)),
                ),
            ],
        );
        Entry {
            key: CheckedItem {
                parsed: map.parsed,
                span: Span {
                    start: key_start.clone(),
                    end: value.start.clone(),
                },
                checks: checks.clone(),
            },
            value: CheckedItem {
                parsed: map.parsed,
                span: value.clone(),
                checks,
            },
        }
    }
}
