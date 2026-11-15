// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::counter::Counter;
use crate::{
    circuits::{
        bitvec::{Bitvec, BitvecIO, BitvecLogic, V8},
        boolean::{Bitw, Boolean},
    },
    compile::logic::{Eltw, Logic, LogicIO},
};

// Decode only what framing needs. In particular, integer/tag arguments need
// no arithmetic, and no legacy decoder length checks enter this circuit.
struct Header<L: Logic> {
    stringp: Bitw<L>,
    itemsp: Bitw<L>,
    mapp: Bitw<L>,
    arrayp: Bitw<L>,
    tagp: Bitw<L>,
    specialp: Bitw<L>,
    simple_specialp: Bitw<L>,
    count0_23: Bitw<L>,
    count24_27: Bitw<L>,
    count24: Bitw<L>,
    count25: Bitw<L>,
}

impl<L: Logic> Header<L> {
    fn decode(bv: &BitvecLogic<L>, b: &Boolean<L>, byte: &V8<L>) -> Self {
        Self {
            stringp: bv.eqmask(byte, 0x40, 0xc0),
            itemsp: bv.eqmask(byte, 0x80, 0xc0),
            mapp: bv.eqmask(byte, 0xa0, 0xe0),
            arrayp: bv.eqmask(byte, 0x80, 0xe0),
            tagp: bv.eqmask(byte, 0xc0, 0xe0),
            specialp: bv.eqmask(byte, 0xe0, 0xe0),
            simple_specialp: bv.eqmask(byte, 0xf4, 0xfc),
            count0_23: b.notb(&bv.eqmask(byte, 24, 24)),
            count24_27: bv.eqmask(byte, 24, 28),
            count24: bv.eqmask(byte, 24, 31),
            count25: bv.eqmask(byte, 25, 31),
        }
    }
}

/// Bytes still belonging to the current token after each buffer position.
pub struct Witness<L: Logic, const N: usize> {
    pub remaining: Vec<Bitvec<L, N>>,
}

impl<L: Logic, const N: usize> Witness<L, N> {
    pub fn constant(logic: &L, remaining: &[u64]) -> Self {
        let bv = BitvecLogic::new(logic);
        Self {
            remaining: remaining.iter().map(|n| bv.of_u64(*n)).collect(),
        }
    }
}

impl<L: LogicIO, const N: usize> Witness<L, N> {
    pub fn allocate(logic: &L, capacity: usize, pos: &mut usize) -> Self {
        let bv = BitvecLogic::new(logic);
        let io = BitvecIO::new(&bv);
        Self {
            remaining: (0..capacity).map(|_| io.next(pos)).collect(),
        }
    }
}

pub(in crate::mdoc::circuits) struct Token<L: Logic> {
    pub header: Bitw<L>,
    pub map: Bitw<L>,
    pub arity: Eltw<L>,
}

/// A checked token stream. Construction is private; parsing retains its checks.
#[must_use = "include the lexer assertions or pass this stream to the parser"]
pub struct Lexed<L: Logic, const N: usize> {
    pub(in crate::mdoc::circuits) tokens: Vec<Token<L>>,
    pub(in crate::mdoc::circuits) start: Bitvec<L, N>,
    pub(in crate::mdoc::circuits) end: Bitvec<L, N>,
    pub(in crate::mdoc::circuits) checks: L::Assertions,
}

impl<L: Logic, const N: usize> Lexed<L, N> {
    pub fn assertions(&self) -> L::Assertions {
        self.checks.clone()
    }

    pub fn headers(&self) -> Vec<Bitw<L>> {
        self.tokens.iter().map(|t| t.header.clone()).collect()
    }
}

pub struct CborLexer<'a, L: Logic> {
    logic: &'a L,
    bv: BitvecLogic<'a, L>,
    boolean: Boolean<'a, L>,
}

impl<'a, L: Logic> CborLexer<'a, L> {
    pub fn new(logic: &'a L) -> Self {
        Self {
            logic,
            bv: BitvecLogic::new(logic),
            boolean: Boolean::new(logic),
        }
    }

    /// Lex `[0, actual_len)` in a buffer whose capacity is `bytes.len()`.
    pub fn lex<const N: usize>(
        &self,
        bytes: &[V8<L>],
        actual_len: &Bitvec<L, N>,
        witness: &Witness<L, N>,
    ) -> Lexed<L, N> {
        self.lex_range(bytes, &self.bv.of_u64(0), actual_len, witness)
    }

    /// Lex an explicitly bounded subrange, e.g. an authenticated tag-24 payload.
    /// The caller binds these endpoints to its enclosing encoding.
    pub fn lex_range<const N: usize>(
        &self,
        bytes: &[V8<L>],
        start: &Bitvec<L, N>,
        end: &Bitvec<L, N>,
        witness: &Witness<L, N>,
    ) -> Lexed<L, N> {
        let capacity = bytes.len();
        assert!((5..=16).contains(&N));
        assert!(capacity + 9 < (1usize << N));
        assert_eq!(witness.remaining.len(), capacity);
        let b = &self.boolean;
        let bv = &self.bv;
        let counter = Counter::new(self.logic, N);
        // Decode byte arguments once in the counter's algebraic encoding.
        // Every byte can serve as an 8-bit argument and the low/high byte of
        // a 16-bit argument. Selecting encoded values avoids bitwise muxes
        // followed by a fresh exponentiation at every token position.
        let argument_counter = counter.widened(16);
        let byte_counts: Vec<_> = bytes
            .iter()
            .map(|byte| argument_counter.encode(&bv.zext::<8, 16>(byte)))
            .collect();
        let high_byte_counts: Vec<_> = bytes
            .iter()
            .map(|byte| {
                argument_counter.encode(&bv.from_fn::<16, _>(|bit| {
                    if bit < 8 {
                        b.falseb()
                    } else {
                        byte[bit - 8].clone()
                    }
                }))
            })
            .collect();
        let czero = counter.constant(0);
        let encoded: Vec<_> = witness
            .remaining
            .iter()
            .map(|n| counter.encode(n))
            .collect();
        let zero = bv.of_u64::<N>(0);
        let mut checks = vec![
            b.assert_true("range_order", &bv.leq(start, end)),
            b.assert_true("range_end", &bv.leq(end, &bv.of_u64(capacity as u64))),
        ];
        let mut tokens = Vec::with_capacity(capacity);
        for i in 0..capacity {
            let prev = if i == 0 {
                &zero
            } else {
                &witness.remaining[i - 1]
            };
            let prev_encoded = if i == 0 { &czero } else { &encoded[i - 1] };
            let index = bv.of_u64::<N>(i as u64);
            let active = b.andb(&bv.leq(start, &index), &bv.lt(&index, end));
            let idle = bv.eqb(prev, &zero);
            let header = b.andb(&active, &idle);
            let d = Header::decode(bv, b, &bytes[i]);
            // Major classes and additional-info alternatives are disjoint.
            // Their union is a linear sum in either arithmetic field.
            let lengths = b.or_assuming_at_most_one_true(&d.stringp, &d.itemsp);
            let short_arg = b.or_assuming_at_most_one_true(
                &d.count0_23,
                &b.or_assuming_at_most_one_true(&d.count24, &d.count25),
            );
            let good_arg = b.or_assuming_at_most_one_true(&d.count0_23, &d.count24_27);
            let valid = b.andb(
                &b.andb(&good_arg, &b.orb(&b.notb(&lengths), &short_arg)),
                &b.or_assuming_at_most_one_true(&b.notb(&d.specialp), &d.simple_specialp),
            );

            // Only lengths/counts are interpreted. Integer/tag argument bytes
            // remain opaque, but their full widths are checked by the countdown.
            let next = bytes.get(i + 1).cloned().unwrap_or_else(|| bv.of_u8(0));
            let next2 = bytes.get(i + 2).cloned().unwrap_or_else(|| bv.of_u8(0));
            let small = bv.from_fn::<16, _>(|j| {
                if j < 5 {
                    bytes[i][j].clone()
                } else {
                    b.falseb()
                }
            });
            let arg8 = bv.zext::<8, 16>(&next);
            let arg16 = bv.from_fn::<16, _>(|j| {
                if j < 8 {
                    next2[j].clone()
                } else {
                    next[j - 8].clone()
                }
            });
            let small_count = argument_counter.encode(&small);
            let arg8_count = byte_counts.get(i + 1).unwrap_or(&czero);
            let high_count = high_byte_counts.get(i + 1).unwrap_or(&czero);
            let low_count = byte_counts.get(i + 2).unwrap_or(&czero);
            let arg16_count = counter.add(high_count, low_count);
            let count = counter.select(
                &d.count0_23,
                &small_count,
                &counter.select(&d.count24, arg8_count, &arg16_count),
            );
            let limit = bv.of_u64::<16>(capacity as u64);
            let map_limit = bv.of_u64::<16>((capacity / 2) as u64);
            // Compare against constants before selecting: choosing a 16-bit
            // bound first would turn this into a variable/variable comparator.
            let bounds = |argument: &Bitvec<L, 16>| {
                b.muxb(
                    &d.mapp,
                    &bv.leq(argument, &map_limit),
                    &bv.leq(argument, &limit),
                )
            };
            let bounded = b.muxb(
                &d.count0_23,
                &bounds(&small),
                &b.muxb(&d.count24, &bounds(&arg8), &bounds(&arg16)),
            );
            let arity = counter.select(
                &d.mapp,
                &counter.add(&count, &count),
                &counter.select(
                    &d.arrayp,
                    &count,
                    &counter.select(&d.tagp, &counter.constant(1), &czero),
                ),
            );

            let width24_25 =
                counter.select(&bytes[i][0], &counter.constant(3), &counter.constant(2));
            let width26_27 =
                counter.select(&bytes[i][0], &counter.constant(9), &counter.constant(5));
            let extended = counter.select(&bytes[i][1], &width26_27, &width24_25);
            let head_width = counter.select(&d.count0_23, &counter.constant(1), &extended);
            let width = counter.add(&head_width, &counter.select(&d.stringp, &count, &czero));
            let target = counter.select(
                &active,
                &counter.select(&header, &width, prev_encoded),
                &czero,
            );
            checks.push(self.logic.assert_all(
                &format!("byte.{i}"),
                &[
                    b.assert_true("valid_header", &b.impliesb(&header, &valid)),
                    b.assert_true(
                        "bounded_length",
                        &b.impliesb(&b.andb(&header, &lengths), &bounded),
                    ),
                    b.assert_true("range_boundary", &b.impliesb(&b.notb(&active), &idle)),
                    self.logic.assert_eq(
                        "countdown",
                        &target,
                        &counter.increment(&encoded[i], &active),
                    ),
                ],
            ));
            tokens.push(Token {
                header,
                map: d.mapp,
                arity,
            });
        }
        if let Some(last) = witness.remaining.last() {
            checks.push(bv.assert_eq("complete_token", last, &zero));
        }
        Lexed {
            tokens,
            start: start.clone(),
            end: end.clone(),
            checks: self.logic.assert_all("cbor_lexer", &checks),
        }
    }
}

#[cfg(test)]
mod tests;
