// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::mdoc::cbor::lexer_prover::ConcreteWitness as LexicalWitness;

/// Pending slots in the whole tree, after each byte. Shared across map scans.
#[derive(Clone, Debug)]
pub struct ConcreteRankWitness {
    pub rank: Vec<u64>,
}

impl ConcreteRankWitness {
    pub fn derive(lexed: &LexicalWitness) -> Result<Self, &'static str> {
        let mut pending = 1u64;
        let mut rank = Vec::with_capacity(lexed.headers.len());
        for (i, header) in lexed.headers.iter().enumerate() {
            if *header {
                pending = pending
                    .checked_sub(1)
                    .ok_or("multiple CBOR roots")?
                    .checked_add(lexed.arities[i])
                    .ok_or("CBOR rank overflow")?;
            }
            rank.push(pending);
        }
        if pending != 0 {
            return Err("incomplete CBOR tree");
        }
        Ok(Self { rank })
    }
}

#[derive(Clone, Debug)]
pub struct ConcreteWitness {
    pub threshold: Vec<u64>,
}

impl ConcreteWitness {
    pub fn derive(
        lexed: &LexicalWitness,
        rank: &ConcreteRankWitness,
        start: usize,
        end: usize,
    ) -> Result<Self, &'static str> {
        let capacity = lexed.headers.len();
        if rank.rank.len() != capacity {
            return Err("rank capacity mismatch");
        }
        if start < lexed.range.start
            || start >= end
            || end > lexed.range.end
            || !lexed.headers[start]
            || !lexed.maps[start]
        {
            return Err("expected CBOR map");
        }
        if end != lexed.range.end && !lexed.headers[end] {
            return Err("map end inside token");
        }
        let mut threshold = vec![0; capacity];
        let mut current = rank.rank[start];
        for (i, value) in threshold.iter_mut().enumerate().take(end).skip(start) {
            if i > start && lexed.headers[i] && rank.rank[i - 1] == current {
                current = current.checked_sub(1).ok_or("excess map children")?;
            }
            *value = current;
        }
        if current != rank.rank[end - 1] {
            return Err("incomplete CBOR map");
        }
        threshold[end..].fill(current);
        Ok(Self { threshold })
    }
}
