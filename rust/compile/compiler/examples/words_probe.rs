// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Emit the SHA-256 word layer's bit lists for one artifact.
//!
//! `Bridge/Sha256/S2Words.lean` and `S2State.lean` hold, for every 32-bit quantity the spec
//! bridge names, the **DAG node indices** of its 32 bits.  Those are per-artifact: the layout
//! (position -> name) is shared between the p256 and GF(2^128) circuits, but the node numbering
//! is not, so the lists have to be regenerated rather than copied.
//!
//! Usage: `words_probe FILE.sidecar`

use std::collections::HashMap;

use compile_compiler::cert::{self, ParsedNode};

/// LSB-first, matching the bit order the spec bridge's `ofBits` expects.
const WORD_BITS: usize = 32;

fn main() {
    let path = std::env::args().nth(1).expect("usage: words_probe FILE.sidecar");
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    let s = cert::parse_sidecar(&bytes).expect("sidecar parses");

    // Input position -> DAG node index.
    let mut node_of_pos: HashMap<usize, usize> = HashMap::new();
    for (index, node) in s.nodes.iter().enumerate() {
        if let ParsedNode::Input { position } = node {
            if node_of_pos.insert(*position, index).is_some() {
                panic!("two DAG nodes claim input position {position}");
            }
        }
    }

    // Layout name -> input position.
    let mut pos_of_name: HashMap<&str, usize> = HashMap::new();
    for (position, name) in &s.input_layout {
        pos_of_name.insert(name.as_str(), *position);
    }

    let bits = |group: &str, index: usize| -> Vec<usize> {
        (0..WORD_BITS)
            .map(|b| {
                let name = format!("{group}{index}_{b}");
                let pos = *pos_of_name
                    .get(name.as_str())
                    .unwrap_or_else(|| panic!("layout has no {name}"));
                *node_of_pos
                    .get(&pos)
                    .unwrap_or_else(|| panic!("no DAG input node at position {pos} ({name})"))
            })
            .collect()
    };

    let emit = |name: &str, rows: Vec<(usize, Vec<usize>)>| {
        println!("def {name} : Nat → List Nat");
        for (i, row) in &rows {
            let list: Vec<String> = row.iter().map(usize::to_string).collect();
            println!("  | {i} => [{}]", list.join(", "));
        }
        println!("  | _ => []\n");
    };

    // `wordBits t` is the message schedule: the input block for `t < 16`, `outw` after.
    emit(
        "wordBits",
        (0..64)
            .map(|t| {
                let row = if t < 16 {
                    bits("input_block", t)
                } else {
                    bits("outw", t - 16)
                };
                (t, row)
            })
            .collect(),
    );
    emit("hinBits", (0..8).map(|i| (i, bits("h0_", i))).collect());
    emit("h1Bits", (0..8).map(|i| (i, bits("h1_", i))).collect());
    emit("outaBits", (0..64).map(|t| (t, bits("outa", t))).collect());
    emit("outeBits", (0..64).map(|t| (t, bits("oute", t))).collect());

    eprintln!(
        "words_probe: ninput={} layout entries={} input nodes={}",
        s.ninput,
        s.input_layout.len(),
        node_of_pos.len()
    );
}
