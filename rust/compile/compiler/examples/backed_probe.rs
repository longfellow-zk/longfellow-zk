// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Which assertion records fail `Quadcert.backedRaw`, and why?
//!
//! `backed_check` is the soundness half of the assertion bridge: every named record must be
//! carried by a real circuit constraint, either a materialized mid-circuit assertion term
//! `(wireIndex, i, i, zero)` in its own layer or a last-layer output wire. Lean reports only
//! that the conjunction is false, so this mirrors the predicate record by record.
//!
//! Usage: `backed_probe FILE.sidecar`

use compile_compiler::cert;

fn main() {
    let path = std::env::args().nth(1).expect("usage: backed_probe FILE.sidecar");
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    let s = cert::parse_sidecar(&bytes).expect("sidecar parses");

    let zero_const = s
        .constants
        .iter()
        .position(|c| c.iter().all(|b| *b == 0))
        .unwrap_or(s.constants.len());
    println!(
        "zeroConst = {zero_const}, noutput = {}, layers = {}, asserts = {}",
        s.noutput,
        s.layers.len(),
        s.assertions.len()
    );

    let mut bad = 0usize;
    let mut reasons: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    for a in &s.assertions {
        let wire = s.node_wires.get(a.asserted_node).copied().flatten();
        let mid = a.wire_layer < s.layers.len()
            && match wire {
                Some((l, i)) => {
                    l == a.wire_layer + 1
                        && s.layers[a.wire_layer].terms.iter().any(|t| {
                            *t == (
                                a.wire_index as u32,
                                i as u32,
                                i as u32,
                                zero_const as u32,
                            )
                        })
                }
                None => false,
            };
        let out = a.wire_index < s.noutput && wire == Some((0, a.wire_index));
        if mid || out {
            continue;
        }
        bad += 1;
        // Why not? Report the shape of the term that *is* on that wire, if any.
        let reason = match wire {
            None => "node has no wire".to_string(),
            Some((l, _)) if l != a.wire_layer + 1 => {
                format!("wire layer {l} != wireLayer+1 = {}", a.wire_layer + 1)
            }
            Some((_, i)) => {
                let cands: Vec<_> = s.layers[a.wire_layer.min(s.layers.len() - 1)]
                    .terms
                    .iter()
                    .filter(|t| t.0 == a.wire_index as u32 && t.1 == i as u32 && t.2 == i as u32)
                    .collect();
                if cands.is_empty() {
                    format!("no term (g={}, {i}, {i}, *) in layer {}", a.wire_index, a.wire_layer)
                } else {
                    format!(
                        "term present but kIndex {:?} != zeroConst {zero_const}",
                        cands.iter().map(|t| t.3).collect::<Vec<_>>()
                    )
                }
            }
        };
        if bad <= 10 {
            println!(
                "  FAIL node {} @ ({},{}) wire {:?} paths {:?}: {reason}",
                a.asserted_node, a.wire_layer, a.wire_index, wire, a.paths
            );
        }
        *reasons.entry(reason).or_default() += 1;
    }
    // Compare the sidecar's constant table with the artifact's, if one is alongside.
    if let Some(lfc2) = std::env::args().nth(2) {
        let bytes = std::fs::read(&lfc2).unwrap_or_else(|e| panic!("read {lfc2}: {e}"));
        let field = compile_algebra::p256::P256Field::new();
        let (c, _) = core_proto::reader::CircuitReader::new(&field, core_proto::FieldID::P256)
            .from_bytes_lfc2(&bytes, true)
            .expect("lfc2 parses");
        let hex = |b: &[u8]| -> String { b.iter().rev().map(|x| format!("{x:02x}")).collect() };
        let art: Vec<String> = c
            .raw
            .constants
            .iter()
            .map(|k| hex(&core_algebra::SerializableField::to_bytes(&field, k)))
            .collect();
        let side: Vec<String> = s.constants.iter().map(|c| hex(c)).collect();
        println!("\nconstants: sidecar {} artifact {}", side.len(), art.len());
        println!("  sidecar[0..4]  {:?}", &side[..4.min(side.len())]);
        println!("  artifact[0..4] {:?}", &art[..4.min(art.len())]);
        println!("  identical order: {}", side == art);
        let szero = side.iter().position(|v| v.trim_start_matches('0').is_empty());
        let azero = art.iter().position(|v| v.trim_start_matches('0').is_empty());
        println!("  zero at sidecar {szero:?}, artifact {azero:?}");
    }
    println!("\n{bad} of {} records fail", s.assertions.len());
    for (r, n) in reasons {
        println!("  {n:>5}  {r}");
    }
}
