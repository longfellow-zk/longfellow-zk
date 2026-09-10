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

//! Shape of the `sum_local` obligation on real ECDSA2 data.
//!
//! `sum_local` must relate, for every DAG node mapped to wire `(L, g)`, the layer's fold
//! restricted to `g` with that node's own sum.  Two ways to discharge it per node:
//!
//!   (a) unfold `evalLayer` and normalise with `ring`, as Rung 1 does for its 19 nodes; the
//!       fold ranges over the layer's *entire* term list, so the elaborated goal carries every
//!       term in the layer whatever the node's own size;
//!   (b) supply the node's group of terms and check a `Forall₂ Realises` correspondence, which
//!       is local: its size is the node's own arity.
//!
//! This prints the numbers that decide between them — per-layer node counts, group sizes, and
//! how much bigger (a)'s goal is than (b)'s.

use std::collections::HashMap;

use circuits_ecdsa2::EcdsaCircuit;
use compile_algebra::{p256::P256Field, secp256r1::Secp256r1};
use compile_compiler::{cert, compile_with_cert};
use compile_eval::FieldID;

fn main() {
    let fc = P256Field::new();
    let curve = Secp256r1::new(&fc);
    let (circuit, stats, symbols, schedule_info) = compile_with_cert(&fc, |iologic| {
        let mut pos = compile_logic::K_FIRST_WIRE_POSITION;
        let ecdsa = EcdsaCircuit::new(&iologic, &curve);
        let given = circuits_ecdsa2::allocate_given_wires(&iologic, &mut pos);
        let derived = circuits_ecdsa2::allocate_derived_wires(&iologic, &mut pos);
        (ecdsa.assert_signature(&given, &derived), 1, 0)
    });

    // The layout is irrelevant to `sum_local`; a minimal one keeps the sidecar valid.
    let layout = [cert::InputLayoutEntry {
        position: 0,
        name: "one",
    }];
    let bytes = cert::build_sidecar(
        &fc,
        FieldID::P256,
        &circuit,
        &symbols,
        &schedule_info,
        &layout,
    );
    let s = cert::parse_sidecar(&bytes).expect("sidecar parses");
    println!(
        "ecdsa2: ninput={} layers={} nodes={} assertions={} terms={}",
        s.ninput,
        s.layers.len(),
        s.nodes.len(),
        s.assertions.len(),
        stats.nterms
    );

    // Nodes are placed on wires; `node_wires` gives (layer, index).  Input nodes sit at the
    // pseudo-layer `layers.len()` and carry no obligation.
    let mut nodes_per_layer: HashMap<usize, usize> = HashMap::new();
    for w in s.node_wires.iter().flatten() {
        *nodes_per_layer.entry(w.0).or_default() += 1;
    }

    println!("\nlayer  terms   nodes   grouped-terms  max|group|  mean|group|   (a)/(b) size ratio");
    for (l, layer) in s.layers.iter().enumerate() {
        let mut group_sizes: HashMap<u32, usize> = HashMap::new();
        for (g, _, _, _) in &layer.terms {
            *group_sizes.entry(*g).or_default() += 1;
        }
        let nodes = nodes_per_layer.get(&l).copied().unwrap_or(0);
        let max = group_sizes.values().copied().max().unwrap_or(0);
        let mean = if group_sizes.is_empty() {
            0.0
        } else {
            layer.terms.len() as f64 / group_sizes.len() as f64
        };
        // (a) carries the whole layer per node; (b) carries only the node's own group.
        let ratio = if mean > 0.0 {
            layer.terms.len() as f64 / mean
        } else {
            0.0
        };
        println!(
            "{l:>4}  {:>6}  {:>6}  {:>13}  {:>10}  {:>10.1}  {:>18.0}x",
            layer.terms.len(),
            nodes,
            group_sizes.len(),
            max,
            mean,
            ratio
        );
    }

    // Total work under each scheme, in "terms mentioned across all per-node goals".
    let mut a_total = 0usize;
    let mut b_total = 0usize;
    for (l, layer) in s.layers.iter().enumerate() {
        let nodes = nodes_per_layer.get(&l).copied().unwrap_or(0);
        a_total += nodes * layer.terms.len();
        b_total += layer.terms.len();
    }
    println!(
        "\ntotal terms across per-node goals:  (a) ring-per-node {a_total:>12}   \
         (b) grouped {b_total:>8}   ratio {:.0}x",
        a_total as f64 / b_total.max(1) as f64
    );

    // ---- emit the head-to-head Lean experiment on one real layer ----
    let Some(out) = std::env::args().nth(1) else {
        return;
    };
    let l: usize = std::env::args()
        .nth(2)
        .and_then(|v| v.parse().ok())
        .unwrap_or(9);
    let k: usize = std::env::args()
        .nth(3)
        .and_then(|v| v.parse().ok())
        .unwrap_or(8);
    let layer = &s.layers[l];

    let mut groups: HashMap<u32, Vec<(u32, u32, u32, u32)>> = HashMap::new();
    for t in &layer.terms {
        groups.entry(t.0).or_default().push(*t);
    }
    // The first k nodes living on this layer, with their sum terms.
    let mut chosen: Vec<(usize, u32, Vec<(u32, usize, usize)>)> = Vec::new();
    for (n, w) in s.node_wires.iter().enumerate() {
        if chosen.len() == k {
            break;
        }
        let Some((wl, wg)) = w else { continue };
        if *wl != l {
            continue;
        }
        if let cert::ParsedNode::Sum { terms } = &s.nodes[n] {
            chosen.push((n, *wg as u32, terms.clone()));
        }
    }

    let raw_terms = |ts: &[(u32, u32, u32, u32)]| -> String {
        ts.iter()
            .map(|(g, h0, h1, kk)| format!("⟨{g}, {h0}, {h1}, {kk}⟩"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let all_terms = raw_terms(&layer.terms);

    // (a): one goal per node, each carrying the layer's entire term list through `evalLayer`.
    let mut a = String::from(
        "-- Style (a): unfold `evalLayer` and normalise, as Rung 1 does.  Each goal drags the\n\
         -- whole layer through the fold regardless of how few terms the node actually has.\n\
         import quadcert.Ingest\nset_option maxRecDepth 4000000\nset_option maxHeartbeats 0\n\
         namespace SumLocalExpA\nopen Quadcert\nvariable {F : Type} [Field F]\n\n",
    );
    a.push_str(&format!(
        "def layerRaw : RawLayer := ⟨{}, [{all_terms}]⟩\n\n",
        layer.nw
    ));
    for (n, g, terms) in &chosen {
        let rhs = groups
            .get(g)
            .map(|ts| {
                ts.iter()
                    .map(|(_, h0, h1, kk)| format!("consts {kk} * vin {h0} * vin {h1}"))
                    .collect::<Vec<_>>()
                    .join(" + ")
            })
            .unwrap_or_else(|| "0".to_string());
        a.push_str(&format!(
            "-- node {n}, wire ({l},{g}), {} own terms out of {} in the layer\n\
             example (consts vin : Nat → F) :\n    \
             evalLayer (layerRaw.toLayer consts) vin {g} = {rhs} := by\n  \
             simp [evalLayer, layerRaw, RawLayer.toLayer, rawTerm]\n  try ring\n\n",
            groups.get(g).map_or(0, Vec::len),
            layer.terms.len()
        ));
    }
    a.push_str("end SumLocalExpA\n");
    std::fs::write(format!("{out}/SumLocalExpA.lean"), a).expect("write A");

    // (b): one goal per node, mentioning only that node's own group.
    let mut b = String::from(
        "-- Style (b): supply the node's group and check `Forall₂ Realises`.  Local: the goal\n\
         -- is the size of the node's own arity, not the layer's.\n\
         import quadcert.Ingest\nset_option maxRecDepth 4000000\nset_option maxHeartbeats 0\n\
         namespace SumLocalExpB\nopen Quadcert\nvariable {F : Type} [Field F]\n\n",
    );
    b.push_str(&format!(
        "/-- The wire map, restricted to the operands these nodes mention. -/\n\
         def wireFn : Nat → Option (Nat × Nat)\n{}  | _ => none\n\n",
        chosen
            .iter()
            .flat_map(|(_, _, terms)| terms.iter().flat_map(|(_, w0, w1)| [*w0, *w1]))
            .collect::<std::collections::BTreeSet<_>>()
            .iter()
            .map(|w| {
                let (wl, wg) = s.node_wires[*w as usize].unwrap_or((l + 1, 0));
                format!("  | {w} => some ({wl}, {wg})\n")
            })
            .collect::<String>()
    ));
    for (n, g, terms) in &chosen {
        let grp = groups.get(g).cloned().unwrap_or_default();
        // Pair each of the node's sum terms with the layer term that realises it, and record
        // the operand orientation: `canonical_term` sorts (h0,h1), so roughly half the pairs
        // are swapped relative to the DAG's operand order.  This matching is exactly what the
        // real emitter has to do, so the experiment measures the real proof.
        let mut pairs: Vec<(String, String, &'static str)> = Vec::new();
        let mut used = vec![false; grp.len()];
        for (kk, w0, w1) in terms {
            let g0 = s.node_wires[*w0].map(|w| w.1);
            let g1 = s.node_wires[*w1].map(|w| w.1);
            let mut found = false;
            for (i, t) in grp.iter().enumerate() {
                if used[i] || t.3 as usize != *kk as usize {
                    continue;
                }
                let dir = if g0 == Some(t.1 as usize) && g1 == Some(t.2 as usize) {
                    "Or.inl"
                } else if g0 == Some(t.2 as usize) && g1 == Some(t.1 as usize) {
                    "Or.inr"
                } else {
                    continue;
                };
                used[i] = true;
                pairs.push((
                    format!("(rawTerm consts ⟨{}, {}, {}, {}⟩)", t.0, t.1, t.2, t.3),
                    format!("⟨consts {kk}, {w0}, {w1}⟩"),
                    dir,
                ));
                found = true;
                break;
            }
            assert!(found, "node {n}: no layer term realises sum term ({kk},{w0},{w1})");
        }
        let proof = pairs.iter().rev().fold("List.Forall₂.nil".to_string(), |rest, (_, _, d)| {
            format!("(List.Forall₂.cons ⟨rfl, {d} ⟨rfl, rfl⟩⟩ {rest})")
        });
        b.push_str(&format!(
            "-- node {n}, wire ({l},{g}), {} own terms\n\
             example (consts : Nat → F) :\n    \
             List.Forall₂ (Realises wireFn {l}) [{}] [{}] :=\n  {proof}\n\n",
            grp.len(),
            pairs.iter().map(|p| p.0.clone()).collect::<Vec<_>>().join(", "),
            pairs.iter().map(|p| p.1.clone()).collect::<Vec<_>>().join(", "),
        ));
    }
    b.push_str("end SumLocalExpB\n");
    std::fs::write(format!("{out}/SumLocalExpB.lean"), b).expect("write B");
    println!("\nwrote SumLocalExpA/B.lean for layer {l}, {k} nodes");
}
