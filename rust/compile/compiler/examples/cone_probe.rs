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

//! The cone of one assertion: every DAG node it depends on, down to inputs.
//!
//! This is the measurement that decides whether the spec bridge is a bounded per-assertion job.
//! The template machinery stops at CSE boundaries, so an assertion's *template* is small; what
//! matters for the meaning lemma is how big its transitive cone is, how much of that cone is
//! shared with other assertions, and how many distinct input positions it reaches.
//!
//! Usage: `cone_probe FILE.sidecar [PATH_SUBSTRING]`

use std::collections::{BTreeSet, HashMap};

use compile_compiler::cert::{self, ParsedNode};

fn main() {
    let path = std::env::args().nth(1).expect("usage: cone_probe FILE.sidecar [PATH]");
    let want = std::env::args().nth(2).unwrap_or_else(|| "slice_wx".to_string());
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    let s = cert::parse_sidecar(&bytes).expect("sidecar parses");

    // How many parents does each node have? Anything above one is a CSE boundary.
    let mut refs: HashMap<usize, usize> = HashMap::new();
    for n in &s.nodes {
        if let ParsedNode::Sum { terms } = n {
            for (_, w0, w1) in terms {
                *refs.entry(*w0).or_default() += 1;
                *refs.entry(*w1).or_default() += 1;
            }
        }
    }

    let cone = |root: usize| -> BTreeSet<usize> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![root];
        while let Some(n) = stack.pop() {
            if !seen.insert(n) {
                continue;
            }
            if let ParsedNode::Sum { terms } = &s.nodes[n] {
                for (_, w0, w1) in terms {
                    stack.push(*w0);
                    stack.push(*w1);
                }
            }
        }
        seen
    };

    let layout: HashMap<usize, &str> =
        s.input_layout.iter().map(|(p, n)| (*p, n.as_str())).collect();

    // `NODES=1,2,3` dumps specific nodes instead of scanning assertions.
    if let Ok(list) = std::env::var("NODES") {
        for tok in list.split(',') {
            let n: usize = tok.trim().parse().expect("node index");
            match &s.nodes[n] {
                ParsedNode::Input { position } => println!(
                    "node {n}: input {position} ({})",
                    layout.get(position).copied().unwrap_or("?")
                ),
                ParsedNode::Sum { terms } => println!(
                    "node {n}: sum {:?}  [refs {}]",
                    terms,
                    refs.get(&n).copied().unwrap_or(0)
                ),
                ParsedNode::Assert0 { w } => println!("node {n}: assert0 {w}"),
            }
        }
        return;
    }

    // `SPLIT=path` reports the cone split at the mux boundary: nodes that depend on the digit
    // wire are the table lookup, everything else is the EC arithmetic. Expanding only the latter
    // keeps the polynomial in six variables (the accumulator and the selected point) instead of
    // eighteen, and drops the degree-7 interpolant entirely.
    if let Ok(want) = std::env::var("SPLIT") {
        // The mux output is what the EC arithmetic consumes: a node whose cone reaches the digit
        // and the table's points, but *not* the accumulator. Everything above it mixes in the
        // accumulator. Cutting there leaves the EC part in six variables -- the accumulator and
        // the selected point -- instead of eighteen, and drops the degree-7 interpolant.
        let acc: std::collections::HashSet<usize> = s
            .input_layout
            .iter()
            .filter(|(_, n)| n.starts_with("intx") || n.starts_with("inty") || n.starts_with("intz"))
            .map(|(p, _)| *p)
            .collect();
        for a in s.assertions.iter().filter(|a| a.paths.iter().any(|p| p.contains(&want))).take(2) {
            let c = cone(a.asserted_node);
            let touches_acc = |n: usize| -> bool {
                cone(n).iter().any(|m| match &s.nodes[*m] {
                    ParsedNode::Input { position } => acc.contains(position),
                    _ => false,
                })
            };
            let pure: std::collections::HashSet<usize> =
                c.iter().copied().filter(|n| !touches_acc(*n)).collect();
            // Maximal accumulator-free nodes: a parent in the cone does touch the accumulator.
            let mut boundary: Vec<usize> = pure
                .iter()
                .copied()
                .filter(|n| {
                    c.iter().any(|p| {
                        touches_acc(*p)
                            && matches!(&s.nodes[*p], ParsedNode::Sum { terms }
                                if terms.iter().any(|(_, w0, w1)| w0 == n || w1 == n))
                    })
                })
                .collect();
            boundary.sort_unstable();
            println!(
                "assertion {} @ ({},{}): cone {}, accumulator-free {}, EC-only {}, boundary {:?}",
                a.asserted_node,
                a.wire_layer,
                a.wire_index,
                c.len(),
                pure.len(),
                c.len() - pure.len(),
                boundary
            );
        }
        return;
    }

    let mut printed = 0usize;
    let mut total: Vec<usize> = Vec::new();
    for a in &s.assertions {
        if !a.paths.iter().any(|p| p.contains(&want)) {
            continue;
        }
        let c = cone(a.asserted_node);
        total.push(c.len());
        if printed < 3 {
            printed += 1;
            let inputs: Vec<&str> = c
                .iter()
                .filter_map(|n| match &s.nodes[*n] {
                    ParsedNode::Input { position } => {
                        Some(layout.get(position).copied().unwrap_or("?"))
                    }
                    _ => None,
                })
                .collect();
            let sums = c
                .iter()
                .filter(|n| matches!(s.nodes[**n], ParsedNode::Sum { .. }))
                .count();
            let shared = c.iter().filter(|n| refs.get(n).copied().unwrap_or(0) > 1).count();
            println!(
                "assertion node {} @ ({},{}) {:?}\n  \
                 cone {} nodes: {sums} sum, {} input, {shared} shared (refcount > 1)\n  \
                 template {} with {} mapped nodes\n  inputs: {:?}",
                a.asserted_node,
                a.wire_layer,
                a.wire_index,
                a.paths,
                c.len(),
                c.len() - sums,
                a.template,
                a.mapping.len(),
                inputs
            );
        }
    }
    if total.is_empty() {
        println!("no assertion path contains {want:?}");
        return;
    }
    total.sort_unstable();
    println!(
        "\n{} assertions matching {want:?}: cone min {} median {} max {}",
        total.len(),
        total[0],
        total[total.len() / 2],
        total[total.len() - 1]
    );

    // The whole-circuit picture: one value lemma per sum node, shared across every assertion
    // that uses it.
    let nsum = s
        .nodes
        .iter()
        .filter(|n| matches!(n, ParsedNode::Sum { .. }))
        .count();
    let union: BTreeSet<usize> = s
        .assertions
        .iter()
        .flat_map(|a| cone(a.asserted_node))
        .collect();
    println!(
        "circuit: {} sum nodes, {} reachable from some assertion ({:.1}%)",
        nsum,
        union.len(),
        union.len() as f64 / s.nodes.len() as f64 * 100.0
    );
}
