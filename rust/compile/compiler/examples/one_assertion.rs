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

//! Emit the meaning lemma for **one** assertion, all the way down to input wires.
//!
//! The bounded experiment behind the specification bridge: if one `slice_wx` closes against
//! Lean's `addE`/`doubleE`, the remaining 1,047 are generation. Each cone is 118 nodes over 18
//! inputs, and every node gets one value lemma — shared nodes included, since a node used by
//! several assertions still only needs one.
//!
//! Usage: `one_assertion FILE.sidecar PATH_SUBSTRING OUT.lean`

use std::collections::{BTreeSet, HashMap};

use compile_compiler::cert::{self, ParsedNode};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = &args[1];
    let want = &args[2];
    let out_path = &args[3];
    let bytes = std::fs::read(path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    let s = cert::parse_sidecar(&bytes).expect("sidecar parses");

    let a = s
        .assertions
        .iter()
        .find(|a| a.paths.iter().any(|p| p.contains(want)))
        .unwrap_or_else(|| panic!("no assertion path contains {want:?}"));

    // Cone in topological order: operands before parents.
    let mut order: Vec<usize> = Vec::new();
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    // Stop at CSE boundaries when asked: a node with more than one parent becomes an opaque
    // variable rather than being expanded.  This is what the template machinery already does,
    // and the reason it does it -- expanding a DAG into a tree duplicates every shared subterm.
    let stop_shared = std::env::var("STOP_SHARED").is_ok();
    let mut refs: HashMap<usize, usize> = HashMap::new();
    for n in &s.nodes {
        if let ParsedNode::Sum { terms } = n {
            for (_, w0, w1) in terms {
                *refs.entry(*w0).or_default() += 1;
                *refs.entry(*w1).or_default() += 1;
            }
        }
    }
    fn visit2(
        n: usize,
        root: usize,
        nodes: &[ParsedNode],
        refs: &HashMap<usize, usize>,
        stop: bool,
        seen: &mut BTreeSet<usize>,
        order: &mut Vec<usize>,
        opaque: &mut BTreeSet<usize>,
    ) {
        if !seen.insert(n) {
            return;
        }
        let shared = stop && n != root && refs.get(&n).copied().unwrap_or(0) > 1;
        if shared {
            opaque.insert(n);
            order.push(n);
            return;
        }
        if let ParsedNode::Sum { terms } = &nodes[n] {
            for (_, w0, w1) in terms {
                visit2(*w0, root, nodes, refs, stop, seen, order, opaque);
                visit2(*w1, root, nodes, refs, stop, seen, order, opaque);
            }
        }
        order.push(n);
    }
    let mut opaque: BTreeSet<usize> = BTreeSet::new();
    visit2(a.asserted_node, a.asserted_node, &s.nodes, &refs, stop_shared,
        &mut seen, &mut order, &mut opaque);

    let layout: HashMap<usize, &str> =
        s.input_layout.iter().map(|(p, n)| (*p, n.as_str())).collect();

    let mut body = String::new();
    let mut inputs_used: Vec<(usize, String)> = Vec::new();
    for &n in &order {
        match &s.nodes[n] {
            ParsedNode::Input { position } => {
                let name = layout.get(position).copied().unwrap_or("?");
                inputs_used.push((*position, name.to_string()));
                body.push_str(&format!(
                    "  have v{n} : interpDag dag inputs {n} = inputs {position} :=\n    \
                     interpDag_input dag inputs {n} {position} (by rw [dag_len]; omega)\n      \
                     (by rw [toDag_getD_fn raw (Ecdsa2.consts F) nodeFn nodefn_ok (by rw [nodes_len]; omega)]; rfl)\n\
                     -- {name}\n"
                ));
            }
            ParsedNode::Sum { terms } if opaque.contains(&n) => {
                // Opaque: no value lemma, the rewrite chain leaves it as `interpDag … n`.
                body.push_str(&format!("  -- node {n} is shared; left opaque\n"));
            }
            ParsedNode::Sum { terms } => {
                let node_lit: Vec<String> = terms
                    .iter()
                    .map(|(k, w0, w1)| format!("⟨consts {k}, {w0}, {w1}⟩"))
                    .collect();
                let mut rhs = "0".to_string();
                for (k, w0, w1) in terms {
                    rhs = format!("({rhs} + consts {k} * interpDag dag inputs {w0} * interpDag dag inputs {w1})");
                }
                body.push_str(&format!(
                    "  have h{n} : dag.getD {n} (.input 0) = .sum [{}] := by\n    \
                     rw [toDag_getD_fn raw (Ecdsa2.consts F) nodeFn nodefn_ok (by rw [nodes_len]; omega)]\n    \
                     rfl\n  \
                     have v{n} : interpDag dag inputs {n} = {rhs} := by\n    \
                     rw [interpDag_sum inputs dag {n} _ h{n} (vs.sum_operands_lt {n} _ h{n})]\n    \
                     simp only [List.foldl_cons, List.foldl_nil]\n",
                    node_lit.join(", ")
                ));
            }
            ParsedNode::Assert0 { .. } => {}
        }
    }


    // Root-last, so each rewrite is already expressed in terms of already-rewritten operands.
    let rws: Vec<String> = order
        .iter()
        .rev()
        .filter(|n| !opaque.contains(n))
        .map(|n| format!("v{n}"))
        .collect();

    let file = format!(
        "-- Generated by `compile_compiler::cert::one_assertion`. Do not edit.\n\
         import quadcert.Ecdsa2Sound\nimport quadcert.Ecdsa2NodeChk\n\
         set_option maxRecDepth 4000000\n\
         set_option maxHeartbeats 4000000\n\n\
         /-!\n\
         # One assertion, expanded to input wires\n\n\
         Assertion node {} at wire ({},{}), paths {:?}.\n\
         Cone: {} nodes, {} of them sums, over {} distinct input positions.\n\n\
         Each sum node gets one value lemma from `interpDag_sum`; the operand-ordering side\n\
         condition comes from `ValidScheduling`, which `Ecdsa2Sound.valid` already supplies.\n\
         Rewriting the chain root-last turns `interpDag dag inputs {}` into a polynomial in\n\
         `inputs`.\n\
         -/\n\n\
         namespace Ecdsa2.OneAssertion\n\n\
         open Quadcert Quadcert.Gen.Ecdsa2\n\n\
         variable {{F : Type}} [Field F]\n\n\
         /-- Building the chain at all: every `getD` hypothesis and every value lemma of the\n\
         cone.  The `getD`s are the risk -- `raw.nodes` is an append of 27 chunks, so reducing\n\
         `getD n` allocates a cons per element traversed. -/\n\
         theorem chain_ring (inputs : Nat → F) :\n    \
         interpDag (raw.toDag (Ecdsa2.consts F)) inputs {} \n      \
         - interpDag (raw.toDag (Ecdsa2.consts F)) inputs {} = 0 := by\n  \
         set dag := raw.toDag (consts F) with hdag\n  \
         set consts := Ecdsa2.consts F with hconsts\n  \
         have vs := Ecdsa2.valid (F := F) inputs\n  \
         have dag_len : dag.length = 26939 := by\n    \
         rw [hdag]; simp only [RawCircuit.toDag, List.length_map]; exact nodes_len\n\
         {body}  \
         rw [{}]\n  \
         ring\n\n\
         end Ecdsa2.OneAssertion\n",
        a.asserted_node,
        a.wire_layer,
        a.wire_index,
        a.paths,
        order.len(),
        order
            .iter()
            .filter(|n| matches!(s.nodes[**n], ParsedNode::Sum { .. }))
            .count(),
        inputs_used.len(),
        a.asserted_node,
        a.asserted_node,
        a.asserted_node,
        rws.join(",\n    "),
    );
    std::fs::write(out_path, &file).unwrap_or_else(|e| panic!("write {out_path}: {e}"));
    println!(
        "wrote {out_path}: assertion {} @ ({},{}), cone {} nodes, {} inputs",
        a.asserted_node,
        a.wire_layer,
        a.wire_index,
        order.len(),
        inputs_used.len()
    );
    println!("inputs: {:?}", inputs_used);
}
