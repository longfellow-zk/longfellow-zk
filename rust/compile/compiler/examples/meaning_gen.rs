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

//! Meaning lemmas: each assertion's DAG node, expanded to a statement about input wires.
//!
//! One lemma per assertion whose cone is small enough to expand outright. Every node of the cone
//! gets a `getD` (through the bisection, so O(log n)) and an `interpDag_sum` value lemma; the
//! chain is rewritten into the hypothesis and `linear_combination` finishes.
//!
//! The goal for each assertion is chosen by its scope path, so the theorem reads in the circuit
//! author's vocabulary rather than in wire positions. Paths whose cones are large -- the bit
//! reconstructions and the 256-bit comparisons at ~2,300 nodes, and the loop rounds at 118 --
//! are skipped here; they need the intermediate-matching route.
//!
//! Usage: `meaning_gen FILE.sidecar OUT.lean`

use std::collections::{BTreeSet, HashMap};

use compile_compiler::cert::{self, ParsedNode};

/// P-256's field characteristic.
const P_HEX: &str = "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff";

fn hex_of(bytes: &[u8]) -> String {
    let s: String = bytes.iter().rev().map(|b| format!("{b:02x}")).collect();
    let t = s.trim_start_matches('0').to_string();
    if t.is_empty() { "0".to_string() } else { t }
}

fn main() {
    let path = std::env::args().nth(1).expect("usage: meaning_gen FILE.sidecar OUT.lean");
    let out_path = std::env::args().nth(2).expect("usage: meaning_gen FILE.sidecar OUT.lean");
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    let s = cert::parse_sidecar(&bytes).expect("sidecar parses");

    let p = u256_from_hex(P_HEX);
    let layout: HashMap<usize, &str> =
        s.input_layout.iter().map(|(p, n)| (*p, n.as_str())).collect();
    let pos_of: HashMap<&str, usize> =
        s.input_layout.iter().map(|(p, n)| (n.as_str(), *p)).collect();

    // Constant values, as Lean expressions: small ones as themselves, `p - n` as `-n`.
    let const_expr = |k: usize| -> (String, String) {
        let v = u256_from_bytes(&s.constants[k]);
        let neg = sub_u256(p, v);
        if cmp_u256(v, neg) <= std::cmp::Ordering::Equal {
            (
                format!("(((0x{} : Nat)) : F)", hex_of(&s.constants[k])),
                format!("consts_pos {k} 0x{} (by rfl)", hex_of(&s.constants[k])),
            )
        } else {
            let h = hex_u256(neg);
            (
                format!("-(((0x{h} : Nat)) : F)"),
                format!("consts_neg {k} 0x{h} (by rfl) (by norm_num)"),
            )
        }
    };

    let cone = |root: usize| -> Vec<usize> {
        let mut order = Vec::new();
        let mut seen = BTreeSet::new();
        fn visit(n: usize, nodes: &[ParsedNode], seen: &mut BTreeSet<usize>, order: &mut Vec<usize>) {
            if !seen.insert(n) {
                return;
            }
            if let ParsedNode::Sum { terms } = &nodes[n] {
                for (_, w0, w1) in terms {
                    visit(*w0, nodes, seen, order);
                    visit(*w1, nodes, seen, order);
                }
            }
            order.push(n);
        }
        visit(root, &s.nodes, &mut seen, &mut order);
        order
    };

    // `DUMP_LAYOUT=1` prints the input layout, one `position name` per line. The layout is the
    // one place meaning is *chosen* rather than checked, so the generators read it here rather
    // than hard-coding positions.
    if std::env::var("DUMP_LAYOUT").is_ok() {
        let mut l: Vec<_> = s.input_layout.iter().collect();
        l.sort_by_key(|(p, _)| *p);
        for (p, n) in l {
            println!("{p} {n}");
        }
        return;
    }

    // `DUMP_ASSERTS=1` prints `index node path` per assertion, in the order `raw.toRecs` holds
    // them. The assembly needs it to name the hypothesis a given meaning lemma consumes: the
    // bridges destructure `assertions_zero` once per chunk (see `E2Digits`), so a lemma about
    // assertion `i` is discharged by the `i`-th name in its chunk.
    if std::env::var("DUMP_ASSERTS").is_ok() {
        for (i, a) in s.assertions.iter().enumerate() {
            println!(
                "{i} {} {}",
                a.asserted_node,
                a.paths.first().map(String::as_str).unwrap_or("")
            );
        }
        return;
    }

    // `DUMP_SHALLOW=id,id,…` prints a node's own `sum` terms and nothing below them. The
    // comparator roots cannot be dumped as cones -- their cone is the whole 256-bit comparison
    // and the recursive walk overflows the stack, which is the same reason those certificates
    // are tree-structured in the first place. One level is all the closing lemma needs.
    if let Ok(want) = std::env::var("DUMP_SHALLOW") {
        for tok in want.split(',') {
            let n: usize = tok.trim().parse().expect("DUMP_SHALLOW must be node ids");
            match &s.nodes[n] {
                ParsedNode::Sum { terms } => {
                    print!("{{\"id\": {n}, \"sum\": [");
                    for (j, (k, w0, w1)) in terms.iter().enumerate() {
                        if j > 0 {
                            print!(", ");
                        }
                        print!("[\"{}\", {w0}, {w1}, {k}]", hex_of(&s.constants[*k as usize]));
                    }
                    println!("]}}");
                }
                ParsedNode::Input { position } => println!(
                    "{{\"id\": {n}, \"input\": {position}, \"name\": \"{}\"}}",
                    layout.get(position).copied().unwrap_or("?")
                ),
                ParsedNode::Assert0 { .. } => println!("{{\"id\": {n}, \"assert0\": true}}"),
            }
        }
        return;
    }

    // The same cone dump, but rooted at an arbitrary node rather than at an assertion. The
    // table-output wires (the mux coordinates the loop rounds stop at, the bit wires the
    // bit-sums stop at) are interior nodes, not assertion roots, so `DUMP_CONE` cannot reach
    // them. Emitting `"root"` the same way keeps the Python side identical.
    // Takes a comma-separated list and prints one JSON object per line, so a round's three mux
    // wires cost one sidecar parse rather than three.
    if let Ok(want) = std::env::var("DUMP_NODE") {
        for tok in want.split(',') {
            let root: usize = tok.trim().parse().expect("DUMP_NODE must be node ids");
            let order = cone(root);
            print!("{{\"root\": {root}, \"nodes\": [");
            for (i, &n) in order.iter().enumerate() {
                if i > 0 {
                    print!(", ");
                }
                match &s.nodes[n] {
                    ParsedNode::Input { position } => print!(
                        "{{\"id\": {n}, \"input\": {position}, \"name\": \"{}\"}}",
                        layout.get(position).copied().unwrap_or("?")
                    ),
                    ParsedNode::Sum { terms } => {
                        print!("{{\"id\": {n}, \"sum\": [");
                        for (j, (k, w0, w1)) in terms.iter().enumerate() {
                            if j > 0 {
                                print!(", ");
                            }
                            print!("[\"{}\", {w0}, {w1}, {k}]", hex_of(&s.constants[*k as usize]));
                        }
                        print!("]}}");
                    }
                    ParsedNode::Assert0 { .. } => {}
                }
            }
            println!("]}}");
        }
        return;
    }

    // `DUMP_CONE=path` prints one assertion's cone as JSON, for the polynomial algebra that
    // the mod-p certificates need. The circuit's fused polynomial agrees with a directly
    // interpolated one only modulo `p`, so `ring` alone cannot reconcile them.
    if let Ok(want) = std::env::var("DUMP_CONE") {
        let idx: usize = std::env::var("DUMP_IDX")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(0);
        let a = s
            .assertions
            .iter()
            .filter(|a| a.paths.iter().any(|p| p.contains(&want)))
            .nth(idx)
            .expect("no such path/index");
        let order = cone(a.asserted_node);
        print!("{{\"root\": {}, \"nodes\": [", a.asserted_node);
        for (i, &n) in order.iter().enumerate() {
            if i > 0 {
                print!(", ");
            }
            match &s.nodes[n] {
                ParsedNode::Input { position } => print!(
                    "{{\"id\": {n}, \"input\": {position}, \"name\": \"{}\"}}",
                    layout.get(position).copied().unwrap_or("?")
                ),
                ParsedNode::Sum { terms } => {
                    print!("{{\"id\": {n}, \"sum\": [");
                    for (j, (k, w0, w1)) in terms.iter().enumerate() {
                        if j > 0 {
                            print!(", ");
                        }
                        print!(
                            "[\"{}\", {w0}, {w1}, {k}]",
                            hex_of(&s.constants[*k as usize])
                        );
                    }
                    print!("]}}");
                }
                ParsedNode::Assert0 { .. } => {}
            }
        }
        println!("]}}");
        return;
    }

    // Which circuit these lemmas are about. The generated modules name a circuit-specific
    // `consts`, `valid` and `nodes_len`, so this cannot stay hardcoded once there is more than
    // one target. `NAME=Sha` emits into `Sha.Meaning` against `quadcert.Sha*`.
    let name = std::env::var("NAME").unwrap_or_else(|_| "Ecdsa2".to_string());
    // The shared support module (`consts_pos`, `consts_neg`, the `p256` abbrev) is named per
    // circuit and is not derivable from `NAME`: ECDSA2's is `E2Meaning`.
    let support = std::env::var("SUPPORT").unwrap_or_else(|_| "E2Meaning".to_string());
    let nodes_len = s.nodes.len();

    // The per-node value chain, shared by the assertion lemmas and by `PROBE_Z`. One `getD`
    // and one `interpDag` value lemma per cone node, in topological order; rewriting the whole
    // list into a hypothesis inlines the cone.
    let build_chain = |order: &[usize]| -> (String, BTreeSet<usize>) {
        let mut chain = String::new();
        let mut cs: BTreeSet<usize> = BTreeSet::new();
        for &n in order {
            match &s.nodes[n] {
                ParsedNode::Input { position } => chain.push_str(&format!(
                    "  have v{n} : interpDag dag inputs {n} = inputs {position} :=\n    \
                     interpDag_input dag inputs {n} {position} (by rw [dag_len]; omega)\n      \
                     (by rw [toDag_getD_fn raw ({name}.consts F) nodeFn nodefn_ok \
                     (by rw [nodes_len]; omega)]; rfl)\n"
                )),
                ParsedNode::Sum { terms } => {
                    let lit: Vec<String> = terms
                        .iter()
                        .map(|(k, w0, w1)| {
                            cs.insert(*k as usize);
                            format!("\u{27e8}{name}.consts F {k}, {w0}, {w1}\u{27e9}")
                        })
                        .collect();
                    let mut rhs = "0".to_string();
                    for (k, w0, w1) in terms {
                        rhs = format!(
                            "({rhs} + {name}.consts F {k} * interpDag dag inputs {w0} \
                             * interpDag dag inputs {w1})"
                        );
                    }
                    chain.push_str(&format!(
                        "  have h{n} : dag.getD {n} (.input 0) = .sum [{}] := by\n    \
                         rw [toDag_getD_fn raw ({name}.consts F) nodeFn nodefn_ok \
                         (by rw [nodes_len]; omega)]\n    rfl\n  \
                         have v{n} : interpDag dag inputs {n} = {rhs} := by\n    \
                         rw [interpDag_sum inputs dag {n} _ h{n} (vs.sum_operands_lt {n} _ h{n})]\n    \
                         simp only [List.foldl_cons, List.foldl_nil]\n",
                        lit.join(", ")
                    ));
                }
                ParsedNode::Assert0 { .. } => {}
            }
        }
        (chain, cs)
    };

    let mut body = String::new();
    let mut emitted = 0usize;
    let mut skipped: HashMap<String, usize> = HashMap::new();

    // `PROBE_Z=<node>` emits one module measuring the *chain* alone: every `have`, the
    // constants rewrites and the full inlining `rw ... at h`, with no `ring` at the end. The
    // ring cost is measured separately against a standalone polynomial identity, and the two
    // together bound a real meaning lemma. Splitting them is the only way to get a number for
    // the 266-node wrapping-sum cones before the goal side of those lemmas exists.
    if let Ok(want) = std::env::var("PROBE_Z") {
        let node: usize = want.trim().parse().expect("PROBE_Z must be a node id");
        let order = cone(node);
        let (chain, cs) = build_chain(&order);
        let rws: Vec<String> = order.iter().rev().map(|n| format!("v{n}")).collect();
        let cnames: Vec<String> = cs.iter().map(|k| format!("ck{k}")).collect();
        let cdefs: String = cs
            .iter()
            .map(|k| format!("  have ck{k} : {name}.consts F {k} = {} := {}\n",
                const_expr(*k).0, const_expr(*k).1))
            .collect();
        let reads_one = order
            .iter()
            .any(|n| matches!(&s.nodes[*n], ParsedNode::Input { position } if *position == 0));
        let file = format!(
            "-- Generated by `meaning_gen PROBE_Z={node}`. Chain-cost probe; not a real lemma.\n\
             import quadcert.{support}\n\
             set_option maxRecDepth 4000000\nset_option maxHeartbeats 4000000\n\n\
             namespace {name}.Probe\n\n\
             open Quadcert Quadcert.Gen.{name} {name}.Meaning\n\n\
             variable {{F : Type}} [Field F] [CharP F {name}.Meaning.p256]\n\n\
             /-- Cone of node {node}: {ncone} nodes, {nconst} distinct constants. -/\n\
             theorem probe_{node} (inputs : Nat \u{2192} F) (hone : inputs 0 = 1)\n    \
             (h : interpDag (raw.toDag ({name}.consts F)) inputs {node} = 0) : True := by\n  \
             set dag := raw.toDag ({name}.consts F) with hdag\n  \
             have vs := {name}.valid (F := F) inputs\n  \
             have dag_len : dag.length = {nodes_len} := by\n    \
             rw [hdag]; simp only [RawCircuit.toDag, List.length_map]; exact nodes_len\n\
             {chain}{cdefs}  \
             rw [{rw}] at h\n  \
             rw [{cn}] at h\n  \
             {one_rw}try push_cast at h\n  \
             trivial\n\n\
             end {name}.Probe\n",
            ncone = order.len(),
            nconst = cs.len(),
            rw = rws.join(", "),
            cn = cnames.join(", "),
            one_rw = if reads_one { "rw [show inputs 0 = 1 from hone] at h\n  " } else { "" },
        );
        std::fs::write(&out_path, &file).unwrap_or_else(|e| panic!("write {out_path}: {e}"));
        println!("probe for node {node}: {} cone nodes, {} constants -> {out_path}",
            order.len(), cs.len());
        return;
    }

    for a in &s.assertions {
        let path = a.paths.first().map(String::as_str).unwrap_or("");
        let order = cone(a.asserted_node);

        // Which inputs does the cone read, in layout terms?
        let names: Vec<(&str, usize)> = order
            .iter()
            .filter_map(|n| match &s.nodes[*n] {
                ParsedNode::Input { position } => {
                    Some((layout.get(position).copied().unwrap_or("?"), *position))
                }
                _ => None,
            })
            .collect();
        let named = |want: &str| -> Option<usize> {
            names.iter().find(|(n, _)| *n == want).map(|(_, p)| *p)
        };

        // The clause, by scope path.
        let goal: Option<String> = if path.ends_with("/rxinv") || path.ends_with("/pkxinv")
            || path.ends_with("/yinv")
        {
            let inv = path.rsplit('/').next().unwrap();
            let other = names.iter().find(|(n, _)| *n != "one" && *n != inv).map(|(_, p)| *p);
            match (named(inv), other) {
                (Some(i), Some(o)) => Some(format!("inputs {o} * inputs {i} = 1")),
                _ => None,
            }
        } else if path.ends_with("/ax_zero") || path.ends_with("/az_zero") {
            names.first().map(|(_, p)| format!("inputs {p} = 0"))
        } else if path.contains("is_on_curve") {
            // (x, y) are the two non-`one` inputs, x first by position.
            let mut xs: Vec<usize> =
                names.iter().filter(|(n, _)| *n != "one").map(|(_, p)| *p).collect();
            xs.sort_unstable();
            if xs.len() == 2 {
                Some(format!(
                    "inputs {y} * inputs {y} \
                     = inputs {x} * inputs {x} * inputs {x} - 3 * inputs {x} + (0x{B} : F)",
                    x = xs[0],
                    y = xs[1],
                    B = "5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b"
                ))
            } else {
                None
            }
        } else if path == "is_boolean" || path.ends_with("/is_boolean") {
            // `x - x * x = 0`. In a field that factors, so the clause is the disjunction; the
            // factoring is done once by `isBit_of_zero_raw` rather than in 6,656 proofs.
            names
                .iter()
                .find(|(n, _)| *n != "one")
                .map(|(_, p)| format!("inputs {p} = 0 ∨ inputs {p} = 1"))
        } else if path.ends_with("/valid_index") {
            // The range interpolant vanishes exactly on the eight lookup nodes;
            // `Lagrange.isDigit_of_range` factors it. The circuit's copy of that polynomial is
            // fused differently, so `linear_combination` reconciles the two.
            names
                .iter()
                .find(|(n, _)| n.starts_with("ers"))
                .map(|(_, p)| format!("ECDSA2.IsDigit (inputs {p})"))
        } else {
            None
        };

        let is_digit = goal.as_deref().is_some_and(|g| g.starts_with("ECDSA2.IsDigit"));
        let is_bool = path == "is_boolean" || path.ends_with("/is_boolean");
        let bool_pos = names.iter().find(|(n, _)| *n != "one").map(|(_, p)| *p).unwrap_or(0);
        let digit_pos = names
            .iter()
            .find(|(n, _)| n.starts_with("ers"))
            .map(|(_, p)| *p)
            .unwrap_or(0);

        let Some(goal) = goal else {
            *skipped.entry(kind_of(path)).or_default() += 1;
            continue;
        };
        if order.len() > 64 {
            *skipped.entry(format!("{} (cone {})", kind_of(path), order.len())).or_default() += 1;
            continue;
        }

        let (chain, cs) = build_chain(&order);
        let rws: Vec<String> = order.iter().rev().map(|n| format!("v{n}")).collect();
        let cnames: Vec<String> = cs.iter().map(|k| format!("ck{k}")).collect();
        let cdefs: String = cs
            .iter()
            .map(|k| {
                let (_, proof) = const_expr(*k);
                format!("  have ck{k} : {name}.consts F {k} = {} := {proof}\n", const_expr(*k).0)
            })
            .collect();

        body.push_str(&format!(
            "\n/-- `{path}` -/\ntheorem m{node} (inputs : Nat → F) (hone : inputs 0 = 1)\n    \
             (h : interpDag (raw.toDag ({name}.consts F)) inputs {node} = 0) :\n    \
             {goal} := by\n  \
             {refine}set dag := raw.toDag ({name}.consts F) with hdag\n  \
             have vs := {name}.valid (F := F) inputs\n  \
             have dag_len : dag.length = {nodes_len} := by\n    \
             rw [hdag]; simp only [RawCircuit.toDag, List.length_map]; exact nodes_len\n\
             {chain}{cdefs}  \
             rw [{rw}] at h\n  \
             rw [{cn}] at h\n  \
             {one_rw}try push_cast at h\n  \
             linear_combination h\n",
            node = a.asserted_node,
            nodes_len = nodes_len,
            name = name,
            rw = rws.join(", "),
            cn = cnames.join(", "),
            // Only when the cone actually reads position 0; `ax_zero`'s cone is the input alone.
            refine = if is_digit {
                format!(
                    "refine ECDSA2.RangeCert.isDigit_of_zero_raw (inputs {digit_pos}) ?_\n  "
                )
            } else if is_bool {
                format!("refine SHA256F.isBit_of_zero_raw (inputs {bool_pos}) ?_\n  ")
            } else {
                String::new()
            },
            one_rw = if names.iter().any(|(_, p)| *p == 0) {
                "rw [show inputs 0 = 1 from hone] at h\n  "
            } else {
                ""
            },
        ));
        emitted += 1;
    }

    let file = format!(
        "-- Generated by `compile_compiler::cert::meaning_gen`. Do not edit.\n\
         import quadcert.{support}\nimport ECDSA.RangeCert\n\
         set_option maxRecDepth 4000000\nset_option maxHeartbeats 4000000\n\n\
         /-!\n# Meaning lemmas, generated\n\n\
         One per assertion whose cone expands outright. See `E2Meaning` for the shape.\n-/\n\n\
         namespace {name}.Meaning\n\n\
         open Quadcert Quadcert.Gen.{name}\n\n\
         variable {{F : Type}} [Field F] [CharP F p256]\n\
         {body}\nend {name}.Meaning\n"
    );
    std::fs::write(&out_path, &file).unwrap_or_else(|e| panic!("write {out_path}: {e}"));
    println!("emitted {emitted} meaning lemmas to {out_path}");
    let mut sk: Vec<_> = skipped.into_iter().collect();
    sk.sort();
    for (k, n) in sk {
        println!("  skipped {n:>4}  {k}");
    }
    let _ = pos_of;
}

fn kind_of(path: &str) -> String {
    path.rsplit('/').next().unwrap_or(path).to_string()
}

// --- minimal 256-bit helpers (the sidecar holds constants as little-endian bytes) ---
type U256 = [u64; 4];

fn u256_from_bytes(b: &[u8]) -> U256 {
    let mut r = [0u64; 4];
    for (i, chunk) in b.chunks(8).take(4).enumerate() {
        let mut w = [0u8; 8];
        w[..chunk.len()].copy_from_slice(chunk);
        r[i] = u64::from_le_bytes(w);
    }
    r
}

fn u256_from_hex(h: &str) -> U256 {
    let mut bytes = vec![0u8; 32];
    let h = format!("{:0>64}", h);
    for i in 0..32 {
        bytes[31 - i] = u8::from_str_radix(&h[i * 2..i * 2 + 2], 16).unwrap();
    }
    u256_from_bytes(&bytes)
}

fn cmp_u256(a: U256, b: U256) -> std::cmp::Ordering {
    for i in (0..4).rev() {
        match a[i].cmp(&b[i]) {
            std::cmp::Ordering::Equal => {}
            o => return o,
        }
    }
    std::cmp::Ordering::Equal
}

fn sub_u256(a: U256, b: U256) -> U256 {
    let mut r = [0u64; 4];
    let mut borrow = 0i128;
    for i in 0..4 {
        let d = a[i] as i128 - b[i] as i128 - borrow;
        if d < 0 {
            r[i] = (d + (1i128 << 64)) as u64;
            borrow = 1;
        } else {
            r[i] = d as u64;
            borrow = 0;
        }
    }
    r
}

fn hex_u256(v: U256) -> String {
    let s: String = (0..4).rev().map(|i| format!("{:016x}", v[i])).collect();
    let t = s.trim_start_matches('0').to_string();
    if t.is_empty() { "0".to_string() } else { t }
}
