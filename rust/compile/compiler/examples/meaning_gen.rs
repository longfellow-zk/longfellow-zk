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

use std::collections::{BTreeMap, BTreeSet, HashMap};

use compile_compiler::{
    cert::{self, ParsedNode, TemplateNode},
    cone::Cones,
};

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
    // Which circuit these lemmas are about. The generated modules name a circuit-specific
    // `consts`, `valid` and `nodes_len`, so this cannot stay hardcoded once there is more than
    // one target. `NAME=Sha` emits into `Sha.Meaning` against `quadcert.Sha*`.
    let name = std::env::var("NAME").unwrap_or_else(|_| "Ecdsa2".to_string());
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

    // One assertion's cone as JSON. Shared by `DUMP_CONE` and `DUMP_CONES` so the single-cone
    // and batch paths cannot drift apart.
    let cone_json = |root: usize| -> String {
        let order = cone(root);
        let mut out = format!("{{\"root\": {root}, \"nodes\": [");
        for (i, &n) in order.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            match &s.nodes[n] {
                ParsedNode::Input { position } => out.push_str(&format!(
                    "{{\"id\": {n}, \"input\": {position}, \"name\": \"{}\"}}",
                    layout.get(position).copied().unwrap_or("?")
                )),
                ParsedNode::Sum { terms } => {
                    out.push_str(&format!("{{\"id\": {n}, \"sum\": ["));
                    for (j, (k, w0, w1)) in terms.iter().enumerate() {
                        if j > 0 {
                            out.push_str(", ");
                        }
                        out.push_str(&format!(
                            "[\"{}\", {w0}, {w1}, {k}]",
                            hex_of(&s.constants[*k as usize])
                        ));
                    }
                    out.push_str("]}");
                }
                ParsedNode::Assert0 { .. } => {}
            }
        }
        out.push_str("]}");
        out
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

    // `DUMP_TEMPLATES=1` counts distinct assertion shapes and how many assertions instantiate
    // each. Assertion count alone does not predict generation cost: anything computed per
    // *shape* and instantiated through `ParsedAssertion.mapping` scales with this histogram
    // rather than with `assertions.len()`.
    if std::env::var("DUMP_TEMPLATES").is_ok() {
        let mut hist: HashMap<usize, (usize, String)> = HashMap::new();
        for a in &s.assertions {
            let e = hist.entry(a.template).or_insert((0, String::new()));
            e.0 += 1;
            if e.1.is_empty() {
                if let Some(path) = a.paths.first() {
                    e.1 = path.clone();
                }
            }
        }
        let mut rows: Vec<(usize, (usize, String))> = hist.into_iter().collect();
        rows.sort_by(|a, b| b.1 .0.cmp(&a.1 .0).then(a.0.cmp(&b.0)));
        println!(
            "{} assertions, {} templates declared, {} instantiated",
            s.assertions.len(),
            s.templates.len(),
            rows.len()
        );
        for (t, (n, path)) in &rows {
            println!(
                "  template {t:4}  {n:5} assertions  {:4} nodes  {:3} leaves  {path}",
                s.templates[*t].nodes.len(),
                s.templates[*t].nleaves
            );
        }
        return;
    }

    // `DUMP_TEMPLATE=<n>` prints one shape's nodes against a representative instance: for each
    // template node, the DAG node it maps to and what that node is. The `LEAF` rows are the
    // shape's holes, and the question they answer is whether the compiler's CSE boundary
    // already lands where the specification has names -- if a loop shape's leaves are the mux
    // outputs and the accumulator coordinates, the cut is derivable; if they are interior
    // arithmetic, a frontier has to be computed below them.
    if let Ok(want) = std::env::var("DUMP_TEMPLATE") {
        let t: usize = want.trim().parse().expect("DUMP_TEMPLATE must be a template index");
        let tmpl = s
            .templates
            .get(t)
            .unwrap_or_else(|| panic!("no template {t}; there are {}", s.templates.len()));
        let (ai, a) = s
            .assertions
            .iter()
            .enumerate()
            .find(|(_, a)| a.template == t)
            .unwrap_or_else(|| panic!("no assertion instantiates template {t}"));
        let ninst = s.assertions.iter().filter(|a| a.template == t).count();
        println!(
            "template {t}: {} nodes, {} leaves, {ninst} assertions",
            tmpl.nodes.len(),
            tmpl.nleaves
        );
        println!(
            "representative: assertion {ai}, asserted node {}, path {}",
            a.asserted_node,
            a.paths.first().map(String::as_str).unwrap_or("-")
        );
        let describe = |n: usize| -> String {
            match s.nodes.get(n) {
                Some(ParsedNode::Input { position }) => match layout.get(position) {
                    Some(nm) => format!("input {position} \"{nm}\""),
                    None => format!("input {position}"),
                },
                Some(ParsedNode::Sum { terms }) => format!("sum[{} terms]", terms.len()),
                Some(ParsedNode::Assert0 { w }) => format!("assert0 w={w}"),
                None => "<node out of range>".to_string(),
            }
        };
        for (i, node) in tmpl.nodes.iter().enumerate() {
            let dag = a.mapping.get(i).copied();
            let wire = dag
                .and_then(|d| s.node_wires.get(d).copied().flatten())
                .map(|(l, j)| format!("({l},{j})"))
                .unwrap_or_else(|| "-".to_string());
            let (kind, tag) = match node {
                TemplateNode::Leaf(k) => (format!("Leaf({k})"), "LEAF"),
                TemplateNode::Sum(ts) => {
                    let ops: Vec<String> =
                        ts.iter().map(|(k, x, y)| format!("({k},{x},{y})")).collect();
                    (format!("Sum[{}]", ops.join(",")), "")
                }
            };
            println!(
                "  {i:>4} {tag:<4} {:<46} dag {:<7} wire {:<10} {}",
                kind,
                dag.map(|d| d.to_string()).unwrap_or_else(|| "-".to_string()),
                wire,
                dag.map(|d| describe(d)).unwrap_or_default()
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
        println!("{}", cone_json(a.asserted_node));
        return;
    }

    // `DUMP_CONES=<dir>` writes every cone in one pass, in exactly the format `DUMP_CONE`
    // prints. `DUMP_CONES_PATHS=slice_wx,slice_wy` reproduces the per-path indexing the shell
    // drivers rely on -- `slice_wx_0.json` is what `DUMP_CONE=slice_wx DUMP_IDX=0` emitted --
    // so a driver stops paying one process spawn and one sidecar parse per assertion. With no
    // paths given, every assertion is written as `assert_<i>.json` under its global index.
    if let Ok(dir) = std::env::var("DUMP_CONES") {
        std::fs::create_dir_all(&dir).unwrap_or_else(|e| panic!("create {dir}: {e}"));
        let stem_of = |x: &str| -> String {
            x.chars()
                .map(|c| {
                    if c.is_ascii_alphanumeric() || c == '.' || c == '_' || c == '-' {
                        c
                    } else {
                        '_'
                    }
                })
                .collect()
        };
        let mut jobs: Vec<(String, usize)> = Vec::new();
        match std::env::var("DUMP_CONES_PATHS") {
            Ok(paths) => {
                for want in paths.split(',').map(str::trim).filter(|p| !p.is_empty()) {
                    for (idx, a) in s
                        .assertions
                        .iter()
                        .filter(|a| a.paths.iter().any(|p| p.contains(want)))
                        .enumerate()
                    {
                        jobs.push((format!("{}_{idx}", stem_of(want)), a.asserted_node));
                    }
                }
            }
            Err(_) => {
                for (i, a) in s.assertions.iter().enumerate() {
                    jobs.push((format!("assert_{i}"), a.asserted_node));
                }
            }
        }
        let mut index = String::from("[");
        for (i, (stem, root)) in jobs.iter().enumerate() {
            let file = format!("{dir}/{stem}.json");
            std::fs::write(&file, format!("{}\n", cone_json(*root)))
                .unwrap_or_else(|e| panic!("write {file}: {e}"));
            if i > 0 {
                index.push_str(", ");
            }
            index.push_str(&format!("{{\"stem\": \"{stem}\", \"root\": {root}}}"));
        }
        index.push(']');
        let ifile = format!("{dir}/index.json");
        std::fs::write(&ifile, index).unwrap_or_else(|e| panic!("write {ifile}: {e}"));
        eprintln!("wrote {} cones to {dir}", jobs.len());
        return;
    }

    // Representative assertions for the analysis dumps: one per template, largest families
    // first. Derived rather than hardcoded, so the dumps work on any circuit -- ECDSA2's
    // families are `slice_w*` and `ecdsa/*`, SHA-256's are not. `DUMP_PATHS=a,b,c` overrides.
    let samples: Vec<(String, usize)> = if let Ok(list) = std::env::var("DUMP_PATHS") {
        list.split(',')
            .map(str::trim)
            .filter(|p| !p.is_empty())
            .filter_map(|want| {
                s.assertions
                    .iter()
                    .position(|a| a.paths.iter().any(|p| p.contains(want)))
                    .map(|i| (want.to_string(), i))
            })
            .collect()
    } else {
        let mut count: HashMap<usize, usize> = HashMap::new();
        let mut first: HashMap<usize, usize> = HashMap::new();
        for (i, a) in s.assertions.iter().enumerate() {
            *count.entry(a.template).or_default() += 1;
            first.entry(a.template).or_insert(i);
        }
        let mut ts: Vec<(usize, usize)> = count.into_iter().collect();
        ts.sort_by_key(|&(t, n)| (std::cmp::Reverse(n), t));
        ts.into_iter()
            .take(8)
            .map(|(t, n)| {
                let i = first[&t];
                let path = s.assertions[i]
                    .paths
                    .first()
                    .cloned()
                    .unwrap_or_else(|| format!("template{t}"));
                (format!("{path} x{n}"), i)
            })
            .collect()
    };

    // `DUMP_CANON=1` measures copy plumbing: how much of the DAG is `copy::` lifting values
    // across layers by multiplying them by one, and how far that shrinks the cones that matter.
    if std::env::var("DUMP_CANON").is_ok() {
        let c = Cones::new(&s);
        let (units, copies, content) = c.stats();
        println!(
            "{} nodes: {units} unit, {copies} copies, {content} carrying content",
            s.nodes.len()
        );
        for (want, ai) in &samples {
            let a = &s.assertions[*ai];
            println!(
                "  {want:34} cone {:5} -> {:5} after canonicalisation",
                cone(a.asserted_node).len(),
                c.cone(&s, c.canon[a.asserted_node]).len()
            );
        }
        return;
    }

    // `DUMP_FRONTIER=<budget>` sizes S2. Every node is a quadratic form, so the monomial count
    // of a full expansion is computable bottom-up: `cost(input) = 1` and
    // `cost(sum) = sum over terms of cost(a)*cost(b)`. The cut rule is then one line -- expand a
    // node iff its full expansion fits the budget, otherwise hold it opaque -- and it reproduces
    // the hand-derived cuts by construction: a 257-term root whose operands are each expensive
    // yields exactly those 257 operands as atoms, which is `gen_bitsum_meaning.py`'s cut.
    // `DUMP_FRONTIER=<budget>` reports the cut `cone::Cones::frontier` chooses.
    // `DUMP_FRONTIER_ATOMS=1` also lists the atoms, which is what distinguishes a cut that
    // matches a hand-placed one by identity from one that merely matches it by count.
    if let Ok(b) = std::env::var("DUMP_FRONTIER") {
        let budget: u64 = b.trim().parse().unwrap_or(256);
        let c = Cones::new(&s);
        println!("budget {budget} monomials (total at the root)");
        for (want, ai) in &samples {
            let a = &s.assertions[*ai];
            let f = c.frontier(&s, a.asserted_node, budget);
            println!(
                "  {want:34} full {:>9} -> total {:>7}, {:4} atoms, {:4} expanded",
                c.cost[f.root],
                f.total,
                f.atoms.len(),
                f.expanded.len()
            );
            if std::env::var("DUMP_FRONTIER_ATOMS").is_ok() {
                for &at in &f.atoms {
                    let wire = s
                        .node_wires
                        .get(at)
                        .copied()
                        .flatten()
                        .map(|(l, j)| format!("({l},{j})"))
                        .unwrap_or_else(|| "-".to_string());
                    let what = match &s.nodes[at] {
                        ParsedNode::Input { position } => match layout.get(position) {
                            Some(nm) => format!("input {position} \"{nm}\""),
                            None => format!("input {position}"),
                        },
                        ParsedNode::Sum { terms } => {
                            format!("sum[{} terms] cost {}", terms.len(), c.cost[at])
                        }
                        ParsedNode::Assert0 { w } => format!("assert0 w={w}"),
                    };
                    println!("      atom {at:>6}  wire {wire:<11} {what}");
                }
            }
        }
        return;
    }

    // `DUMP_FRONTIER_ALL=<budget>` runs the cut over every assertion and groups the results by
    // template. It answers the two questions M4 turns on:
    //
    //   * is per-shape caching *sound*  -- do all instances of a template yield the same cut?
    //   * is it *needed*                -- what does computing all 1,048 actually cost?
    //
    // M4 was motivated by amortising an expensive search. M2 removed the search, so if this runs
    // in well under a second the amortisation has no performance case left and its only remaining
    // value is in emission, not analysis.
    if let Ok(b) = std::env::var("DUMP_FRONTIER_ALL") {
        let budget: u64 = b.trim().parse().unwrap_or(512);
        let c = Cones::new(&s);
        let t0 = std::time::Instant::now();
        let mut sig: HashMap<usize, Vec<(usize, usize, u64)>> = HashMap::new();
        for a in &s.assertions {
            let f = c.frontier(&s, a.asserted_node, budget);
            sig.entry(a.template)
                .or_default()
                .push((f.atoms.len(), f.expanded.len(), f.total));
        }
        let elapsed = t0.elapsed().as_secs_f64();
        println!(
            "{} assertions over {} templates, budget {budget}, {elapsed:.3}s",
            s.assertions.len(),
            sig.len()
        );
        let mut rows: Vec<(usize, Vec<(usize, usize, u64)>)> = sig.into_iter().collect();
        rows.sort_by_key(|(t, v)| (std::cmp::Reverse(v.len()), *t));
        let (mut uniform, mut varied) = (0usize, 0usize);
        for (t, v) in &rows {
            let first = v[0];
            let same = v.iter().all(|&x| x == first);
            if same {
                uniform += 1;
            } else {
                varied += 1;
            }
            println!(
                "  template {t:3} x{:<5} {:7} atoms {:4} expanded {:4} total {:>10}",
                v.len(),
                if same { "same" } else { "VARIES" },
                first.0,
                first.1,
                first.2
            );
            if !same {
                let mut u = v.clone();
                u.sort();
                u.dedup();
                println!("          {} distinct cuts, e.g. {:?}", u.len(), &u[..u.len().min(3)]);
            }
        }
        println!("{uniform} templates uniform, {varied} varied");
        return;
    }

    // The wrapping-sum template registry and its unifier.
    //
    // The map from template index to circuit node cannot be read off `ParsedAssertion.mapping`:
    // the Lean templates in `S2TmplWrap.lean` are a different decomposition from
    // `cert::Template`'s depth-8 expansion.  It does not need to be guessed either.
    // `Core/ConeTmpl.coneIs` is structural unification: for a template node `.sum ts` at index
    // `i`, the DAG node `map i` must be a sum whose `j`th term is `(k_j, map a_j, map b_j)`, with
    // `a_j, b_j < i`.  So fixing `map root` to the asserted node determines every other entry by
    // walking indices downward, and any conflict means the template does not match.  Doing that
    // here reproduces what Lean's `decide` checks, so the two agree by construction.
    //
    // Unification is also what *selects* the template: an assertion is tried against the registry
    // in order and the first entry that unifies wins.  Nothing keys off the assertion path or the
    // round number, which is why `tnWrap7b` needs no special case -- the one round whose product
    // tree the compiler emitted with its operands reversed is picked up by the same mechanism
    // that rejects `tnWrap7` for it.
    //
    // A wrong pick cannot yield a wrong result.  `EMIT_TMPL_WRAP` emits `coneIs ... = true` by
    // `decide +kernel` per instance, and `EMIT_EDGES` feeds tables that `edgesMatch ... = true`
    // re-derives the same way, so Lean checks every match against the committed node table.
    //
    // Both emitters need this same answer, so they share one registry and one unifier.
    // A template node: a hole, or a sum of `(k_index, lhs, rhs)` over template indices.
    enum Tn {
        Leaf,
        Sum(&'static [(u32, usize, usize)]),
    }
    use Tn::{Leaf, Sum};

    /// One entry per template lemma in `Bridge/Sha256/S2TmplWrap.lean`.
    ///
    /// `nodes` is transcribed from that file and `consts` lists its constant hypotheses in
    /// the order the lemma takes them. The duplication is the price of instantiating a
    /// hand-written template; `coneIs` is what catches a divergence.
    struct WrapTmpl {
        /// The Lean `def` holding the template node list.
        tmpl: &'static str,
        /// The Lean template lemma to apply.
        lemma: &'static str,
        /// `n` in `wrapPoly n`, i.e. how many multiples of 2^32 the sum may wrap by.
        n: u32,
        /// Template index of the asserted node.
        root: usize,
        /// Template index of the hole standing for `z = c - p`.
        hole: usize,
        /// Template index of the constant-one input.
        one: usize,
        /// Constant lemmas, in the lemma's argument order.
        consts: &'static [&'static str],
        nodes: &'static [Tn],
    }

    const REGISTRY: &[WrapTmpl] = &[
        WrapTmpl {
            tmpl: "tnWrap2",
            lemma: "tmpl_wrap2",
            n: 2,
            root: 5,
            hole: 1,
            one: 0,
            consts: &["cnstw_0", "cnstw_65"],
            nodes: &[
                Leaf,
                Leaf,
                Sum(&[(0, 0, 0)]),
                Sum(&[(0, 2, 1)]),
                Sum(&[(65, 2, 2), (0, 2, 1)]),
                Sum(&[(0, 3, 4)]),
            ],
        },
        WrapTmpl {
            tmpl: "tnWrap4",
            lemma: "tmpl_wrap4",
            n: 4,
            root: 10,
            hole: 3,
            one: 0,
            consts: &["cnstw_0", "cnstw_65'", "cnstw_66", "cnstw_67"],
            nodes: &[
                Leaf,
                Sum(&[(0, 0, 0)]),
                Sum(&[(0, 1, 1)]),
                Leaf,
                Sum(&[(66, 2, 2), (0, 2, 3)]),
                Sum(&[(67, 2, 2), (0, 2, 3)]),
                Sum(&[(0, 4, 5)]),
                Sum(&[(0, 2, 3)]),
                Sum(&[(65, 2, 2), (0, 2, 3)]),
                Sum(&[(0, 7, 8)]),
                Sum(&[(0, 6, 9)]),
            ],
        },
        WrapTmpl {
            tmpl: "tnWrap6",
            lemma: "tmpl_wrap6",
            n: 6,
            root: 17,
            hole: 3,
            one: 0,
            consts: &[
                "cnstw_0",
                "cnstw_65'",
                "cnstw_66",
                "cnstw_67",
                "cnstw_68",
                "cnstw_69",
            ],
            nodes: &[
                Leaf,
                Sum(&[(0, 0, 0)]),
                Sum(&[(0, 1, 1)]),
                Leaf,
                Sum(&[(68, 2, 2), (0, 2, 3)]),
                Sum(&[(69, 2, 2), (0, 2, 3)]),
                Sum(&[(0, 4, 5)]),
                Sum(&[(0, 2, 2)]),
                Sum(&[(66, 2, 2), (0, 2, 3)]),
                Sum(&[(0, 7, 8)]),
                Sum(&[(0, 6, 9)]),
                Sum(&[(67, 2, 2), (0, 2, 3)]),
                Sum(&[(65, 2, 2), (0, 2, 3)]),
                Sum(&[(0, 11, 12)]),
                Sum(&[(0, 2, 3)]),
                Sum(&[(0, 7, 14)]),
                Sum(&[(0, 13, 15)]),
                Sum(&[(0, 10, 16)]),
            ],
        },
        WrapTmpl {
            tmpl: "tnWrap7",
            lemma: "tmpl_wrap7",
            n: 7,
            root: 18,
            hole: 3,
            one: 0,
            consts: &[
                "cnstw_0",
                "cnstw_65'",
                "cnstw_66",
                "cnstw_67",
                "cnstw_68",
                "cnstw_69",
                "cnstw_70",
            ],
            nodes: &[
                Leaf,
                Sum(&[(0, 0, 0)]),
                Sum(&[(0, 1, 1)]),
                Leaf,
                Sum(&[(70, 2, 2), (0, 2, 3)]),
                Sum(&[(68, 2, 2), (0, 2, 3)]),
                Sum(&[(0, 4, 5)]),
                Sum(&[(69, 2, 2), (0, 2, 3)]),
                Sum(&[(66, 2, 2), (0, 2, 3)]),
                Sum(&[(0, 7, 8)]),
                Sum(&[(0, 6, 9)]),
                Sum(&[(67, 2, 2), (0, 2, 3)]),
                Sum(&[(65, 2, 2), (0, 2, 3)]),
                Sum(&[(0, 11, 12)]),
                Sum(&[(0, 2, 2)]),
                Sum(&[(0, 2, 3)]),
                Sum(&[(0, 14, 15)]),
                Sum(&[(0, 13, 16)]),
                Sum(&[(0, 10, 17)]),
            ],
        },
        // The mirrored `n = 7` tree: same polynomial, `(0,z,1)` before `(k,1,1)` rather than
        // after. It must come after `tnWrap7`, which it cannot be confused with -- `coneIs`
        // compares operand lists exactly -- but ordering the registry from most to least
        // common keeps the common case at the first probe.
        WrapTmpl {
            tmpl: "tnWrap7b",
            lemma: "tmpl_wrap7b",
            n: 7,
            root: 18,
            hole: 3,
            one: 0,
            consts: &[
                "cnstw_0",
                "cnstw_65'",
                "cnstw_66",
                "cnstw_67",
                "cnstw_68",
                "cnstw_69",
                "cnstw_70",
            ],
            nodes: &[
                Leaf,
                Sum(&[(0, 0, 0)]),
                Sum(&[(0, 1, 1)]),
                Leaf,
                Sum(&[(0, 3, 2), (70, 2, 2)]),
                Sum(&[(0, 3, 2), (68, 2, 2)]),
                Sum(&[(0, 4, 5)]),
                Sum(&[(0, 3, 2), (69, 2, 2)]),
                Sum(&[(0, 3, 2), (66, 2, 2)]),
                Sum(&[(0, 7, 8)]),
                Sum(&[(0, 6, 9)]),
                Sum(&[(0, 3, 2), (67, 2, 2)]),
                Sum(&[(0, 3, 2), (65, 2, 2)]),
                Sum(&[(0, 11, 12)]),
                Sum(&[(0, 2, 2)]),
                Sum(&[(0, 3, 2)]),
                Sum(&[(0, 15, 14)]),
                Sum(&[(0, 13, 16)]),
                Sum(&[(0, 10, 17)]),
            ],
        },
    ];

    // Walk template indices downward from the root. Every operand index is smaller than its
    // parent's, so an entry is final by the time the loop reaches it, and one pass either
    // fills the whole map or finds a conflict.
    let unify = |t: &WrapTmpl, root: usize| -> Option<Vec<usize>> {
        let mut map: Vec<Option<usize>> = vec![None; t.nodes.len()];
        map[t.root] = Some(root);
        for i in (0..t.nodes.len()).rev() {
            let Some(dag) = map[i] else { continue };
            let Tn::Sum(ts) = &t.nodes[i] else { continue };
            let ParsedNode::Sum { terms } = &s.nodes[dag] else {
                return None;
            };
            if terms.len() != ts.len() {
                return None;
            }
            for (term, &(k, a, b)) in terms.iter().zip(ts.iter()) {
                if term.0 != k {
                    return None;
                }
                for (slot, val) in [(a, term.1), (b, term.2)] {
                    match map[slot] {
                        Some(prev) if prev != val => return None,
                        _ => map[slot] = Some(val),
                    }
                }
            }
        }
        map.into_iter().collect()
    };

    // `EMIT_EDGES=1` emits the node tables that `Bridge/Sha256/S2Edges*.lean` carry by hand.
    //
    // Those modules prove one `edgesMatch` per assertion *family* rather than one `coneIs` per
    // assertion -- 4 decides for the 184 wrapping sums, 13 for the 6,656 booleanity ones -- and
    // 26 modules consume the theorems they export.  What makes that possible is that a family's
    // instances are all the same shape over a different base node, so a map is `base(e)` plus
    // fixed index arithmetic, and only `base` is data.
    //
    // Only `base` is emitted.  The arithmetic and every theorem stay hand-written.  The generator
    // checks that the hand arithmetic reproduces each unified map *exactly* and writes nothing if
    // it does not, so a change in circuit shape is a generation-time failure naming the instance,
    // not a false `decide` inside a proof several modules downstream.
    //
    // That split is worth keeping because it is the one that held.  Measured against a later
    // compile, 63 of 64 `zOf6` bases and 60 of 64 `zOf7` bases had drifted, while the arithmetic
    // -- including round 18's fully contiguous tree, and the CSE'd `532` the other 63 rounds
    // share -- still reproduced every map.  Node ids drift; cone shape does not.
    if std::env::var("EMIT_EDGES").is_ok() {
        // `tnBool` from `S2TmplBool.lean`.  Hole 1, root 2, so `mapOfB e = [0, bitOfB e,
        // assertOfB e]`.  `lemma`/`n`/`consts` are unused here -- only the node list matters --
        // but are recorded so the entry reads like the others.
        const BOOL: WrapTmpl = WrapTmpl {
            tmpl: "tnBool",
            lemma: "tmpl_isBool",
            n: 0,
            root: 2,
            hole: 1,
            one: 0,
            consts: &["cnst_0", "cnst_2"],
            nodes: &[Leaf, Leaf, Sum(&[(0, 0, 1), (2, 1, 1)])],
        };

        /// One emitted family: which templates feed it, how its instances are numbered, and the
        /// tables to write out.
        struct Fam {
            /// Templates whose instances share one table.  `tnWrap7` and `tnWrap7b` do: they are
            /// two shapes of the same 64 round assertions, and `zOf7` covers both.
            tmpls: &'static [&'static str],
            /// Path segment carrying the family index (`rounds.12` -> 12), which is the
            /// `assert_mapi` loop counter and therefore what `e` means in `zOf6 e`.
            /// `None` numbers instances in sidecar order, for a family nothing indexes by name.
            word: Option<&'static str>,
            count: usize,
            /// `(table name, template index it holds)`, in the order `rebuild` reads them.
            tables: &'static [(&'static str, usize)],
        }
        const FAMS: &[Fam] = &[
            Fam {
                tmpls: &["tnWrap2"],
                word: Some("final"),
                count: 8,
                tables: &[("zOfW", 1), ("f0OfW", 3), ("f1OfW", 4), ("rootOfW", 5)],
            },
            Fam {
                tmpls: &["tnWrap4"],
                word: Some("schedule"),
                count: 48,
                tables: &[("zOfS", 3)],
            },
            Fam {
                tmpls: &["tnWrap6"],
                word: Some("rounds"),
                count: 64,
                tables: &[("zOf6", 3)],
            },
            Fam {
                tmpls: &["tnWrap7", "tnWrap7b"],
                word: Some("rounds"),
                count: 64,
                tables: &[("zOf7", 3)],
            },
            Fam {
                tmpls: &["tnBool"],
                word: None,
                count: 6656,
                tables: &[("bitOfB", 1), ("assertOfB", 2)],
            },
        ];

        // The index arithmetic transcribed from the `mapOf*` definitions in `S2Edges*.lean`.
        // `cols` are this instance's table values, in the family's declared order.  Constants
        // appear literally so the check covers them too: `238`/`239` are the shared `1` nodes and
        // `532` the CSE'd one the round trees borrow.
        let rebuild = |tmpl: &str, e: usize, cols: &[usize], i: usize| -> usize {
            let z = cols[0];
            match tmpl {
                "tnWrap2" => [0, cols[0], 238, cols[1], cols[2], cols[3]][i],
                "tnBool" => [0, cols[0], cols[1]][i],
                "tnWrap4" => {
                    if i < 3 {
                        [0, 238, 239][i]
                    } else {
                        z + (i - 3)
                    }
                }
                "tnWrap6" => {
                    if i < 3 {
                        [0, 238, 239][i]
                    } else if i < 7 {
                        z + (i - 3)
                    } else if i == 7 {
                        // Round 18's tree owns `532`, so for it alone the run is unbroken.
                        if e == 18 {
                            z + 4
                        } else {
                            532
                        }
                    } else if e == 18 {
                        z + (i - 3)
                    } else {
                        z + (i - 4)
                    }
                }
                "tnWrap7" | "tnWrap7b" => {
                    if i < 3 {
                        [0, 238, 239][i]
                    } else if i < 14 {
                        z + (i - 3)
                    } else if i == 14 {
                        532
                    } else {
                        z + (i - 4)
                    }
                }
                other => panic!("no index arithmetic recorded for {other}"),
            }
        };

        // `sha256/rounds/rounds.12/round_step/...` -> 12.
        let path_index = |path: &str, word: &str| -> Option<usize> {
            path.split('/')
                .find_map(|seg| seg.strip_prefix(word)?.strip_prefix('.')?.parse().ok())
        };

        // Unify every assertion once, bucketed by the template it matched.
        let mut found: HashMap<&str, Vec<(String, usize, Vec<usize>)>> = HashMap::new();
        let mut unmatched = 0usize;
        for a in &s.assertions {
            let path = a.paths.first().map(String::as_str).unwrap_or("");
            let hit = REGISTRY
                .iter()
                .chain(std::iter::once(&BOOL))
                .find_map(|t| unify(t, a.asserted_node).map(|m| (t, m)));
            match hit {
                Some((t, m)) => found
                    .entry(t.tmpl)
                    .or_default()
                    .push((path.to_string(), a.asserted_node, m)),
                None => unmatched += 1,
            }
        }
        if unmatched > 0 {
            println!("note: {unmatched} assertion(s) matched no template and are not emitted");
        }

        let mut out = String::from(
            "-- Generated by `meaning_gen`; do not edit.\n\
             --\n\
             -- Base node tables for the `edgesMatch` families in `Bridge/Sha256/S2Edges*.lean`.\n\
             -- The index arithmetic that turns a base into a full cone map lives there; this\n\
             -- file is only the part that changes when the circuit is recompiled.\n\
             namespace Quadcert.Gen.Sha256Blk.Edges\n",
        );

        for fam in FAMS {
            // Gather the family's instances and place each at its own index.
            let mut slot: Vec<Option<(String, Vec<usize>)>> = vec![None; fam.count];
            let mut seq = 0usize;
            for tmpl in fam.tmpls {
                for (path, _root, map) in found.get(tmpl).into_iter().flatten() {
                    let e = match fam.word {
                        Some(w) => path_index(path, w).unwrap_or_else(|| {
                            panic!("no `{w}.<n>` segment in {path}")
                        }),
                        None => {
                            seq += 1;
                            seq - 1
                        }
                    };
                    assert!(e < fam.count, "index {e} out of range for {tmpl} in {path}");
                    assert!(
                        slot[e].is_none(),
                        "two {tmpl} instances claim index {e}; second is {path}"
                    );
                    slot[e] = Some((path.clone(), map.clone()));
                }
            }
            let missing: Vec<usize> = (0..fam.count).filter(|&e| slot[e].is_none()).collect();
            assert!(
                missing.is_empty(),
                "{:?}: no instance for indices {:?}",
                fam.tmpls,
                &missing[..missing.len().min(8)]
            );

            // Check the hand arithmetic against every unified map before emitting anything.
            for (e, entry) in slot.iter().enumerate() {
                let (path, map) = entry.as_ref().unwrap();
                let cols: Vec<usize> = fam.tables.iter().map(|&(_, i)| map[i]).collect();
                let tmpl = fam.tmpls[0];
                for i in 0..map.len() {
                    let want = rebuild(tmpl, e, &cols, i);
                    assert_eq!(
                        want, map[i],
                        "index arithmetic for {tmpl} disagrees with the circuit at \
                         index {e}, template slot {i} ({path}):\n  hand {want}\n  true {}\n  \
                         full {map:?}\nThe cone shape changed; `mapOf*` in S2Edges*.lean and \
                         `rebuild` here both need updating before these tables mean anything.",
                        map[i]
                    );
                }
            }

            for &(name, ti) in fam.tables {
                let vals: Vec<usize> = slot
                    .iter()
                    .map(|entry| entry.as_ref().unwrap().1[ti])
                    .collect();
                out.push_str(&format!(
                    "\n/-- `{name}`: {} entries, template slot {ti}. -/\ndef {name} : Nat → Nat := fun e => (",
                    vals.len()
                ));
                bisect(&vals, 0, vals.len(), &mut out);
                out.push_str(")\n");
            }
        }
        out.push_str("\nend Quadcert.Gen.Sha256Blk.Edges\n");
        std::fs::write(&out_path, &out).unwrap_or_else(|e| panic!("write {out_path}: {e}"));
        println!("emitted edge tables to {out_path} ({} bytes)", out.len());
        for fam in FAMS {
            let names: Vec<&str> = fam.tables.iter().map(|&(n, _)| n).collect();
            println!("  {:?}: {} instances -> {}", fam.tmpls, fam.count, names.join(", "));
        }
        return;
    }


    if std::env::var("EMIT_TMPL_WRAP").is_ok() {

        let mut out = format!(
            "-- Generated by `meaning_gen`; do not edit.\n\
             import quadcert.Bridge.Sha256.S2TmplWrap\n\
             set_option maxRecDepth 4000000\n\
             namespace {name}\n\
             open Quadcert Quadcert.Gen.{name}\n\n\
             variable {{F : Type}} [Field F]\n"
        );
        let mut hits: BTreeMap<&str, usize> = BTreeMap::new();
        let mut misses: Vec<(&str, usize)> = Vec::new();
        for a in &s.assertions {
            let path = a.paths.first().map(String::as_str).unwrap_or("");
            if !path.contains("assert_wrapping_sum") {
                continue;
            }
            let Some((t, map)) = REGISTRY
                .iter()
                .find_map(|t| unify(t, a.asserted_node).map(|m| (t, m)))
            else {
                misses.push((path, a.asserted_node));
                continue;
            };
            let root = map[t.root];
            let z = map[t.hole];
            let one = map[t.one];
            let lst = format!(
                "([{}] : List Nat)",
                map.iter().map(usize::to_string).collect::<Vec<_>>().join(", ")
            );
            out.push_str(&format!(
                "\n/-- `{path}`, node {root}, via `{tmpl}`. -/\n\
                 theorem wrap_{root} [CharP F p256w] (inputs : Nat → F)\n    \
                 (hin0 : inputs 0 = 1)\n    \
                 (hroot : interpDag (raw.toDag (cnstw F)) inputs {root} = 0) :\n    \
                 SHA256F.wrapPoly {n} ((2 ^ 32 : Nat) : F)\n      \
                 (interpDag (raw.toDag (cnstw F)) inputs {z}) = 0 := by\n  \
                 have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by\n    \
                 simp [RawCircuit.toDag]\n  \
                 have hcone : coneIs nodeFn {tmpl} (fun i => {lst}.getD i 0) = true := by\n    \
                 decide +kernel\n  \
                 have hmap : ∀ i, i < {tmpl}.length → {lst}.getD i 0 < raw.nodes.length := by\n    \
                 intro i hi\n    \
                 have hl : {tmpl}.length = {len} := rfl\n    \
                 rw [hl] at hi\n    \
                 rw [nodes_len]\n    \
                 interval_cases i <;> decide\n  \
                 have htr := coneIs_transfer raw (cnstw F) inputs nodeFn nodefn_ok {tmpl}\n      \
                 (fun i => {lst}.getD i 0) hcone hmap {ri} (by decide)\n  \
                 have hlv0 : interpDag (raw.toDag (cnstw F)) inputs ({lst}.getD {hi} 0) = 1 := by\n    \
                 show interpDag (raw.toDag (cnstw F)) inputs {one} = 1\n    \
                 rw [interpDag_input (raw.toDag (cnstw F)) inputs {one} 0\n      \
                 (by rw [hdaglen, nodes_len]; norm_num)\n      \
                 (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok \n        \
                 (by rw [nodes_len]; norm_num)]; rfl)]\n    \
                 exact hin0\n  \
                 have hz : interpDag (tmplDag (cnstw F) {tmpl})\n      \
                 (fun h => interpDag (raw.toDag (cnstw F)) inputs ({lst}.getD h 0)) {ri} \
                 = 0 := by\n    \
                 rw [← htr]; exact hroot\n  \
                 exact {lemma} (cnstw F)\n    \
                 (fun h => interpDag (raw.toDag (cnstw F)) inputs ({lst}.getD h 0))\n    \
                 {cs} hlv0 hz\n",
                tmpl = t.tmpl,
                lemma = t.lemma,
                n = t.n,
                len = t.nodes.len(),
                ri = t.root,
                hi = t.one,
                cs = t.consts.join(" "),
            ));
            *hits.entry(t.tmpl).or_default() += 1;
        }
        out.push_str(&format!("\nend {name}\n"));
        std::fs::write(&out_path, &out).unwrap_or_else(|e| panic!("write {out_path}: {e}"));
        let total: usize = hits.values().sum();
        println!("emitted {total} wrap instances to {out_path} ({} bytes)", out.len());
        for (tmpl, n) in &hits {
            println!("  {tmpl}: {n}");
        }
        if !misses.is_empty() {
            println!("  {} assertion(s) matched no template:", misses.len());
            for (path, node) in misses.iter().take(10) {
                println!("    node {node}  {path}");
            }
        }
        return;
    }

    // `EMIT_WIRES=1` emits the per-word node tables that hand-written bridges currently carry
    // by hand. `S2Words.wordBits` and `S2State.hinBits` are 205 lines of node ids between them,
    // and node ids come out of the compiler -- so those files break whenever the circuit is
    // recompiled, which is what stops `Gen/` from being regenerable rather than committed.
    //
    // The data is entirely derivable. `LayoutBuilder::record_range(start, 32, "outw5")` names
    // input positions `outw5_0 .. outw5_31`, least significant bit first, so every layout entry
    // is `{group}{index}_{bit}`; pairing that with the `Input` node at each position gives the
    // table. What stays hand-written is the *reasoning* on top -- that `wordBits k` is
    // `input_block k` below 16 and `outw (k-16)` above, or how `stateBits t i` shifts -- which is
    // specification knowledge and mentions no node.
    if std::env::var("EMIT_WIRES").is_ok() {
        let mut pos_node: HashMap<usize, usize> = HashMap::new();
        for (n, node) in s.nodes.iter().enumerate() {
            if let ParsedNode::Input { position } = node {
                pos_node.insert(*position, n);
            }
        }
        // `outw5_17` -> ("outw", 5, 17); `h0_0_5` -> ("h0_", 0, 5)
        let split_num = |x: &str| -> Option<(String, usize)> {
            let cut = x
                .rfind(|c: char| !c.is_ascii_digit())
                .map(|i| i + 1)
                .unwrap_or(0);
            if cut == x.len() {
                return None;
            }
            x[cut..]
                .parse::<usize>()
                .ok()
                .map(|n| (x[..cut].to_string(), n))
        };
        let mut table: BTreeMap<String, BTreeMap<usize, BTreeMap<usize, usize>>> = BTreeMap::new();
        // Scalar inputs such as `one` carry no `_{bit}` suffix and are not word bits.
        let mut scalars: Vec<&str> = Vec::new();
        for (pos, full) in &s.input_layout {
            let Some(node) = pos_node.get(pos) else { continue };
            let Some((base, bit)) = split_num(full) else {
                scalars.push(full);
                continue;
            };
            let Some((group, index)) = split_num(base.trim_end_matches('_')) else {
                scalars.push(full);
                continue;
            };
            table
                .entry(group)
                .or_default()
                .entry(index)
                .or_default()
                .insert(bit, *node);
        }
        let ident = |g: &str| -> String {
            let mut out = String::new();
            let mut up = false;
            for c in g.chars() {
                if c == '_' {
                    up = true;
                } else if up {
                    out.extend(c.to_uppercase());
                    up = false;
                } else {
                    out.push(c);
                }
            }
            format!("{out}Bits")
        };
        let mut out = format!(
            "-- Generated by `meaning_gen`; do not edit.\n\
             namespace Quadcert.Gen.{name}\n"
        );
        for (group, byindex) in &table {
            let widths: BTreeSet<usize> = byindex.values().map(BTreeMap::len).collect();
            let ws: Vec<String> = widths.iter().map(usize::to_string).collect();
            out.push_str(&format!(
                "\n/-- `{group}` wires: index to its bit nodes, least significant first. \
                 {} words of {} bits. -/\ndef {} : Nat → List Nat\n",
                byindex.len(),
                ws.join("/"),
                ident(group)
            ));
            for (index, bits) in byindex {
                let ns: Vec<String> = bits.values().map(usize::to_string).collect();
                out.push_str(&format!("  | {index} => [{}]\n", ns.join(", ")));
            }
            out.push_str("  | _ => []\n");
        }
        out.push_str(&format!("\nend Quadcert.Gen.{name}\n"));
        std::fs::write(&out_path, &out).unwrap_or_else(|e| panic!("write {out_path}: {e}"));
        println!(
            "emitted {} wire tables to {out_path} ({} bytes)",
            table.len(),
            out.len()
        );
        for (group, byindex) in &table {
            println!("  {:<14} {} words -> {}", group, byindex.len(), ident(group));
        }
        if !scalars.is_empty() {
            println!(
                "  {} scalar input(s), not word bits, skipped: {}",
                scalars.len(),
                scalars.join(", ")
            );
        }
        return;
    }

    // `EMIT_TMPL_BOOL=1` emits the `is_boolean` family as **template instances** rather than as
    // one self-contained lemma per assertion.
    //
    // This is the shape `Bridge/Sha256/S2TmplBool.lean` establishes: the algebra is proved once
    // in `tmpl_isBool`, and an instance is discharged by matching its cone against `tnBool` with
    // `decide +kernel` and transporting through `coneIs_transfer`. No per-node value chain, and
    // nothing algebraic repeated per instance. It matters because the family is 6,656 of
    // SHA-256's 6,840 assertions and 284,707 of mdoc_hash's 303,413.
    //
    // All the per-instance emitter needs is `ParsedAssertion.mapping` -- template index to DAG
    // node -- and the input position of the bit. The template lemma itself is *not* generated:
    // it names `SHA256F.isBit_of_zero_raw`, which is specification vocabulary, and lives in the
    // handwritten support module named by `TMPL_IMPORT`.
    if let Ok(limit) = std::env::var("EMIT_TMPL_BOOL") {
        // `EMIT_TMPL_BOOL=<n>` caps the number of instances, so the first compile can be one
        // lemma rather than 6,656. `all` emits the whole family.
        let limit: usize = limit.trim().parse().unwrap_or(usize::MAX);
        let import = std::env::var("TMPL_IMPORT")
            .unwrap_or_else(|_| "quadcert.Bridge.Sha256.S2TmplBool".to_string());
        // Instances are collected, then written in batches. The import floor dominates:
        // measured on SHA-256, a module costs ~6 s and ~6.0 GB before its first lemma, and each
        // instance adds ~0.09 s and ~6-11 MB. One module per instance would be 6,656 x 6 s of
        // pure floor (~11 h); all 6,656 in one module extrapolates to 45-78 GB, over the
        // machine. `BATCH=<n>` picks the point between -- ~1,024 lands near 17 GB, 7 modules.
        let batch: usize = std::env::var("BATCH")
            .ok()
            .and_then(|v| v.trim().parse().ok())
            .unwrap_or(usize::MAX);
        let header = format!(
            "-- Generated by `meaning_gen`; do not edit.\n\
             import {import}\n\
             set_option maxRecDepth 4000000\n\
             namespace {name}\n\
             open Quadcert Quadcert.Gen.{name}\n\n\
             variable {{F : Type}} [Field F]\n"
        );
        let mut insts: Vec<String> = Vec::new();
        let mut emitted = 0usize;
        let mut rejected = 0usize;
        for a in &s.assertions {
            let path = a.paths.first().map(String::as_str).unwrap_or("");
            if !(path == "is_boolean" || path.ends_with("/is_boolean")) {
                continue;
            }
            // The shape is [constant-one input, the bit, the asserted node].
            if a.mapping.len() != 3 {
                rejected += 1;
                continue;
            }
            let (m0, m1, m2) = (a.mapping[0], a.mapping[1], a.mapping[2]);
            let ParsedNode::Input { position: bit } = s.nodes[m1] else {
                rejected += 1;
                continue;
            };
            if m2 != a.asserted_node {
                rejected += 1;
                continue;
            }
            let map = format!("([{m0}, {m1}, {m2}] : List Nat)");
            insts.push(format!(
                "\n/-- `{path}`, node {m2}. -/\n\
                 theorem bool_{m2} [CharP F p256] (inputs : Nat → F)\n    \
                 (hin0 : inputs 0 = 1)\n    \
                 (hroot : interpDag (raw.toDag (cnst F)) inputs {m2} = 0) :\n    \
                 inputs {bit} = 0 ∨ inputs {bit} = 1 := by\n  \
                 have hdaglen : (raw.toDag (cnst F)).length = raw.nodes.length := by\n    \
                 simp [RawCircuit.toDag]\n  \
                 have hcone : coneIs nodeFn tnBool (fun i => {map}.getD i 0) = true := by\n    \
                 decide +kernel\n  \
                 have hmap : ∀ i, i < tnBool.length → {map}.getD i 0 < raw.nodes.length := by\n    \
                 intro i hi\n    \
                 have h3 : tnBool.length = 3 := rfl\n    \
                 rw [h3] at hi\n    \
                 rw [nodes_len]\n    \
                 match i, hi with\n    \
                 | 0, _ => decide\n    \
                 | 1, _ => decide\n    \
                 | 2, _ => decide\n  \
                 have htr := coneIs_transfer raw (cnst F) inputs nodeFn nodefn_ok tnBool\n      \
                 (fun i => {map}.getD i 0) hcone hmap 2 (by decide)\n  \
                 have hlv0 : interpDag (raw.toDag (cnst F)) inputs ({map}.getD 0 0) = 1 := by\n    \
                 show interpDag (raw.toDag (cnst F)) inputs {m0} = 1\n    \
                 rw [interpDag_input (raw.toDag (cnst F)) inputs {m0} 0\n      \
                 (by rw [hdaglen, nodes_len]; norm_num)\n      \
                 (by rw [toDag_getD_fn raw (cnst F) nodeFn nodefn_ok \n        \
                 (by rw [nodes_len]; norm_num)]; rfl)]\n    \
                 exact hin0\n  \
                 have hlv1 : interpDag (raw.toDag (cnst F)) inputs ({map}.getD 1 0) \
                 = inputs {bit} := by\n    \
                 show interpDag (raw.toDag (cnst F)) inputs {m1} = inputs {bit}\n    \
                 rw [interpDag_input (raw.toDag (cnst F)) inputs {m1} {bit}\n      \
                 (by rw [hdaglen, nodes_len]; norm_num)\n      \
                 (by rw [toDag_getD_fn raw (cnst F) nodeFn nodefn_ok \n        \
                 (by rw [nodes_len]; norm_num)]; rfl)]\n  \
                 have hz : interpDag (tmplDag (cnst F) tnBool)\n      \
                 (fun h => interpDag (raw.toDag (cnst F)) inputs ({map}.getD h 0)) 2 = 0 := by\n    \
                 rw [← htr]; exact hroot\n  \
                 have hb := tmpl_isBool (cnst F)\n    \
                 (fun h => interpDag (raw.toDag (cnst F)) inputs ({map}.getD h 0))\n    \
                 cnst_0 cnst_2 hlv0 hz\n  \
                 rwa [hlv1] at hb\n"
            ));
            emitted += 1;
            if emitted >= limit {
                break;
            }
        }
        let stem = out_path.strip_suffix(".lean").unwrap_or(&out_path);
        let chunks: Vec<&[String]> = if batch == usize::MAX || insts.len() <= batch {
            vec![&insts[..]]
        } else {
            insts.chunks(batch).collect()
        };
        let single = chunks.len() == 1;
        let mut total = 0usize;
        for (i, chunk) in chunks.iter().enumerate() {
            let mut out = header.clone();
            for inst in chunk.iter() {
                out.push_str(inst);
            }
            out.push_str(&format!("\nend {name}\n"));
            let file = if single {
                format!("{stem}.lean")
            } else {
                format!("{stem}{i}.lean")
            };
            std::fs::write(&file, &out).unwrap_or_else(|e| panic!("write {file}: {e}"));
            total += out.len();
            println!("  {file}: {} instances, {} bytes", chunk.len(), out.len());
        }
        println!(
            "emitted {emitted} instances in {} module(s), {total} bytes, {rejected} rejected",
            chunks.len()
        );
        return;
    }

    // `DUMP_SWEEP=1` walks the budget geometrically and reports the whole trade-off curve per
    // family, so an objective can be chosen from the shape of the curve rather than guessed.
    // `interior` counts atoms that are sums rather than inputs -- the hand-placed cuts are
    // characterised by how few of those they leave (three, for a loop round), so it is the
    // column that distinguishes a structural cut from one that merely ran out of budget.
    if std::env::var("DUMP_SWEEP").is_ok() {
        let c = Cones::new(&s);
        for (want, ai) in &samples {
            let a = &s.assertions[*ai];
            println!("{want}  (full expansion {} monomials)", c.cost[c.canon[a.asserted_node]]);
            println!("    {:>10} {:>7} {:>9} {:>9} {:>12}", "budget", "atoms", "interior", "expanded", "total");
            let mut prev: Option<(usize, usize, usize, u64)> = None;
            for e in 0..21u32 {
                let budget = 1u64 << e;
                let f = c.frontier(&s, a.asserted_node, budget);
                let interior = f
                    .atoms
                    .iter()
                    .filter(|&&n| matches!(&s.nodes[n], ParsedNode::Sum { .. }))
                    .count();
                let row = (f.atoms.len(), interior, f.expanded.len(), f.total);
                if prev.as_ref() != Some(&row) {
                    println!(
                        "    {budget:>10} {:>7} {:>9} {:>9} {:>12}",
                        row.0, row.1, row.2, row.3
                    );
                    prev = Some(row);
                }
            }
        }
        return;
    }

    // The shared support module (`consts_pos`, `consts_neg`, the `p256` abbrev) is named per
    // circuit and is not derivable from `NAME`: ECDSA2's is `E2Meaning`.
    // The hand-written support module the generated lemmas import. It lives at
    // `Bridge/Ecdsa2/E2Meaning.lean`; the old default, `E2Meaning`, predates the split of
    // `quadcert` into `Core/`, `Bridge/` and `Gen/` and named a module that no longer exists,
    // so the default run emitted `import quadcert.E2Meaning` and could not build.
    let support = std::env::var("SUPPORT")
        .unwrap_or_else(|_| "Bridge.Ecdsa2.E2Meaning".to_string());
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

/// Write `v` as a balanced `if e < mid then .. else ..` bisection over `e`.
///
/// A flat `List Nat` lookup would be O(n) per probe and so O(n^2) across a family, which is what
/// makes `coneIs` over a large map unusable -- measured on a synthetic map, 0.99 s at n=256,
/// 18.7 s at n=1024 and an abort at n=4096, against 0.14 / 1.20 / 14.2 s bisected.  At 6,656
/// booleanity edges the difference decides whether the module builds at all, so every table goes
/// out in this shape.  The split points match the hand-written tables exactly, so regenerating an
/// unchanged circuit reproduces them byte for byte.
fn bisect(v: &[usize], lo: usize, hi: usize, out: &mut String) {
    if hi - lo == 1 {
        out.push_str(&v[lo].to_string());
        return;
    }
    let mid = (lo + hi) / 2;
    out.push_str(&format!("if e < {mid} then "));
    bisect(v, lo, mid, out);
    out.push_str(" else ");
    bisect(v, mid, hi, out);
}
