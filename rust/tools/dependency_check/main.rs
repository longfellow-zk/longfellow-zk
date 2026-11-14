// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Dependency check over rust-analyzer's resolved index of this crate.
//!
//! ```sh
//! cargo run --release --features tooling --bin dependency_check [-- --dot <directory>]
//! ```
//!
//! The tool runs `rust-analyzer scip` on the crate (with the analysis features
//! `testonly,tooling`) and builds the file graph: an edge A -> B means a
//! reference written in file A resolves to an item defined in file B. Every
//! reference counts, in signatures, bodies, imports and macro output, and it
//! is attributed to the file where it is written, so a method defined in
//! `prover.rs` makes `prover.rs` depend on its type, not the reverse. Module
//! names in paths, function-local symbols, macros, symbols defined outside the
//! crate, test and bench files, and the crate root `src/lib.rs` (which only
//! mounts modules and defines the `cfg_*!` wrappers) are not edges.
//!
//! A component is a file's directory up to its `src` directory (for example
//! `runtime/v2/zk`), or its own directory when it has none (`runtime` for
//! `runtime/mod.rs`). `tools/dependency_check/rules.txt` lists every component with the
//! components it may use. The check fails when
//! - a component is missing from the rules, or a rule names no component;
//! - a component uses one that its rule does not list;
//! - the rules themselves contain a cycle, or allow an edge between a v1 and a v2 component;
//! - a v1 file uses a v2 file or the reverse. A file belongs to version vN when a directory on its
//!   path, or a `_`-separated word of its name, is `vN` (`runtime/v2/...`, `core/proto/src/v1/...`,
//!   `v2_segment.rs`);
//! - the file graph has a cycle: no file may depend on itself through others;
//! - a file whose name marks one proof role (`prover`, `verifier`, or a name containing exactly one
//!   of them as a `_`-separated word) uses a file of the other role;
//! - a reference breaks a `[symbol rules]` line, which says which files may (`only`) or may not
//!   (`never`) reference a symbol, or a symbol pattern names no symbol of the crate. Symbol rules
//!   see references within a file too; they keep transcript framing, sealing and private coins
//!   where the protocol design puts them.
//!
//! `--dot <directory>` also writes `files.dot` and `components.dot` there;
//! `--current` prints the current graph in the rules format instead of checking.
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
    process::Command,
};

use protobuf::Message;

type Graph = BTreeMap<String, BTreeMap<String, usize>>;

fn excluded(path: &str) -> bool {
    path == "src/lib.rs"
        || path
            .split('/')
            .any(|part| part == "tests" || part == "benches")
}

fn component(path: &str) -> String {
    let parts: Vec<_> = path.split('/').collect();
    match parts.iter().position(|part| *part == "src") {
        Some(i) => parts[..i].join("/"),
        None => parts[..parts.len() - 1].join("/"),
    }
}

/// The protocol version a path belongs to, if any.
fn version(path: &str) -> Option<&'static str> {
    let (dirs, file) = path.rsplit_once('/').unwrap_or(("", path));
    let stem = file.strip_suffix(".rs").unwrap_or(file);
    let mut words = dirs.split('/').chain(stem.split('_'));
    match (words.clone().any(|w| w == "v1"), words.any(|w| w == "v2")) {
        (true, false) => Some("v1"),
        (false, true) => Some("v2"),
        _ => None,
    }
}

fn role(path: &str) -> Option<&'static str> {
    let stem = Path::new(path).file_stem()?.to_str()?;
    let words: Vec<_> = stem.split('_').collect();
    match (words.contains(&"prover"), words.contains(&"verifier")) {
        (true, false) => Some("prover"),
        (false, true) => Some("verifier"),
        _ => None,
    }
}

/// One resolved reference between two indexed files.
struct Reference {
    from: String,
    line: i32,
    /// The symbol without package and version, e.g. `runtime/v2/zk/joint/X#`.
    symbol: String,
    /// The file that defines the symbol.
    to: String,
}

const PACKAGE: &str = "rust-analyzer cargo longfellow-zk ";

/// Runs rust-analyzer; returns the file graph, every reference between
/// indexed files, and every symbol the crate defines.
fn file_graph(root: &Path, work: &Path) -> (Graph, Vec<Reference>, BTreeSet<String>) {
    std::fs::create_dir_all(work).expect("create the index directory");
    let config = work.join("rust-analyzer.json");
    std::fs::write(
        &config,
        r#"{"cargo": {"features": ["testonly", "tooling"]}}"#,
    )
    .expect("write the rust-analyzer configuration");
    let index_path = work.join("index.scip");
    let output = Command::new("rust-analyzer")
        .arg("scip")
        .arg(root)
        .arg("--config-path")
        .arg(&config)
        .arg("--output")
        .arg(&index_path)
        .output()
        .expect("run rust-analyzer (install it with `rustup component add rust-analyzer`)");
    assert!(
        output.status.success(),
        "rust-analyzer scip failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let bytes = std::fs::read(&index_path).expect("read the index");
    let index = scip::types::Index::parse_from_bytes(&bytes).expect("parse the index");
    let definition = scip::types::SymbolRole::Definition as i32;
    // Binaries' items are named by package only, so two binaries can define
    // the same symbol; a reference resolves to its own file's definition, or
    // one in its component, when there is one.
    let mut defined_in: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for doc in &index.documents {
        for occurrence in &doc.occurrences {
            if occurrence.symbol_roles & definition != 0 {
                defined_in
                    .entry(occurrence.symbol.as_str())
                    .or_default()
                    .push(doc.relative_path.as_str());
            }
        }
    }
    let mut graph = Graph::new();
    let mut references = Vec::new();
    for doc in &index.documents {
        let from = doc.relative_path.as_str();
        if excluded(from) {
            continue;
        }
        graph.entry(from.to_owned()).or_default();
        for occurrence in &doc.occurrences {
            let symbol = occurrence.symbol.as_str();
            if occurrence.symbol_roles & definition != 0
                || symbol.starts_with("local ")
                || symbol.ends_with('/')
                || symbol.ends_with('!')
            {
                continue;
            }
            let Some(candidates) = defined_in.get(symbol) else {
                continue;
            };
            let to = if candidates.contains(&from) {
                from
            } else {
                *candidates
                    .iter()
                    .find(|c| component(c) == component(from))
                    .unwrap_or(&candidates[0])
            };
            if excluded(to) {
                continue;
            }
            // Symbol rules see same-file references too; the graph does not.
            references.push(Reference {
                from: from.to_owned(),
                line: occurrence.range[0] + 1,
                symbol: descriptor(symbol).to_owned(),
                to: to.to_owned(),
            });
            if to != from {
                *graph
                    .entry(from.to_owned())
                    .or_default()
                    .entry(to.to_owned())
                    .or_default() += 1;
            }
        }
    }
    let symbols = defined_in
        .keys()
        .map(|symbol| descriptor(symbol).to_owned())
        .collect();
    (graph, references, symbols)
}

/// A crate symbol without package and version: `runtime/v2/zk/joint/X#`.
fn descriptor(symbol: &str) -> &str {
    symbol
        .strip_prefix(PACKAGE)
        .and_then(|rest| rest.split_once(' '))
        .map_or(symbol, |(_, descriptor)| descriptor)
}

fn collapse(files: &Graph) -> Graph {
    let mut components = Graph::new();
    for (from, targets) in files {
        let a = component(from);
        components.entry(a.clone()).or_default();
        for (to, count) in targets {
            let b = component(to);
            if a != b {
                *components
                    .entry(a.clone())
                    .or_default()
                    .entry(b)
                    .or_default() += count;
            }
        }
    }
    components
}

/// Strongly connected components with more than one node, each sorted.
fn cycles(graph: &Graph) -> BTreeSet<Vec<String>> {
    let nodes: Vec<&String> = graph
        .keys()
        .chain(graph.values().flat_map(BTreeMap::keys))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let id: BTreeMap<&str, usize> = nodes
        .iter()
        .enumerate()
        .map(|(i, n)| (n.as_str(), i))
        .collect();
    let adj: Vec<Vec<usize>> = nodes
        .iter()
        .map(|n| {
            graph
                .get(*n)
                .map(|m| m.keys().map(|k| id[k.as_str()]).collect())
                .unwrap_or_default()
        })
        .collect();
    // Iterative Tarjan, so deep graphs cannot overflow the stack.
    let n = nodes.len();
    let (mut index, mut low, mut on) = (vec![usize::MAX; n], vec![0; n], vec![false; n]);
    let (mut stack, mut next, mut found) = (Vec::new(), 0, BTreeSet::new());
    for start in 0..n {
        if index[start] != usize::MAX {
            continue;
        }
        let mut work = vec![(start, 0)];
        while let Some(&mut (v, ref mut edge)) = work.last_mut() {
            if *edge == 0 && index[v] == usize::MAX {
                index[v] = next;
                low[v] = next;
                next += 1;
                stack.push(v);
                on[v] = true;
            }
            if let Some(&w) = adj[v].get(*edge) {
                *edge += 1;
                if index[w] == usize::MAX {
                    work.push((w, 0));
                } else if on[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            work.pop();
            if let Some(&(parent, _)) = work.last() {
                low[parent] = low[parent].min(low[v]);
            }
            if low[v] == index[v] {
                let mut members = Vec::new();
                loop {
                    let w = stack.pop().unwrap();
                    on[w] = false;
                    members.push(nodes[w].clone());
                    if w == v {
                        break;
                    }
                }
                if members.len() > 1 {
                    members.sort();
                    found.insert(members);
                }
            }
        }
    }
    found
}

/// `symbol only files...` or `symbol never files...`: which files may (only)
/// or may not (never) reference a symbol. `*` matches any run of characters
/// in both the symbol and the file patterns.
struct SymbolRule {
    text: String,
    symbol: String,
    only: bool,
    files: Vec<String>,
}

fn glob(pattern: &str, text: &str) -> bool {
    let mut parts = pattern.split('*');
    let Some(mut rest) = text.strip_prefix(parts.next().unwrap()) else {
        return false;
    };
    let middle: Vec<_> = parts.collect();
    for (i, part) in middle.iter().enumerate() {
        if i + 1 == middle.len() {
            return rest.ends_with(part);
        }
        match rest.find(part) {
            Some(at) => rest = &rest[at + part.len()..],
            None => return false,
        }
    }
    rest.is_empty()
}

struct Rules {
    allowed: Graph,
    symbols: Vec<SymbolRule>,
}

fn rules(path: &Path) -> Rules {
    let text = std::fs::read_to_string(path).expect("read tools/dependency_check/rules.txt");
    let mut allowed = Graph::new();
    let mut symbols = Vec::new();
    let mut section = "";
    for line in text.lines().map(str::trim) {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line.starts_with('[') {
            assert!(line == "[symbol rules]", "unknown section {line}");
            section = line;
            continue;
        }
        if section == "[symbol rules]" {
            let words: Vec<&str> = line.split_whitespace().collect();
            assert!(
                words.len() > 2 && matches!(words[1], "only" | "never"),
                "a symbol rule reads `<symbol> only|never <files>...`: {line}"
            );
            symbols.push(SymbolRule {
                text: line.to_owned(),
                symbol: words[0].to_owned(),
                only: words[1] == "only",
                files: words[2..].iter().map(|word| (*word).to_owned()).collect(),
            });
            continue;
        }
        let (name, deps) = line
            .split_once(':')
            .unwrap_or_else(|| panic!("rule without ':': {line}"));
        let entry = allowed.entry(name.trim().to_owned()).or_default();
        for dep in deps.split_whitespace() {
            entry.insert(dep.to_owned(), 0);
        }
    }
    Rules { allowed, symbols }
}

fn dot(graph: &Graph, title: &str, cluster: bool, labels: bool) -> String {
    let red: BTreeSet<String> = cycles(graph).into_iter().flatten().collect();
    let mut out = format!(
        "digraph \"{title}\" {{\n  graph [rankdir=LR, label=\"{title}\", labelloc=t, fontname=\"Helvetica\"];\n  node [shape=box, fontname=\"Helvetica\", fontsize=10];\n  edge [color=\"#00000040\"];\n"
    );
    let mut groups: BTreeMap<String, Vec<&String>> = BTreeMap::new();
    for node in graph.keys().chain(graph.values().flat_map(BTreeMap::keys)) {
        let key = if cluster {
            component(node)
        } else {
            String::new()
        };
        let members = groups.entry(key).or_default();
        if !members.contains(&node) {
            members.push(node);
        }
    }
    for (i, (key, members)) in groups.iter().enumerate() {
        if cluster {
            out += &format!("  subgraph \"cluster_{i}\" {{\n    label=\"{key}\"; style=rounded; color=\"#888888\";\n");
        }
        for node in members {
            let label = if cluster {
                node.rsplit('/').next().unwrap()
            } else {
                node.as_str()
            };
            let style = if red.contains(*node) {
                ", color=red, penwidth=2"
            } else {
                ""
            };
            out += &format!("    \"{node}\" [label=\"{label}\"{style}];\n");
        }
        if cluster {
            out += "  }\n";
        }
    }
    let scc_of: BTreeMap<String, usize> = cycles(graph)
        .into_iter()
        .enumerate()
        .flat_map(|(i, members)| members.into_iter().map(move |m| (m, i)))
        .collect();
    for (from, targets) in graph {
        for (to, count) in targets {
            let mut attrs = Vec::new();
            if scc_of.get(from).is_some_and(|c| scc_of.get(to) == Some(c)) {
                attrs.push("color=red, penwidth=2".to_owned());
            }
            if labels {
                attrs.push(format!("label=\"{count}\""));
            }
            out += &format!("  \"{from}\" -> \"{to}\" [{}];\n", attrs.join(", "));
        }
    }
    out + "}\n"
}

fn main() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (dot_dir, current) = match args.as_slice() {
        [] => (None, false),
        [flag] if flag == "--current" => (None, true),
        [flag, dir] if flag == "--dot" => (Some(PathBuf::from(dir)), false),
        _ => panic!("usage: dependency_check [--current | --dot <directory>]"),
    };
    let (files, references, symbols) = file_graph(&root, &root.join("target/dependency_check"));
    let components = collapse(&files);
    if current {
        for (name, deps) in &components {
            let names: Vec<_> = deps.keys().map(String::as_str).collect();
            println!("{name}: {}", names.join(" "));
        }
        for cycle in cycles(&files) {
            println!("# file cycle: {}", cycle.join(" "));
        }
        return;
    }
    let rules = rules(&root.join("tools/dependency_check/rules.txt"));
    let mut failures = Vec::new();

    for (name, deps) in &components {
        let Some(allowed) = rules.allowed.get(name) else {
            failures.push(format!("component {name} has no rule"));
            continue;
        };
        for (dep, count) in deps {
            if !allowed.contains_key(dep) {
                let example = files
                    .iter()
                    .filter(|(from, _)| component(from) == *name)
                    .find_map(|(from, targets)| {
                        targets
                            .keys()
                            .find(|to| component(to) == *dep)
                            .map(|to| (from, to))
                    })
                    .map(|(from, to)| format!(" (e.g. {from} uses {to})"))
                    .unwrap_or_default();
                failures.push(format!(
                    "{name} uses {dep}, which its rule does not allow: {count} references{example}"
                ));
            }
        }
    }
    for (name, deps) in &rules.allowed {
        if !components.contains_key(name) {
            failures.push(format!("rule for unknown component {name}"));
        }
        for dep in deps.keys() {
            if !rules.allowed.contains_key(dep) {
                failures.push(format!("rule for {name} names unknown component {dep}"));
            }
        }
    }
    for cycle in cycles(&rules.allowed) {
        failures.push(format!("the rules contain a cycle: {}", cycle.join(" ")));
    }
    for (name, deps) in &rules.allowed {
        for dep in deps.keys() {
            if let (Some(a), Some(b)) = (version(name), version(dep)) {
                if a != b {
                    failures.push(format!(
                        "the rules let {a} component {name} use {b} component {dep}"
                    ));
                }
            }
        }
    }
    for (from, targets) in &files {
        for to in targets.keys() {
            if let (Some(a), Some(b)) = (version(from), version(to)) {
                if a != b {
                    failures.push(format!("{a} file {from} uses {b} file {to}"));
                }
            }
        }
    }
    for cycle in cycles(&files) {
        failures.push(format!("file cycle: {}", cycle.join(" ")));
    }
    for (from, targets) in &files {
        if let Some(own) = role(from) {
            for to in targets.keys() {
                if role(to).is_some_and(|other| other != own) {
                    failures.push(format!(
                        "{own} file {from} uses {} file {to}",
                        role(to).unwrap()
                    ));
                }
            }
        }
    }
    for rule in &rules.symbols {
        // A pattern that names no crate symbol is a typo, not a passing rule.
        if !symbols.iter().any(|symbol| glob(&rule.symbol, symbol)) {
            failures.push(format!("symbol rule names no symbol: `{}`", rule.text));
        }
        for r in references.iter().filter(|r| glob(&rule.symbol, &r.symbol)) {
            let listed = rule.files.iter().any(|pattern| glob(pattern, &r.from));
            if listed != rule.only {
                failures.push(format!(
                    "{}:{} references {} (defined in {}), against `{}`",
                    r.from, r.line, r.symbol, r.to, rule.text
                ));
            }
        }
    }

    if let Some(dir) = dot_dir {
        std::fs::create_dir_all(&dir).expect("create the dot directory");
        std::fs::write(
            dir.join("files.dot"),
            dot(&files, "longfellow-zk files", true, false),
        )
        .expect("write files.dot");
        std::fs::write(
            dir.join("components.dot"),
            dot(&components, "longfellow-zk components", false, true),
        )
        .expect("write components.dot");
    }
    println!(
        "{} files, {} file edges; {} components, {} component edges",
        files.len(),
        files.values().map(BTreeMap::len).sum::<usize>(),
        components.len(),
        components.values().map(BTreeMap::len).sum::<usize>(),
    );
    // A `use ... as` alias yields two occurrences of the same reference.
    failures.dedup();
    for failure in &failures {
        eprintln!("{failure}");
    }
    if !failures.is_empty() {
        eprintln!("dependency check failed: {} problems", failures.len());
        std::process::exit(1);
    }
}
