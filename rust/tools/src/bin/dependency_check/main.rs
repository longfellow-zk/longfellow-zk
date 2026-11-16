// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Dependency check over rust-analyzer's resolved index of the library crate.
//!
//! ```sh
//! cargo run --release -p longfellow-zk-tools --bin dependency_check [-- --dot <directory>]
//! ```
//!
//! The tool runs `rust-analyzer scip` on the workspace in `rust/` (with the
//! library's `testonly` feature) and builds the file graph of the library
//! (`rust/src`; the tools in `rust/tools` are not part of it): an edge A -> B means a
//! reference written in file A resolves to an item defined in file B. Every
//! reference counts, in signatures, bodies, imports and macro output, and it
//! is attributed to the file where it is written, so a method defined in
//! `prover.rs` makes `prover.rs` depend on its type, not the reverse. Module
//! names in paths, function-local symbols, macros, symbols defined outside the
//! crate, test and bench files, and the crate root `src/lib.rs` (which only
//! mounts modules and defines the `cfg_*!` wrappers) are not edges.
//!
//! A component is a module path listed in `rules.txt` beside this source
//! (for example `runtime/v2/zk`: `src/runtime/v2/zk.rs` and everything under
//! `src/runtime/v2/zk/`); a file belongs to the longest listed component its
//! module path starts with. The rules list every component with the components
//! it may use. The check fails when
//! - a component is missing from the rules, or a rule names no component;
//! - a component uses one that its rule does not list;
//! - the rules themselves contain a cycle, or allow an edge between a v1 and a v2 component;
//! - a v1 file uses a v2 file or the reverse. A file belongs to version vN when a directory on its
//!   path, or a `_`-separated word of its name, is `vN` (`runtime/v2/...`, `core/proto/v1/...`,
//!   `v2_segment.rs`);
//! - the file graph has a cycle: no file may depend on itself through others;
//! - a file of one proof role uses a file of the other. A file belongs to a role when a directory
//!   on its path, or a `_`-separated word of its name, is `prover` or `verifier` and nothing names
//!   the other (`zk/prover/...`, `prover_commitment.rs`);
//! - a compile-time file uses a run-time file or the reverse, or a shared file uses either. The
//!   phase of every file is fixed by [`phase`] in this source, not by the editable rules, so
//!   loosening it takes a reviewed code change;
//! - a prover/verifier contract (`runtime::vN::proto`) uses anything but core, `util`, the run-time
//!   algebra and its framing (the v1 subfield or the v2 transcript), fixed by [`proto_allows`];
//! - a library file without a role gates anything but a module declaration or a `use` on a proof
//!   role or the compile phase ([`item_gates`]); items that need a role live in a file of that
//!   role. The modules of [`ITEM_GATES_PENDING`] are exempt until they are converted;
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

/// Files outside the library's `src` (the benches and the tools), test files
/// (a `tests` path segment or `tests.rs`), and the crate root, which only
/// mounts modules and defines the `cfg_*!` wrappers.
fn excluded(path: &str) -> bool {
    path == "src/lib.rs"
        || !path.starts_with("src/")
        || path
            .split('/')
            .any(|part| part == "tests" || part == "tests.rs")
}

/// The module path of a file: `src/runtime/v2/zk/joint.rs` is `runtime/v2/zk/joint`.
fn module_path(path: &str) -> &str {
    let relative = path.strip_prefix("src/").unwrap_or(path);
    relative.strip_suffix(".rs").unwrap_or(relative)
}

/// The components listed in the rules. A file belongs to the longest listed
/// component its module path starts with; a file under none of them is its
/// own unlisted component, which the check reports. A parent component, one
/// with listed components below it (`runtime/v2`), owns only its root file:
/// any other file under it is unlisted until it gets its own rule, so a new
/// module cannot join a facade unnoticed.
struct Components(BTreeSet<String>);
impl Components {
    fn of(&self, path: &str) -> String {
        let module = module_path(path);
        let mut prefix = module;
        loop {
            if self.0.contains(prefix) {
                let parent = self
                    .0
                    .range(format!("{prefix}/")..)
                    .next()
                    .is_some_and(|c| c.starts_with(&format!("{prefix}/")));
                if parent && prefix != module {
                    return module.to_owned();
                }
                return prefix.to_owned();
            }
            match prefix.rfind('/') {
                Some(end) => prefix = &prefix[..end],
                None => return module.to_owned(),
            }
        }
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

/// Which side of the compile/run-time split a file is on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    /// Circuit construction and compilation.
    Compile,
    /// Proving, verification and native witness derivation.
    Runtime,
    /// Contracts both sides agree on; uses neither.
    Shared,
    /// Test-only code that connects native witnesses to circuit wires
    /// (`cfg_testonly!`): may use both sides.
    Bridge,
    /// Programs and drivers that run both sides, and facades that only
    /// mount and re-export modules: may use both sides.
    Neutral,
}

/// The applications, each with its native parsers. An application module
/// (`mdoc`) mirrors the library's layering below it: see
/// [`application_phase`].
const APPLICATIONS: [(&str, &[&str]); 1] = [("mdoc", &["cbor"])];

/// The application a module path belongs to: its module path below the
/// application, and the application's native parsers.
fn application(module: &str) -> Option<(&str, &'static [&'static str])> {
    APPLICATIONS.iter().find_map(|&(name, parsers)| {
        module
            .strip_prefix(name)
            .and_then(|rest| rest.strip_prefix('/'))
            .map(|rest| (rest, parsers))
    })
}

/// The phase of a library file. A first-match table: listing a file in the
/// wrong class, or adding a class, is a design change to review here.
fn phase(path: &str) -> Phase {
    use Phase::*;
    let m = module_path(path);
    if let Some((rest, parsers)) = application(m) {
        return application_phase(path, rest, parsers);
    }
    let under = |root: &str| m == root || m.starts_with(&format!("{root}/"));
    if under("bin") {
        // Drivers that compile and run.
        Neutral
    } else if m == "runtime" {
        // A module facade that only mounts and re-exports.
        Neutral
    } else if under("core") || under("util") {
        // Contracts and dependency-free helpers.
        Shared
    } else if under("compile") {
        Compile
    } else if under("runtime") {
        Runtime
    } else if let Some(rest) = m.strip_prefix("circuits/") {
        circuit_phase(path, rest)
    } else {
        panic!("{path} has no phase; classify it in `phase`");
    }
}

/// The phase of a file of an application, by its module path `rest` below
/// the application: the same layering as the library's, with the
/// application's own contract, test vectors, stored artifacts, development
/// provider and native `parsers`.
fn application_phase(path: &str, rest: &str, parsers: &[&str]) -> Phase {
    use Phase::*;
    let under = |root: &str| rest == root || rest.starts_with(&format!("{root}/"));
    if under("development_provider") || rest == "artifacts" {
        // The development provider compiles and runs; the artifacts are
        // the stored circuits and proofs.
        Neutral
    } else if rest == "circuits" {
        // A module facade that only mounts and re-exports.
        Neutral
    } else if under("proto") || under("testcases") {
        // The application's contract and test vectors.
        Shared
    } else if under("compile") {
        Compile
    } else if under("runtime") || parsers.iter().any(|parser| under(parser)) {
        // The application's run time and its native parsers.
        Runtime
    } else if let Some(circuit) = rest.strip_prefix("circuits/") {
        circuit_phase(path, circuit)
    } else {
        panic!("{path} has no phase; classify it in `application_phase`");
    }
}

/// A circuit module `<name>[/<half>[/...]]` below `circuits` or
/// `mdoc::circuits`. The root `<name>` is a facade; a half, and every module
/// below it, takes the half's phase. A half of an unknown kind has no phase
/// until it is classified here.
fn circuit_phase(path: &str, rest: &str) -> Phase {
    use Phase::*;
    let mut segments = rest.split('/');
    let name = segments.next().unwrap_or(rest);
    let half = segments.next();
    match half.unwrap_or(name) {
        "circuit" | "allocate" | "fields" => Compile,
        // Native witness halves.
        "concrete" => Runtime,
        "evaluate" => Bridge,
        // The witness layout that the circuit and the native witness share,
        // with the constants and point types it is built from.
        "shape" => Shared,
        // A circuit's root module mounts and re-exports its halves.
        _ if half.is_none() => Neutral,
        _ => panic!("{path} has no phase; classify its kind in `circuit_phase`"),
    }
}

/// Whether a file is a facade, whose only content may be module declarations
/// and re-exports: a neutral circuit root (of the library or of an
/// application), `runtime`, or an application's `circuits`.
fn is_facade(path: &str) -> bool {
    let m = module_path(path);
    // The module path within its application, if it has one.
    let local = application(m).map_or(m, |(rest, _)| rest);
    let circuit_root = local
        .strip_prefix("circuits/")
        .is_some_and(|rest| !rest.contains('/'));
    let facade = m == "runtime" || (local != m && local == "circuits");
    phase(path) == Phase::Neutral && (circuit_root || facade)
}

/// The first statement in a facade's source that is not a module
/// declaration, a `use`, an attribute or a `cfg_*!` block around those, if
/// any. A facade with items could run either phase's code through trait
/// impls that no reference names, out of reach of the phase check.
fn facade_item(text: &str) -> Option<String> {
    let src = strip_comments(text);
    let mut rest = src.trim_start();
    let mut depth = 0usize;
    while !rest.is_empty() {
        if let Some(r) = rest.strip_prefix('}').filter(|_| depth > 0) {
            depth -= 1;
            rest = r.trim_start();
        } else if rest.starts_with('#') {
            // An attribute: skip to its closing bracket.
            let mut brackets = 0usize;
            let mut end = rest.len();
            for (i, c) in rest.char_indices() {
                match c {
                    '[' => brackets += 1,
                    ']' => {
                        brackets -= 1;
                        if brackets == 0 {
                            end = i + 1;
                            break;
                        }
                    }
                    _ => {}
                }
            }
            rest = rest[end..].trim_start();
        } else if let Some(r) = rest
            .strip_prefix("cfg_")
            .and_then(|r| r.split_once('!'))
            .filter(|(name, _)| name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'))
            .and_then(|(_, r)| r.trim_start().strip_prefix('{'))
        {
            depth += 1;
            rest = r.trim_start();
        } else {
            let item = match rest.strip_prefix("pub") {
                Some(after) => match after.trim_start().strip_prefix('(') {
                    Some(scope) => scope.split_once(')').map_or(scope, |(_, tail)| tail),
                    None => after,
                },
                None => rest,
            }
            .trim_start();
            if !(item.starts_with("mod ") || item.starts_with("use ")) {
                return Some(rest.lines().next().unwrap_or(rest).to_owned());
            }
            let end = rest.find(';').map_or(rest.len(), |i| i + 1);
            rest = rest[end..].trim_start();
        }
    }
    None
}

/// The features whose gates select a proof role (`_role` is any role) or the
/// compile phase.
const GATE_FEATURES: [&str; 4] = ["prover", "verifier", "_role", "compiler"];

/// The `cfg_*!` wrappers of those gates.
const GATE_MACROS: [&str; 5] = [
    "cfg_prover!",
    "cfg_verifier!",
    "cfg_role!",
    "cfg_compiler!",
    "cfg_prover_or_compiler!",
];

/// The modules whose item-level role gates are converted when they are next
/// edited (AGENTS.md), and the frozen v1 run time, converted only on request.
/// Remove an entry once its files gate only module lines; add none.
const ITEM_GATES_PENDING: [&str; 7] = [
    "mdoc/runtime/v1",
    "mdoc/runtime/v2",
    "runtime/v1",
    "runtime/v2/foreign",
    "runtime/v2/sumcheck",
    "runtime/v2/transcript",
    "runtime/v2/zk",
];

/// Whether `path` may gate items on a role: a binary, a file that [`role`]
/// gives a role, or one under a module of [`ITEM_GATES_PENDING`].
fn may_gate_items(path: &str) -> bool {
    let m = module_path(path);
    m.starts_with("bin/")
        || role(path).is_some()
        || ITEM_GATES_PENDING
            .iter()
            .any(|root| m == *root || m.starts_with(&format!("{root}/")))
}

/// The role and phase gates on anything but a module declaration or a `use`:
/// for each, its line (from 1) and the gated item's first line. Such a gate
/// belongs on the module line of a file of that role (AGENTS.md).
fn item_gates(text: &str) -> Vec<(usize, String)> {
    let lines: Vec<&str> = text.lines().collect();
    let gates = |attribute: &str| {
        attribute.starts_with("#[cfg(")
            && GATE_FEATURES
                .iter()
                .any(|f| attribute.contains(&format!("feature = \"{f}\"")))
    };
    // A module declaration or a `use`, after its visibility.
    let declares = |statement: &str| {
        let unqualified = match statement.strip_prefix("pub") {
            Some(after) => match after.trim_start().strip_prefix('(') {
                Some(scope) => scope.split_once(')').map_or(scope, |(_, rest)| rest),
                None => after,
            },
            None => statement,
        }
        .trim_start();
        unqualified.starts_with("mod ") || unqualified.starts_with("use ")
    };
    let mut found = Vec::new();
    // The line of a gate whose item is still to come.
    let mut gate: Option<usize> = None;
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim();
        if line.is_empty() || line.starts_with("//") {
            i += 1;
            continue;
        }
        if line.starts_with("#[") {
            // An attribute, possibly over several lines, possibly followed
            // by its item on the same line.
            let mut attribute = String::new();
            let mut depth = 0isize;
            let mut rest = String::new();
            let start = i;
            'attribute: while i < lines.len() {
                for (at, c) in lines[i].trim().char_indices() {
                    match c {
                        '[' => depth += 1,
                        ']' => {
                            depth -= 1;
                            if depth == 0 {
                                let last = lines[i].trim();
                                attribute.push_str(&last[..=at]);
                                rest = last[at + 1..].trim().to_owned();
                                break 'attribute;
                            }
                        }
                        _ => {}
                    }
                }
                attribute.push_str(lines[i].trim());
                attribute.push(' ');
                i += 1;
            }
            i += 1;
            if gates(&attribute) && gate.is_none() {
                gate = Some(start);
            }
            if rest.is_empty() {
                continue;
            }
            if let Some(at) = gate.take() {
                if !declares(&rest) {
                    found.push((at + 1, rest));
                }
            }
            continue;
        }
        if let Some(at) = gate.take() {
            if !declares(line) {
                found.push((at + 1, line.to_owned()));
            }
        }
        if GATE_MACROS.iter().any(|m| line.starts_with(m)) && line.contains('{') {
            // A wrapper block: everything up to its closing brace.
            let start = i;
            let mut block = String::new();
            let mut depth = 0isize;
            'block: while i < lines.len() {
                for c in lines[i].chars() {
                    match c {
                        '{' => depth += 1,
                        '}' => {
                            depth -= 1;
                            if depth == 0 {
                                block.push_str(lines[i]);
                                break 'block;
                            }
                        }
                        _ => {}
                    }
                }
                block.push_str(lines[i]);
                block.push('\n');
                i += 1;
            }
            let inner = block
                .split_once('{')
                .and_then(|(_, r)| r.rsplit_once('}'))
                .map_or("", |(inner, _)| inner);
            if let Some(item) = facade_item(inner) {
                found.push((start + 1, item));
            }
        }
        i += 1;
    }
    found
}

/// Source without `//` and `/* */` comments (string literals do not occur in
/// facades, so they are not tracked).
fn strip_comments(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while !rest.is_empty() {
        if let Some(r) = rest.strip_prefix("//") {
            rest = r.find('\n').map_or("", |i| &r[i..]);
        } else if let Some(r) = rest.strip_prefix("/*") {
            rest = r.find("*/").map_or("", |i| &r[i + 2..]);
            out.push(' ');
        } else {
            let c = rest.chars().next().unwrap();
            out.push(c);
            rest = &rest[c.len_utf8()..];
        }
    }
    out
}

/// Whether a file of phase `from` may use a file of phase `to`. References
/// resolve to the defining file, so a use through a facade is an edge to
/// the file behind it; a direct edge to a facade or driver is a reference
/// to an item defined there.
fn phase_allows(from: Phase, to: Phase) -> bool {
    use Phase::*;
    match (from, to) {
        (Bridge | Neutral, _) => true,
        (_, Shared) => true,
        (Compile, Compile) | (Runtime, Runtime) => true,
        (Compile | Runtime | Shared, _) => false,
    }
}

/// Whether the parent module declares `mod evaluate;` only for tests: every
/// declaration lies inside `cfg_testonly! { ... }` or under `#[cfg(test)]`,
/// and there is at least one. A bridge may use both phases only because it is
/// never built into a library user's binary, so one ungated declaration (say
/// under `#[cfg(not(test))]`) next to a gated one fails.
fn bridge_is_test_only(root: &Path, path: &str) -> bool {
    let Some(parent) = Path::new(path).parent() else {
        return false;
    };
    let Ok(text) = std::fs::read_to_string(root.join(parent).with_extension("rs")) else {
        return false;
    };
    let mut depth = 0usize;
    let mut testonly_at = None;
    let mut cfg_test = false;
    let mut declared = false;
    for line in text.lines() {
        let t = line.trim();
        if t.starts_with("cfg_testonly!") && t.ends_with('{') {
            testonly_at = Some(depth);
        }
        if t.ends_with("mod evaluate;") {
            if testonly_at.is_none() && !cfg_test {
                return false;
            }
            declared = true;
        }
        cfg_test = t == "#[cfg(test)]";
        depth += t.matches('{').count();
        depth = depth.saturating_sub(t.matches('}').count());
        if testonly_at.is_some_and(|d| depth <= d) && t.contains('}') {
            testonly_at = None;
        }
    }
    declared
}

/// The prover/verifier contracts, `runtime::vN::proto`, use only the shared
/// layers below them: core, the run-time algebra, and the framing they are
/// defined over. Like [`phase`], this is fixed here, not in the rules.
fn proto_allows(from: &str, to: &str) -> bool {
    let (user, used) = (module_path(from), module_path(to));
    let under = |m: &str, root: &str| m == root || m.starts_with(&format!("{root}/"));
    let version = if under(user, "runtime/v1/proto") {
        "v1"
    } else if under(user, "runtime/v2/proto") {
        "v2"
    } else {
        return true;
    };
    let framing = if version == "v1" {
        "runtime/v1/subfield"
    } else {
        "runtime/v2/transcript"
    };
    under(used, &format!("runtime/{version}/proto"))
        || under(used, "core")
        || under(used, "util")
        || under(used, "runtime/algebra")
        || under(used, framing)
}

/// The proof role a path belongs to, if any: as for [`version`], a directory on
/// its path or a `_`-separated word of its name is `prover` or `verifier`, and
/// no word names the other role (`zk/prover/...`, `prover_commitment.rs`).
fn role(path: &str) -> Option<&'static str> {
    let (dirs, file) = path.rsplit_once('/').unwrap_or(("", path));
    let stem = file.strip_suffix(".rs").unwrap_or(file);
    let mut words = dirs.split('/').chain(stem.split('_'));
    match (
        words.clone().any(|w| w == "prover"),
        words.any(|w| w == "verifier"),
    ) {
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
        r#"{"cargo": {"features": ["longfellow-zk/testonly"]}}"#,
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
    // else to the definition sharing the longest path prefix with it.
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
                // The definition sharing the longest path prefix with `from`.
                *candidates
                    .iter()
                    .max_by_key(|c| {
                        c.bytes()
                            .zip(from.bytes())
                            .take_while(|(a, b)| a == b)
                            .count()
                    })
                    .unwrap()
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

fn collapse(files: &Graph, names: &Components) -> Graph {
    let mut components = Graph::new();
    for (from, targets) in files {
        let a = names.of(from);
        components.entry(a.clone()).or_default();
        for (to, count) in targets {
            let b = names.of(to);
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
    let text = std::fs::read_to_string(path).expect("read the dependency rules.txt");
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

/// `clusters`: group the nodes (files) by component.
fn dot(graph: &Graph, title: &str, clusters: Option<&Components>, labels: bool) -> String {
    let cluster = clusters.is_some();
    let red: BTreeSet<String> = cycles(graph).into_iter().flatten().collect();
    let mut out = format!(
        "digraph \"{title}\" {{\n  graph [rankdir=LR, label=\"{title}\", labelloc=t, fontname=\"Helvetica\"];\n  node [shape=box, fontname=\"Helvetica\", fontsize=10];\n  edge [color=\"#00000040\"];\n"
    );
    let mut groups: BTreeMap<String, Vec<&String>> = BTreeMap::new();
    for node in graph.keys().chain(graph.values().flat_map(BTreeMap::keys)) {
        let key = clusters.map_or(String::new(), |names| names.of(node));
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
    // This tool is in `rust/tools`; the library it checks is `rust/`.
    let tools = Path::new(env!("CARGO_MANIFEST_DIR"));
    let root = tools
        .parent()
        .expect("the tools crate lies inside the library's directory")
        .to_path_buf();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (dot_dir, current) = match args.as_slice() {
        [] => (None, false),
        [flag] if flag == "--current" => (None, true),
        [flag, dir] if flag == "--dot" => (Some(PathBuf::from(dir)), false),
        _ => panic!("usage: dependency_check [--current | --dot <directory>]"),
    };
    let rules = rules(&tools.join("src/bin/dependency_check/rules.txt"));
    let names = Components(rules.allowed.keys().cloned().collect());
    let (files, references, symbols) = file_graph(&root, &root.join("target/dependency_check"));
    let components = collapse(&files, &names);
    if current {
        for (name, deps) in &components {
            let used: Vec<_> = deps.keys().map(String::as_str).collect();
            println!("{name}: {}", used.join(" "));
        }
        for cycle in cycles(&files) {
            println!("# file cycle: {}", cycle.join(" "));
        }
        return;
    }
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
                    .filter(|(from, _)| names.of(from) == *name)
                    .find_map(|(from, targets)| {
                        targets
                            .keys()
                            .find(|to| names.of(to) == *dep)
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
    for from in files.keys().filter(|f| f.starts_with("src/")) {
        if phase(from) == Phase::Bridge && !bridge_is_test_only(&root, from) {
            failures.push(format!("bridge {from} is not declared only for tests"));
        }
        if is_facade(from) {
            let text = std::fs::read_to_string(root.join(from)).unwrap_or_default();
            if let Some(item) = facade_item(&text) {
                failures.push(format!("facade {from} defines an item: {item}"));
            }
        }
        if !may_gate_items(from) {
            let text = std::fs::read_to_string(root.join(from)).unwrap_or_default();
            for (line, item) in item_gates(&text) {
                failures.push(format!(
                    "{from}:{line} gates an item on a role or phase; move it to a file of \
                     that role: {item}"
                ));
            }
        }
    }
    for (from, targets) in &files {
        if !from.starts_with("src/") {
            continue;
        }
        for to in targets.keys().filter(|to| to.starts_with("src/")) {
            let (a, b) = (phase(from), phase(to));
            if !phase_allows(a, b) {
                failures.push(format!("{a:?} file {from} uses {b:?} file {to}"));
            }
            if !proto_allows(from, to) {
                failures.push(format!("prover/verifier contract {from} uses {to}"));
            }
        }
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
            dot(&files, "longfellow-zk files", Some(&names), false),
        )
        .expect("write files.dot");
        std::fs::write(
            dir.join("components.dot"),
            dot(&components, "longfellow-zk components", None, true),
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

#[cfg(test)]
mod tests;
