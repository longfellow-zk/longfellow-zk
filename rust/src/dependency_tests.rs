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

//! Repository module graph, phase boundaries, and v1/v2 isolation checks.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

/// Ignore comments and literals, then remove individual test-only items. Keeping
/// offsets intact makes delimiter matching independent of quoted Rust syntax.
fn production_code(source: &str) -> String {
    let bytes = source.as_bytes();
    let mut code = bytes.to_vec();
    let mut cursor = 0;
    while cursor < bytes.len() {
        let start = cursor;
        if bytes[cursor..].starts_with(b"//") {
            cursor += bytes[cursor..]
                .iter()
                .position(|&b| b == b'\n')
                .unwrap_or(bytes.len() - cursor);
        } else if bytes[cursor..].starts_with(b"/*") {
            cursor += 2;
            let mut depth = 1;
            while depth > 0 {
                assert!(cursor < bytes.len(), "unterminated source comment");
                if bytes[cursor..].starts_with(b"/*") {
                    depth += 1;
                    cursor += 2;
                } else if bytes[cursor..].starts_with(b"*/") {
                    depth -= 1;
                    cursor += 2;
                } else {
                    cursor += 1;
                }
            }
        } else if let Some(end) = literal_end(source, cursor) {
            cursor = end;
        } else {
            cursor += 1;
            continue;
        }
        mask(&mut code[start..cursor]);
    }

    cursor = 0;
    while cursor < code.len() {
        if code[cursor..].starts_with(b"#[") {
            let end = cursor
                + code[cursor..]
                    .iter()
                    .position(|&b| b == b']')
                    .expect("unterminated source attribute")
                + 1;
            if code[cursor..end]
                .iter()
                .copied()
                .filter(|b| !b.is_ascii_whitespace())
                .eq(b"#[cfg(test)]".iter().copied())
            {
                let item_end = test_item_end(&code, end);
                mask(&mut code[cursor..item_end]);
                cursor = item_end;
                continue;
            }
        }
        cursor += 1;
    }
    String::from_utf8(code).expect("mask preserves UTF-8")
}

fn mask(bytes: &mut [u8]) {
    for byte in bytes {
        if *byte != b'\n' {
            *byte = b' ';
        }
    }
}

/// Recognize ordinary/raw strings and character literals without treating a
/// lifetime such as `'a` as a quote. Byte-string prefixes need no special case.
fn literal_end(source: &str, start: usize) -> Option<usize> {
    let bytes = source.as_bytes();
    let quote = bytes[start];
    if quote == b'r' {
        let mut cursor = start + 1;
        while bytes.get(cursor) == Some(&b'#') {
            cursor += 1;
        }
        if bytes.get(cursor) == Some(&b'"') {
            let ending = format!("\"{}", "#".repeat(cursor - start - 1));
            let end = source[cursor + 1..]
                .find(&ending)
                .expect("unterminated raw string");
            return Some(cursor + 1 + end + ending.len());
        }
        return None;
    }
    if quote == b'\'' && bytes.get(start + 1) != Some(&b'\\') {
        let character = source[start + 1..].chars().next()?;
        if bytes.get(start + 1 + character.len_utf8()) != Some(&b'\'') {
            return None;
        }
    } else if quote != b'\'' && quote != b'"' {
        return None;
    }
    let mut cursor = start + 1;
    while cursor < bytes.len() {
        match bytes[cursor] {
            b'\\' => cursor += 2,
            value if value == quote => return Some(cursor + 1),
            _ => cursor += 1,
        }
    }
    panic!("unterminated source literal");
}

/// Skip exactly one attributed item, including an inline module or a macro
/// invocation; production declarations after that item remain visible.
fn test_item_end(code: &[u8], start: usize) -> usize {
    let mut depth = 0usize;
    for (offset, &byte) in code[start..].iter().enumerate() {
        match byte {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => {
                depth = depth.checked_sub(1).expect("unbalanced source item");
                if byte == b'}' && depth == 0 {
                    return start + offset + 1;
                }
            }
            b';' if depth == 0 => return start + offset + 1,
            _ => {}
        }
    }
    panic!("unterminated test-only source item");
}

#[test]
fn production_after_test_items_is_checked() {
    let source = r##"
        use crate::runtime::algebra;
        #[cfg ( test )]
        #[path = "test_support.rs"] mod support;
        use crate::runtime::zk_v2;
        #[cfg(test)] mod tests { fn sample() { let _ = "}"; } }
        use crate::runtime::sumcheck_v1;
    "##;
    assert_eq!(
        extract_crate_deps(&production_code(source)),
        BTreeSet::from([
            "runtime::algebra".to_owned(),
            "runtime::zk_v2".to_owned(),
            "runtime::sumcheck_v1".to_owned(),
        ])
    );
}

#[test]
fn source_literals_and_comments_cannot_hide_or_invent_dependencies() {
    let source = r###"
        // crate::compile::logic #[cfg(test)]
        /* nested /* comment */ crate::compile::algebra */
        const MESSAGE: &str = r#"crate::compile::compiler #[cfg(test)]"#;
        fn sample<'a>(input: &'a [u8]) { let _ = ('}', '\'', b'[', "\\\""); }
        use crate::runtime::algebra;
    "###;
    assert_eq!(
        extract_crate_deps(&production_code(source)),
        BTreeSet::from(["runtime::algebra".to_owned(),])
    );
}

/// Recursively collects all `.rs` source files under `dir`, skipping standalone binary targets
/// (`bin/`).
fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = fs::read_dir(dir).unwrap_or_else(|error| {
        panic!(
            "cannot inspect dependency sources in {}: {error}",
            dir.display()
        )
    });
    for entry in entries {
        let path = entry.expect("read dependency source entry").path();
        if path.is_dir() {
            if path.file_name().and_then(|n| n.to_str()) == Some("bin") {
                continue;
            }
            collect_rs_files(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

/// Recursively parses a path or braced `use` tree following `crate::` (e.g.,
/// `crate::runtime::proto`, `crate::runtime::{merkle::..., proto::...}`, or
/// `crate::{circuits::ec::..., compile::{algebra::..., logic::...}}`) and records every
/// referenced `<layer>::<submodule>` (or `util`) into `deps`.
fn parse_crate_tree(raw: &str, layer_prefix: Option<&str>, deps: &mut BTreeSet<String>) {
    let s = raw.trim_start();
    if let Some(inner) = s.strip_prefix('{') {
        let mut depth = 1usize;
        let mut item_start = 0;
        for (idx, ch) in inner.char_indices() {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        parse_crate_tree(&inner[item_start..idx], layer_prefix, deps);
                        break;
                    }
                }
                ',' if depth == 1 => {
                    parse_crate_tree(&inner[item_start..idx], layer_prefix, deps);
                    item_start = idx + 1;
                }
                _ => {}
            }
        }
        return;
    }

    let ident: String = s
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect();
    if ident.is_empty() {
        return;
    }
    let rest = &s[ident.len()..];
    match layer_prefix {
        None => {
            if ident == "util" {
                deps.insert("util".to_string());
            } else if matches!(
                ident.as_str(),
                "core" | "runtime" | "compile" | "circuits" | "mdoc" | "tools"
            ) {
                if let Some(after_colons) = rest.strip_prefix("::") {
                    parse_crate_tree(after_colons, Some(&ident), deps);
                }
            }
        }
        Some(layer) => {
            if ident != "self" {
                deps.insert(format!("{layer}::{ident}"));
            }
        }
    }
}

/// Scans Rust source text for `crate::<layer>::<submodule>` paths (including braced
/// `use crate::{...}` trees) and returns the set of top-level sub-modules referenced by `src`.
fn extract_crate_deps(source: &str) -> BTreeSet<String> {
    let normalized = source.replace("longfellow_zk::", "crate::");
    let src = normalized.as_str();
    let mut deps = BTreeSet::new();
    let bytes = src.as_bytes();
    let needle = b"crate::";
    let mut i = 0;
    while i + needle.len() <= bytes.len() {
        if &bytes[i..i + needle.len()] == needle
            && (i == 0 || !(bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_'))
        {
            let rest = &src[i + needle.len()..];
            parse_crate_tree(rest, None, &mut deps);
            i += needle.len();
        } else {
            i += 1;
        }
    }
    deps.into_iter()
        .map(|dep| {
            if matches!(dep.as_str(), "mdoc::v1" | "mdoc::v2") {
                "mdoc::runtime".to_owned()
            } else {
                dep
            }
        })
        .collect()
}

/// Performs depth-first cycle detection starting from `node` in `graph`.
/// Returns `Some(cycle_path)` if a directed cycle is found, or `None` if the subgraph is
/// acyclic.
fn has_cycle(
    node: &str,
    graph: &BTreeMap<String, BTreeSet<String>>,
    visiting: &mut BTreeSet<String>,
    visited: &mut BTreeSet<String>,
    path: &mut Vec<String>,
) -> Option<Vec<String>> {
    if visiting.contains(node) {
        path.push(node.to_string());
        return Some(path.clone());
    }
    if visited.contains(node) {
        return None;
    }
    visiting.insert(node.to_string());
    path.push(node.to_string());
    if let Some(neighbors) = graph.get(node) {
        for next in neighbors {
            if let Some(cycle) = has_cycle(next, graph, visiting, visited, path) {
                return Some(cycle);
            }
        }
    }
    path.pop();
    visiting.remove(node);
    visited.insert(node.to_string());
    None
}

/// Verifies that:
/// 1. No production source file in any module imports a module from a higher architectural layer
///    (`util` < `core` < `runtime` < `compile` < `circuits` < `mdoc` < offline preparation < CLI).
/// 2. The full directed dependency graph across all registered sub-modules contains no cycles.
#[test]
fn test_module_dependency_dag_and_layer_boundaries() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let modules = [
        ("util", "util/src"),
        ("bench_support", "benches/support"),
        ("tools::zk_tool", "tools/zk_tool"),
        ("core::algebra", "core/algebra/src"),
        ("core::bits", "core/bits/src"),
        ("core::proto", "core/proto/src"),
        ("runtime::algebra", "runtime/algebra/src"),
        ("runtime::proto", "runtime/proto/src"),
        ("runtime::random", "runtime/random/src"),
        ("runtime::merkle", "runtime/merkle/src"),
        ("runtime::sumcheck_v1", "runtime/sumcheck-v1/src"),
        ("runtime::sumcheck_v2", "runtime/sumcheck-v2/src"),
        ("runtime::zk_v2", "runtime/zk-v2/src"),
        ("runtime::ligero", "runtime/ligero/src"),
        ("runtime::polygero", "runtime/polygero/src"),
        ("runtime::dual_packing", "runtime/dual-packing/src"),
        ("runtime::zk_v1", "runtime/zk-v1/src"),
        ("compile::algebra", "compile/algebra/src"),
        ("compile::proto", "compile/proto/src"),
        ("compile::logic", "compile/logic/src"),
        ("compile::compiler", "compile/compiler/src"),
        ("compile::polygero", "compile/polygero/src"),
        ("compile::eval", "compile/eval/src"),
        ("circuits::analog_adder", "circuits/analog_adder/src"),
        ("circuits::analog_decoder", "circuits/analog_decoder/src"),
        ("circuits::arithmetic", "circuits/arithmetic/src"),
        ("circuits::bitvec", "circuits/bitvec/src"),
        ("circuits::bit_plucker", "circuits/bit_plucker/src"),
        ("circuits::bignum", "circuits/bignum/src"),
        ("circuits::big_bitvec", "circuits/big_bitvec/src"),
        ("circuits::boolean", "circuits/boolean/src"),
        ("circuits::ec", "circuits/ec/src"),
        ("circuits::ecdsa2", "circuits/ecdsa2/src"),
        ("circuits::gf2_128", "circuits/gf2_128/src"),
        ("circuits::lookup", "circuits/lookup/src"),
        ("circuits::mac", "circuits/mac/src"),
        ("circuits::mac_gf128", "circuits/mac_gf128/src"),
        ("circuits::memcmp", "circuits/memcmp/src"),
        ("circuits::polynomial", "circuits/polynomial/src"),
        ("circuits::routing", "circuits/routing/src"),
        ("circuits::sha256", "circuits/sha256/src"),
        ("circuits::sha256msg", "circuits/sha256msg/src"),
        ("circuits::experimental", "circuits/experimental/src"),
        ("mdoc::proto", "applications/mdoc_zk/proto/src"),
        ("mdoc::circuits", "applications/mdoc_zk/circuits/src"),
        ("mdoc::compile", "applications/mdoc_zk/compile/src"),
        (
            "mdoc::development_provider",
            "applications/mdoc_zk/development_provider/src",
        ),
        ("mdoc::runtime", "applications/mdoc_zk/runtime/src"),
        ("mdoc::testcases", "applications/mdoc_zk/testcases/src"),
        ("mdoc::artifacts", "applications/mdoc_zk/artifacts/src"),
    ];

    let layer_rank = |mod_name: &str| -> u8 {
        if matches!(mod_name, "util" | "bench_support") {
            0
        } else if mod_name.starts_with("core::") {
            1
        } else if mod_name.starts_with("runtime::") {
            2
        } else if mod_name.starts_with("compile::") {
            3
        } else if mod_name.starts_with("circuits::") {
            4
        } else if mod_name == "tools::zk_tool" {
            7
        } else if mod_name == "mdoc::development_provider" {
            6
        } else if mod_name.starts_with("mdoc::") {
            5
        } else if mod_name.starts_with("tools::") {
            6
        } else {
            panic!("Unknown module {mod_name}")
        }
    };

    let mut graph: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (mod_name, rel_dir) in modules {
        let mut files = Vec::new();
        collect_rs_files(&root.join(rel_dir), &mut files);
        let mut deps = BTreeSet::new();
        for f in files {
            let content = fs::read_to_string(&f).expect("read rs file");
            // Keep production after test-only items; ignore comments and literals.
            let prod_content = production_code(&content);
            for dep in extract_crate_deps(&prod_content) {
                if dep != mod_name {
                    assert!(
                        modules.iter().any(|&(name, _)| name == dep),
                        "Unregistered dependency: {mod_name} ({}) imports {dep}",
                        f.display()
                    );
                    assert!(
                        layer_rank(&dep) <= layer_rank(mod_name),
                        "Layer violation: {mod_name} ({}) imports higher-layer module {dep}",
                        f.display()
                    );
                    deps.insert(dep);
                }
            }
        }
        graph.insert(mod_name.to_string(), deps);
    }

    let mut visiting = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut path = Vec::new();
    for node in graph.keys() {
        if let Some(cycle) = has_cycle(node, &graph, &mut visiting, &mut visited, &mut path) {
            panic!("Module dependency cycle detected: {}", cycle.join(" -> "));
        }
    }
}
/// Sumcheck produces protocol messages and symbolic constraints; ZK systems
/// consume them. Enforce this direction for both versions and their codecs,
/// including role/feature-gated files that are inactive in the current build.
#[test]
fn test_sumcheck_protocol_dependencies() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for version in ["v1", "v2"] {
        let module = format!("runtime::sumcheck_{version}");
        let mut files = Vec::new();
        collect_rs_files(
            &root.join(format!("runtime/sumcheck-{version}/src")),
            &mut files,
        );
        files.push(root.join(format!("runtime/proto/src/sumcheck_{version}.rs")));
        for file in files {
            let source = fs::read_to_string(&file).expect("read sumcheck dependency source");
            let production = production_code(&source);
            if let Some(dependency) = sumcheck_dependency_violation(&module, &production) {
                panic!(
                    "Sumcheck dependency violation in {}: {dependency}",
                    file.display()
                );
            }
        }
    }
}

/// Dual packing is a standalone reduction with backend-neutral claims.
#[test]
fn test_dual_packing_protocol_dependencies() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime/dual-packing/src");
    let mut files = Vec::new();
    collect_rs_files(&root, &mut files);
    for file in files {
        let code = production_code(&fs::read_to_string(&file).unwrap());
        for dep in extract_crate_deps(&code) {
            assert!(
                matches!(
                    dep.as_str(),
                    "core::algebra"
                        | "core::bits"
                        | "runtime::algebra"
                        | "runtime::proto"
                        | "runtime::random"
                        | "runtime::dual_packing"
                ),
                "dual-packing dependency in {}: {dep}",
                file.display()
            );
        }
        for word in code.split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_') {
            assert!(
                !matches!(
                    word,
                    "OnceLock"
                        | "sumcheck_v1"
                        | "sumcheck_v2"
                        | "polygero"
                        | "ligero"
                        | "zk_v1"
                        | "zk_v2"
                        | "mdoc"
                        | "compile"
                ),
                "dual-packing boundary in {}: {word}",
                file.display()
            );
        }
    }
}

/// Allow only sumcheck's own code and the common algebra, circuit/proof data,
/// randomness, and utilities. Identifier checks also catch relative imports,
/// aliases and higher-level proof types hidden beneath the shared proto module.
fn sumcheck_dependency_violation(module: &str, production: &str) -> Option<String> {
    for dependency in extract_crate_deps(production) {
        if dependency != module
            && !(module == "runtime::sumcheck_v2" && dependency == "core::bits")
            && !matches!(
                dependency.as_str(),
                "core::algebra"
                    | "core::proto"
                    | "runtime::algebra"
                    | "runtime::proto"
                    | "runtime::random"
                    | "util"
            )
        {
            return Some(dependency);
        }
    }
    let other = if module == "runtime::sumcheck_v1" {
        "sumcheck_v2"
    } else {
        "sumcheck_v1"
    };
    for word in production.split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_') {
        if matches!(word, "polygero" | "ligero" | "zk" | "zk_v1" | "zk_v2")
            || word == other
            || word.starts_with("Polygero")
            || word.starts_with("Ligero")
            // ZkField is an algebra trait, independent of either proof system.
            || (word.starts_with("Zk") && word != "ZkField")
        {
            return Some(word.to_owned());
        }
    }
    None
}

#[test]
fn sumcheck_dependency_checks_cover_import_forms_and_features() {
    for module in ["runtime::sumcheck_v1", "runtime::sumcheck_v2"] {
        for source in [
            "use crate::runtime::polygero::PolygeroParam;",
            "use crate::{runtime::{zk_v1::ZkProver, algebra::RuntimeField}};",
            "use longfellow_zk::runtime::zk_v2::ZkVerifier;",
            "use super::super::polygero as commitment;",
            "use crate::runtime as rt; use rt::{zk_v2 as system};",
            "use crate::runtime::proto::{polygero as proof};",
            "use crate::runtime::proto::zk_v2::ZkProof;",
            "use crate::runtime::proto::{ZkProof as Proof};",
            "use super::super::ligero::LigeroProver;",
            "#[cfg(feature = \"prover\")] use crate::runtime::zk_v2;",
            "#[cfg(test)] mod tests {} use crate::runtime::polygero;",
        ] {
            assert!(
                sumcheck_dependency_violation(module, &production_code(source)).is_some(),
                "missed {module} dependency in {source}"
            );
        }
        let allowed = r#"
            use crate::{core::{algebra::SerializableField, proto::circuit::Circuit},
                runtime::{algebra::ZkField, random::Transcript}, util};
            // Production verification is provided by crate::runtime::zk_v2.
            const NOTE: &str = "Polygero and ZkVerifier";
            #[cfg(test)] mod tests { use crate::runtime::zk_v2; }
        "#;
        assert_eq!(
            sumcheck_dependency_violation(module, &production_code(allowed)),
            None
        );
    }
}

/// Every interpolation source is registered, including feature-gated ones.
/// Algebra backends may depend on algebra and utilities, never proof protocols.
#[test]
fn test_interpolation_dependencies() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let directory = root.join("runtime/algebra/src/range_interpolation");
    let mut actual = Vec::new();
    collect_rs_files(&directory, &mut actual);
    let registered: BTreeSet<_> = [
        "mod.rs",
        "arithmetic.rs",
        "binary.rs",
        "quadratic_extension_fft.rs",
        "scalar.rs",
        "crt.rs",
        "crt_fft.rs",
    ]
    .map(|file| directory.join(file))
    .into_iter()
    .collect();
    assert_eq!(
        actual.iter().cloned().collect::<BTreeSet<_>>(),
        registered,
        "Update the interpolation dependency registry when adding or removing sources"
    );
    actual.push(root.join("runtime/algebra/src/lch14.rs"));
    for file in actual {
        let source = fs::read_to_string(&file).expect("read interpolation source");
        assert!(
            !source.contains("feature = \"prover\"") && !source.contains("feature = \"verifier\""),
            "proof-role feature in algebra source {}",
            file.display()
        );
        let production = production_code(&source);
        for dep in extract_crate_deps(&production) {
            assert!(
                matches!(dep.as_str(), "core::algebra" | "runtime::algebra" | "util"),
                "Interpolation dependency in {}: {dep}",
                file.display()
            );
        }
    }
}

/// Shared V2 arithmetic and constraint lowering cannot acquire commitment
/// dependencies. Prover and verifier implementations remain independent.
#[test]
fn test_v2_role_and_shared_module_boundaries() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for (relative_path, forbidden) in [
        ("runtime/sumcheck-v2/src/prover.rs", "verifier"),
        ("runtime/sumcheck-v2/src/dense.rs", "verifier"),
        ("runtime/sumcheck-v2/src/eval.rs", "verifier"),
        ("runtime/sumcheck-v2/src/verifier.rs", "prover"),
        ("runtime/sumcheck-v2/src/reduction.rs", "prover"),
        ("runtime/zk-v2/src/prover.rs", "verifier"),
        ("runtime/zk-v2/src/commitment_prover.rs", "verifier"),
        ("runtime/zk-v2/src/commitment_verifier.rs", "prover"),
        ("runtime/zk-v2/src/verifier.rs", "prover"),
        ("runtime/polygero/src/prover.rs", "verifier"),
        ("runtime/polygero/src/prover_commitment.rs", "verifier"),
        ("runtime/polygero/src/verifier.rs", "prover"),
        ("runtime/sumcheck-v2/src/monomial.rs", "shared_sumcheck"),
        ("runtime/sumcheck-v2/src/quad.rs", "shared_sumcheck"),
        ("runtime/sumcheck-v2/src/split.rs", "shared_sumcheck"),
        ("runtime/sumcheck-v2/src/symbolic.rs", "shared_sumcheck"),
        ("runtime/sumcheck-v2/src/transcript.rs", "shared_sumcheck"),
    ] {
        let file = root.join(relative_path);
        let source = fs::read_to_string(&file).expect("read registered V2 source");
        let production = production_code(&source);
        let code = &production;
        let forbidden_words: &[&str] = match forbidden {
            "prover" => &[
                "prover",
                "prover_commitment",
                "PolygeroProver",
                "ZkProver",
                "prove_core",
                "eval_circuit",
            ],
            "verifier" => &[
                "verifier",
                "PolygeroVerifier",
                "ZkVerifier",
                "derive_constraints",
            ],
            "shared_sumcheck" => &[
                "prover",
                "verifier",
                "prove_core",
                "derive_constraints",
                "eval_circuit",
                "ligero",
                "polygero",
                "LigeroLinearConstraint",
                "PolygeroLinearTerm",
            ],
            _ => unreachable!(),
        };
        assert!(
            !code
                .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
                .any(|word| forbidden_words.contains(&word)),
            "V2 {forbidden} boundary in {}",
            file.display()
        );
        for dep in extract_crate_deps(&production) {
            assert!(
                !dep.starts_with("compile::")
                    && dep != "runtime::sumcheck_v1"
                    && dep != "runtime::zk_v1",
                "V2 phase or legacy dependency in {}: {dep}",
                file.display()
            );
        }
    }
    for name in [
        "config",
        "hash",
        "param",
        "polynomials",
        "constraints",
        "transcript",
    ] {
        let file = root.join(format!("runtime/polygero/src/{name}.rs"));
        let source = fs::read_to_string(&file).unwrap();
        let production = production_code(&source);
        assert!(
            !production
                .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
                .any(|word| [
                    "prover",
                    "prover_commitment",
                    "verifier",
                    "PolygeroProver",
                    "PolygeroVerifier",
                    "SubfieldV1"
                ]
                .contains(&word)),
            "role implementation dependency in shared Polygero module {}",
            file.display()
        );
    }
}

/// Arithmetic and MLDSA keep compiler and runtime dependencies
/// in separate directories, regardless of which features enable the files.
#[test]
fn test_experimental_phase_boundaries() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for (path, forbidden) in [
        ("core/algebra/src/fp24.rs", "both"),
        ("core/algebra/src/fp24_ext6.rs", "both"),
        ("runtime/algebra/src/fp24_ext6.rs", "compile"),
        (
            "runtime/algebra/src/range_interpolation/crt_fft.rs",
            "compile",
        ),
        ("runtime/algebra/src/range_interpolation", "compile"),
        ("runtime/sumcheck-v2/src", "compile"),
        ("runtime/zk-v2/src", "compile"),
        ("runtime/polygero/src/prover_commitment.rs", "compile"),
        ("runtime/polygero/src", "compile"),
        ("compile/algebra/src/fp24_ext6.rs", "runtime"),
        ("compile/compiler/src/v1", "runtime"),
        ("compile/compiler/src/v2", "runtime"),
        ("circuits/experimental/src/mldsa/params.rs", "both"),
        ("circuits/experimental/src/mldsa/shake_layout.rs", "both"),
        ("circuits/experimental/src/mldsa/runtime", "compile"),
        ("circuits/experimental/src/mldsa/compile", "runtime"),
    ] {
        let checked_path = root.join(path);
        let mut files = Vec::new();
        if checked_path.is_file() {
            files.push(checked_path);
        } else {
            collect_rs_files(&checked_path, &mut files);
        }
        assert!(!files.is_empty());
        for file in files {
            let source = fs::read_to_string(&file).unwrap();
            let production = production_code(&source);
            for phase in ["compile", "runtime"] {
                if forbidden != phase && forbidden != "both" {
                    continue;
                }
                let deps = extract_crate_deps(&production);
                assert!(
                    !deps
                        .iter()
                        .any(|dep| dep.starts_with(&format!("{phase}::")))
                        && !production.contains(&format!("super::{phase}::"))
                        && !production.contains(&format!("mldsa::{phase}::")),
                    "phase boundary violation in {}: {phase}",
                    file.display()
                );
            }
        }
    }
}
#[test]
fn test_polygero_protocol_and_phase_boundaries() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for (relative_path, forbidden) in [
        ("runtime/polygero/src", "runtime::ligero"),
        ("runtime/ligero/src", "runtime::polygero"),
        ("runtime/proto/src/polygero.rs", "runtime::proto::ligero"),
        ("runtime/proto/src/ligero.rs", "runtime::proto::polygero"),
        ("runtime/proto/src/zk_v2.rs", "runtime::proto::ligero"),
        ("runtime/zk-v2/src", "runtime::ligero"),
    ] {
        let path = root.join(relative_path);
        let mut files = Vec::new();
        if path.is_file() {
            files.push(path);
        } else {
            collect_rs_files(&path, &mut files);
        }
        assert!(!files.is_empty());
        for file in files {
            let source = fs::read_to_string(&file).unwrap();
            let production = production_code(&source);
            // The DAG extractor intentionally stops at layer::module.
            // Also inspect identifiers so grouped proto imports cannot
            // hide a dependency on the other protocol's proof types.
            let opposite = if forbidden.contains("ligero") {
                "Ligero"
            } else {
                "Polygero"
            };
            let code = &production;
            assert!(
                !code
                    .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
                    .any(|word| word.starts_with(opposite)),
                "cross-protocol type in {}",
                file.display()
            );
            for dep in extract_crate_deps(&production) {
                assert!(
                    !dep.starts_with(forbidden) && !dep.starts_with("compile::"),
                    "protocol/phase boundary in {}: {dep}",
                    file.display()
                );
            }
        }
    }
}
/// Offline tooling is a separate layer and every source is registered.
#[test]
fn test_tooling_and_system_source_boundaries() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let tests = root.join("applications/mdoc_zk/runtime/tests");
    let mut test_files = Vec::new();
    collect_rs_files(&tests, &mut test_files);
    let expected_tests: BTreeSet<_> = [
        "all/mod.rs",
        "all/v1.rs",
        "all/next.rs",
        "v2_circuits.rs",
        "v2_inputs.rs",
        "v2_attributes.rs",
        "next.rs",
        "specs.rs",
        "v1_provider.rs",
        "v2_provider.rs",
    ]
    .map(|file| tests.join(file))
    .into_iter()
    .collect();
    assert_eq!(
        test_files.into_iter().collect::<BTreeSet<_>>(),
        expected_tests
    );
    let tools = root.join("tools/zk_tool");
    let mut files = Vec::new();
    collect_rs_files(&tools, &mut files);
    let expected: BTreeSet<_> = [
        "main.rs",
        "exact.rs",
        "profiles.rs",
        "cache.rs",
        "lean.rs",
        "generate.rs",
    ]
    .map(|f| tools.join(f))
    .into_iter()
    .collect();
    assert_eq!(files.into_iter().collect::<BTreeSet<_>>(), expected);
    let parameters = root.join("tools/parameters");
    let mut parameter_files = Vec::new();
    collect_rs_files(&parameters, &mut parameter_files);
    assert!(
        parameter_files.is_empty(),
        "Rust selection belongs in compile/polygero"
    );
    for version in ["v1", "v2"] {
        let directory = root.join(format!("applications/mdoc_zk/runtime/src/{version}"));
        let mut actual = Vec::new();
        collect_rs_files(&directory, &mut actual);
        let expected_system_files: BTreeSet<_> = [
            "mod.rs",
            "zk_spec.rs",
            "provider.rs",
            "attribute.rs",
            "circuits.rs",
            "error.rs",
            "key.rs",
            "mac.rs",
            "inputs/mod.rs",
            "inputs/builder.rs",
            "inputs/public.rs",
            "inputs/private.rs",
            "proto.rs",
            "prover.rs",
            "verifier.rs",
        ]
        .map(|f| directory.join(f))
        .into_iter()
        .collect();
        assert_eq!(
            actual.into_iter().collect::<BTreeSet<_>>(),
            expected_system_files
        );
        for role in ["prover", "verifier"] {
            let source = fs::read_to_string(directory.join(format!("{role}.rs"))).unwrap();
            assert!(!source.contains("tuned_config") && !source.contains("tune_large_field"));
        }
    }
    let legacy =
        fs::read_to_string(root.join("applications/mdoc_zk/runtime/src/v1/zk_spec.rs")).unwrap();
    assert!(!legacy.contains("NEXT_VERSION"));
}

/// Native input parsing has private external tests, and application proof roles
/// must not write potentially sensitive evaluation failures to process logs.
#[test]
fn test_v2_input_security_boundaries() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for (source, tests) in [
        (
            "applications/mdoc_zk/circuits/src/cbor/parse.rs",
            "applications/mdoc_zk/circuits/tests/cbor_parse.rs",
        ),
        (
            "applications/mdoc_zk/runtime/src/v2/attribute.rs",
            "applications/mdoc_zk/runtime/tests/v2_attributes.rs",
        ),
    ] {
        let source = fs::read_to_string(root.join(source)).unwrap();
        assert!(root.join(tests).is_file());
        assert!(!source.lines().any(|line| line.trim() == "#[test]"));
        assert!(!source.contains("pub mod tests") && !source.contains("pub(crate) mod tests"));
    }
    for role in ["prover", "verifier"] {
        let source =
            fs::read_to_string(root.join(format!("applications/mdoc_zk/runtime/src/v2/{role}.rs")))
                .unwrap();
        let code = production_code(&source);
        assert!(
            !code.contains("eprintln!") && !code.contains("println!") && !code.contains("dbg!")
        );
    }
}

/// Parameter selection consumes protocol metadata; it must not construct
/// circuit, prover, verifier, or interpolation state. The application supplies
/// public workload data and its backend-capacity predicate.
#[test]
fn test_polygero_compiler_boundaries() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let directory = root.join("compile/polygero");
    let mut files = Vec::new();
    collect_rs_files(&directory, &mut files);
    let expected: BTreeSet<_> = ["src/lib.rs", "src/profiles.rs", "tests/parameters.rs"]
        .map(|file| directory.join(file))
        .into_iter()
        .collect();
    assert_eq!(files.into_iter().collect::<BTreeSet<_>>(), expected);
    for name in ["lib.rs", "profiles.rs"] {
        let file = directory.join("src").join(name);
        let source = fs::read_to_string(&file).unwrap();
        assert!(!source.lines().any(|line| line.trim() == "#[test]"));
        assert!(!source.contains("pub mod tests") && !source.contains("pub(crate) mod tests"));
        let production = production_code(&source);
        for dependency in extract_crate_deps(&production) {
            assert!(
                matches!(
                    dependency.as_str(),
                    "compile::polygero" | "core::algebra" | "runtime::proto"
                ),
                "Parameter selection dependency in {}: {dependency}",
                file.display()
            );
        }
        for word in production.split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_') {
            assert!(
                !matches!(
                    word,
                    "Circuit"
                        | "ZkContext"
                        | "PolygeroParam"
                        | "PolygeroProver"
                        | "PolygeroVerifier"
                ),
                "Runtime or circuit state in {}: {word}",
                file.display()
            );
        }
    }
    let mut compiler_files = Vec::new();
    collect_rs_files(&root.join("compile/compiler/src"), &mut compiler_files);
    for file in compiler_files {
        let source = fs::read_to_string(&file).unwrap();
        assert!(
            !extract_crate_deps(&production_code(&source)).contains("compile::polygero"),
            "Circuit compiler depends on parameter policy in {}",
            file.display()
        );
    }
}

/// The development provider is the application orchestration layer. Neither
/// runtime providers nor circuit compilers may reach back into that layer,
/// including through imports hidden behind inactive feature gates.
#[test]
fn test_development_provider_boundaries() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let directory = root.join("applications/mdoc_zk/development_provider");
    let mut files = Vec::new();
    collect_rs_files(&directory, &mut files);
    let expected = [
        "src/lib.rs",
        "src/next_v2.rs",
        "src/cache_v2.rs",
        "tests/provider.rs",
    ]
    .map(|name| directory.join(name))
    .into_iter()
    .collect::<BTreeSet<_>>();
    assert_eq!(files.into_iter().collect::<BTreeSet<_>>(), expected);

    for (directory, compiling) in [
        ("applications/mdoc_zk/runtime/src", false),
        ("applications/mdoc_zk/compile/src", true),
    ] {
        let mut files = Vec::new();
        collect_rs_files(&root.join(directory), &mut files);
        for file in files {
            let code = production_code(&fs::read_to_string(&file).unwrap());
            for dep in extract_crate_deps(&code) {
                assert!(
                    dep != "mdoc::development_provider"
                        && !dep.starts_with("tools::")
                        && (compiling || !(dep.starts_with("compile::") || dep == "mdoc::compile"))
                        && (!compiling
                            || !(dep.starts_with("runtime::") || dep == "mdoc::runtime")),
                    "application phase violation in {}: {dep}",
                    file.display()
                );
            }
            // Also catch relative and aliased imports of the compiler/provider.
            for word in code.split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_') {
                assert!(
                    word != "development_provider" && (compiling || word != "compile"),
                    "application phase violation in {}: {word}",
                    file.display()
                );
            }
        }
    }
}
/// Sumcheck v2 has separate proving and derivation paths, with private tests.
#[test]
fn test_sumcheck_v2_source_layout_and_test_privacy() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime/sumcheck-v2");
    for (subdirectory, expected_files) in [
        (
            "src",
            &[
                "lib.rs",
                "monomial.rs",
                "split.rs",
                "dense.rs",
                "boolean.rs",
                "quad.rs",
                "eval.rs",
                "prover.rs",
                "verifier.rs",
                "symbolic.rs",
                "transcript.rs",
                "reduction.rs",
            ][..],
        ),
        (
            "tests",
            &[
                "all/mod.rs",
                "all/dense.rs",
                "all/circuit.rs",
                "all/explicit.rs",
                "all/poly.rs",
                "all/sumcheck_v2.rs",
                "all/wiring.rs",
                "boolean.rs",
                "split.rs",
                "reference.rs",
            ][..],
        ),
    ] {
        let directory = root.join(subdirectory);
        let mut files = Vec::new();
        collect_rs_files(&directory, &mut files);
        let expected: BTreeSet<_> = expected_files
            .iter()
            .map(|file| directory.join(file))
            .collect();
        assert_eq!(files.iter().cloned().collect::<BTreeSet<_>>(), expected);
        for file in files {
            let source = fs::read_to_string(&file).unwrap();
            assert!(!source.contains("pub mod tests") && !source.contains("pub(crate) mod tests"));
            if subdirectory == "src" {
                assert!(
                    !source.lines().any(|line| line.trim() == "#[test]"),
                    "inline test in {}",
                    file.display()
                );
            }
        }
    }
}

/// Polygero owns only protocol code. Search policy and test bodies stay outside src.
#[test]
fn test_polygero_source_layout_and_test_privacy() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime/polygero/src");
    let mut files = Vec::new();
    collect_rs_files(&directory, &mut files);
    let expected: BTreeSet<_> = [
        "lib.rs",
        "hash.rs",
        "constraints.rs",
        "config.rs",
        "param.rs",
        "polynomials.rs",
        "prover_commitment.rs",
        "prover.rs",
        "verifier.rs",
        "transcript.rs",
    ]
    .map(|file| directory.join(file))
    .into_iter()
    .collect();
    assert_eq!(files.iter().cloned().collect::<BTreeSet<_>>(), expected);
    for file in files {
        let source = fs::read_to_string(&file).unwrap();
        assert!(
            !source.lines().any(|line| line.trim() == "#[test]"),
            "inline test in {}",
            file.display()
        );
        assert!(
            !source.contains("pub(crate) mod tests") && !source.contains("pub mod tests"),
            "exported test module in {}",
            file.display()
        );
        let production = production_code(&source);
        for word in ["TUNING_PROFILES", "MLDSA_PROFILES", "tune_large_field"] {
            assert!(
                !production.contains(word),
                "offline policy in {}",
                file.display()
            );
        }
    }
    let parameter = fs::read_to_string(directory.join("param.rs")).unwrap();
    assert!(!parameter.contains("interpolate_range") && !parameter.contains("Vec<F::E>"));
}

/// ZK v2 keeps role orchestration separate and its compiler tests outside src.
#[test]
fn test_zk_v2_source_layout_and_test_privacy() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime/zk-v2/src");
    let mut files = Vec::new();
    collect_rs_files(&directory, &mut files);
    let expected: BTreeSet<_> = [
        "lib.rs",
        "context.rs",
        "constraint_compiler.rs",
        "commitment.rs",
        "commitment_prover.rs",
        "commitment_verifier.rs",
        "transcript.rs",
        "prover.rs",
        "verifier.rs",
    ]
    .map(|file| directory.join(file))
    .into_iter()
    .collect();
    assert_eq!(files.iter().cloned().collect::<BTreeSet<_>>(), expected);
    for file in files {
        let source = fs::read_to_string(&file).unwrap();
        assert!(
            !source.lines().any(|line| line.trim() == "#[test]"),
            "inline test in {}",
            file.display()
        );
        assert!(!source.contains("pub(crate) mod tests") && !source.contains("pub mod tests"));
    }
    let context = fs::read_to_string(directory.join("context.rs")).unwrap();
    assert!(!production_code(&context).contains("prepare_inputs"));
}

/// Legacy test bodies live outside production sources; module links stay private.
#[test]
fn test_v1_test_layout_and_privacy() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for module in ["sumcheck-v1", "ligero", "zk-v1"] {
        let mut files = Vec::new();
        collect_rs_files(&root.join(format!("runtime/{module}/src")), &mut files);
        for file in files {
            let source = fs::read_to_string(&file).unwrap();
            assert!(
                !source.lines().any(|line| line.trim() == "#[test]"),
                "inline test in {}",
                file.display()
            );
            assert!(
                !source.contains("pub mod tests") && !source.contains("pub(crate) mod tests"),
                "exported test module in {}",
                file.display()
            );
        }
    }
    let directory = root.join("runtime/zk-v1/tests");
    let mut files = Vec::new();
    collect_rs_files(&directory, &mut files);
    let expected: BTreeSet<_> = ["constraint_compiler.rs", "prover.rs", "zk.rs"]
        .map(|name| directory.join(name))
        .into_iter()
        .collect();
    assert_eq!(files.into_iter().collect::<BTreeSet<_>>(), expected);
}

/// System implementations have no dependency on the opposite system, even
/// through grouped imports or files inactive in the current feature build.
#[test]
fn test_v1_v2_implementation_isolation() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for (version, opposite, commitment) in [("v1", "v2", "Polygero"), ("v2", "v1", "Ligero")] {
        let mut files = Vec::new();
        for directory in [
            format!("applications/mdoc_zk/runtime/src/{version}"),
            format!("compile/compiler/src/{version}"),
            format!("runtime/sumcheck-{version}/src"),
            format!("runtime/zk-{version}/src"),
        ] {
            collect_rs_files(&root.join(directory), &mut files);
        }
        for name in ["sumcheck", "zk"] {
            files.push(root.join(format!("runtime/proto/src/{name}_{version}.rs")));
        }
        let forbidden = [
            opposite.to_owned(),
            format!("sumcheck_{opposite}"),
            format!("zk_{opposite}"),
            format!("compile_{opposite}"),
            commitment.to_lowercase(),
        ];
        for file in files {
            let source = fs::read_to_string(&file).expect("registered system source");
            let production = production_code(&source);
            let code = &production;
            for word in code.split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_') {
                assert!(
                    !forbidden.iter().any(|name| word == name) && !word.starts_with(commitment),
                    "{version} imports the opposite system in {}: {word}",
                    file.display()
                );
            }
        }
    }
    let directory = root.join("applications/mdoc_zk/runtime/src");
    let shared: BTreeSet<_> = fs::read_dir(&directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "rs"))
        .collect();
    assert_eq!(
        shared,
        BTreeSet::from([directory.join("lib.rs"), directory.join("zk_spec.rs")])
    );
}

/// Offline certificate sources live in the formal project. Shared Hahn
/// sources contain only packing arithmetic; protocol bridges remain separate.
#[test]
fn test_hahn_certificate_sources() {
    fn collect(directory: &Path, out: &mut BTreeSet<std::path::PathBuf>) {
        for entry in fs::read_dir(directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                collect(&path, out);
            } else if path.extension().and_then(|s| s.to_str()) == Some("lean") {
                out.insert(path);
            }
        }
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let formal = root.join("../formal/parameters");
    let shared = formal.join("hahn");
    let mut expected = BTreeSet::from([
        shared.join("RuntimeHahn/Packing.lean"),
        shared.join("RuntimeHahn/Budget.lean"),
        shared.join("RuntimeHahn/HahnPolynomial.lean"),
        shared.join("RuntimeHahn/APITest.lean"),
        shared.join("RuntimeHahn/CheckedPolynomial.lean"),
        shared.join("RuntimeHahn/Coefficients.lean"),
        shared.join("RuntimeHahn/IntegralKernel.lean"),
        shared.join("RuntimeHahn/PolynomialIdentity.lean"),
    ]);
    for (name, degrees, certificate) in [
        ("Hash", 23, true),
        ("Signature", 23, true),
        ("Mldsa992", 3, true),
        ("Mldsa1024", 5, true),
        ("Mldsa960", 3, true),
        ("LigeroV7Sig", 9, true),
        ("LigeroV7SigFS", 25, true),
        ("LigeroV7Hash1", 11, true),
        ("LigeroV7Hash2", 11, true),
        ("LigeroV7Hash3", 11, true),
        ("LigeroV7Hash4", 11, true),
        ("Benchmark2109", 23, false),
        ("Benchmark2119", 21, false),
        ("Benchmark2129", 19, false),
        ("Benchmark2140", 17, false),
        ("Benchmark2152", 15, false),
    ] {
        if certificate {
            expected.insert(shared.join(format!("RuntimeHahn/{name}.lean")));
        }
        let prefix = "RuntimeHahn/Kernels";
        expected.insert(shared.join(format!("{prefix}/Kernels{name}.lean")));
        for degree in 1..=degrees {
            expected.insert(shared.join(format!("{prefix}/{name}Kernels/Degree{degree:02}.lean")));
        }
    }
    let mut actual = BTreeSet::new();
    collect(&shared, &mut actual);
    assert_eq!(actual, expected, "update the Hahn source registry");
    for file in actual {
        let source = fs::read_to_string(&file).unwrap();
        for imported in source
            .lines()
            .filter_map(|line| line.strip_prefix("import "))
        {
            assert!(
                imported.starts_with("Mathlib.")
                    || imported.starts_with("RuntimeHahn.")
                    || imported.starts_with("CodingTheory.")
                    // The audit aggregates certificate checks from both libraries.
                    || (file == shared.join("RuntimeHahn/APITest.lean")
                        && imported == "polygero.Benchmarks.HahnRateSixteenth.Certificates"),
                "protocol dependency in shared packing arithmetic {}: {imported}",
                file.display()
            );
        }
    }
    let protocol = formal.join("polygero");
    let mut protocol_files = BTreeSet::new();
    collect(&protocol, &mut protocol_files);
    assert_eq!(
        protocol_files,
        BTreeSet::from([
            protocol.join("PolygeroRustHahn.lean"),
            protocol.join("TunedProfiles.lean"),
        ])
    );
    assert!(!root.join("runtime/polygero/theory").exists());
    let bridge = fs::read_to_string(protocol.join("PolygeroRustHahn.lean")).unwrap();
    assert!(bridge
        .lines()
        .any(|line| line == "import polygero.FiatShamir.Nonrecursive"));
    let mut rust_sources = BTreeSet::new();
    for directory in [
        "src",
        "core",
        "compile",
        "runtime",
        "circuits",
        "applications",
        "tools",
        "util",
        "benches",
    ] {
        collect(&root.join(directory), &mut rust_sources);
    }
    assert!(rust_sources.is_empty(), "Lean sources belong in ../formal");
}

/// The V2 backend and codec operate entirely in the ambient field.
#[test]
fn test_v2_backend_has_no_subfield_encoding() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for relative in [
        "runtime/polygero/src/verifier.rs",
        "runtime/polygero/src/prover.rs",
        "runtime/polygero/src/prover_commitment.rs",
        "runtime/zk-v2/src/verifier.rs",
        "runtime/zk-v2/src/prover.rs",
        "runtime/proto/src/polygero.rs",
        "runtime/proto/src/zk_v2.rs",
        "compile/polygero/src/lib.rs",
        "runtime/polygero/src/param.rs",
    ] {
        let source = fs::read_to_string(root.join(relative)).unwrap();
        let production = production_code(&source);
        assert!(
            !production
                .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
                .any(|word| [
                    "SubfieldV1",
                    "subfield_boundary",
                    "subfield_rows",
                    "com_subfield_rows"
                ]
                .contains(&word)),
            "subfield classification in {relative}"
        );
    }
    let commitment =
        fs::read_to_string(root.join("runtime/polygero/src/prover_commitment.rs")).unwrap();
    assert!(!commitment.contains("Vec<bool>") && !commitment.contains("[bool]"));
}
