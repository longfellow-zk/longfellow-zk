// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The code-fixed layer checks.

use super::*;

fn bridge_in(parent: &str) -> bool {
    let dir = std::env::temp_dir().join(format!("deps-bridge-{}", std::process::id()));
    std::fs::create_dir_all(dir.join("src/c")).unwrap();
    std::fs::write(dir.join("src/c.rs"), parent).unwrap();
    let gated = bridge_is_test_only(&dir, "src/c/evaluate.rs");
    std::fs::remove_dir_all(&dir).unwrap();
    gated
}

#[test]
fn bridges_must_be_declared_only_for_tests() {
    assert!(bridge_in(
        "mod circuit;\ncfg_testonly! {\n    mod evaluate;\n}\n"
    ));
    assert!(bridge_in("#[cfg(test)]\nmod evaluate;\n"));
    assert!(bridge_in(
        "cfg_testonly! {\n    mod concrete;\n    mod evaluate;\n    pub use evaluate::f;\n}\n"
    ));
    assert!(!bridge_in("mod evaluate;\n"));
    assert!(!bridge_in(
        "cfg_testonly! {\n    mod concrete;\n}\nmod evaluate;\n"
    ));
    assert!(!bridge_in("#[cfg(test)]\nmod tests;\nmod evaluate;\n"));
}

#[test]
fn phases_follow_the_layout() {
    use Phase::*;
    for (path, expected) in [
        ("src/compile/compiler/v2/top.rs", Compile),
        ("src/mdoc/compile/circuits.rs", Compile),
        ("src/circuits/sha256/circuit.rs", Compile),
        ("src/runtime/v2/zk/prover.rs", Runtime),
        ("src/mdoc/runtime/v2/link.rs", Runtime),
        ("src/circuits/sha256/concrete.rs", Runtime),
        ("src/mdoc/circuits/cbor/mdoc.rs", Runtime),
        ("src/core/algebra/encoding.rs", Shared),
        ("src/mdoc/proto/adapter.rs", Shared),
        ("src/circuits/sha256/constants.rs", Shared),
        ("src/util/array.rs", Shared),
        ("src/circuits/sha256/evaluate.rs", Bridge),
        ("src/circuits/sha256.rs", Neutral),
        ("src/bin/zk_tool/main.rs", Neutral),
        ("src/mdoc/development_provider/next_v2.rs", Neutral),
    ] {
        assert_eq!(phase(path), expected, "{path}");
    }
    assert!(!phase_allows(Compile, Runtime));
    assert!(!phase_allows(Runtime, Compile));
    assert!(!phase_allows(Shared, Runtime));
    assert!(!phase_allows(Shared, Compile));
    assert!(!phase_allows(Compile, Bridge));
    assert!(phase_allows(Bridge, Runtime) && phase_allows(Runtime, Shared));
}

#[test]
fn contracts_use_only_lower_layers() {
    assert!(proto_allows(
        "src/runtime/v2/proto/zk.rs",
        "src/runtime/v2/transcript/session.rs"
    ));
    assert!(proto_allows(
        "src/runtime/v1/proto/zk.rs",
        "src/runtime/v1/subfield.rs"
    ));
    assert!(proto_allows(
        "src/runtime/v2/proto/zk.rs",
        "src/core/algebra/field.rs"
    ));
    assert!(!proto_allows(
        "src/runtime/v2/proto/zk.rs",
        "src/runtime/v2/polygero/error.rs"
    ));
    assert!(!proto_allows(
        "src/runtime/v1/proto/zk.rs",
        "src/runtime/v2/transcript.rs"
    ));
    assert!(proto_allows(
        "src/runtime/v2/zk/prover.rs",
        "src/runtime/v2/polygero/error.rs"
    ));
}
