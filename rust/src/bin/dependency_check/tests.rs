// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The code-fixed layer checks.

use super::*;

fn bridge_in(parent: &str) -> bool {
    // A directory per call: tests run in parallel.
    static CALLS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let call = CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("deps-bridge-{}-{call}", std::process::id()));
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

#[test]
fn a_bridge_must_not_also_be_declared_ungated() {
    assert!(!bridge_in(
        "#[cfg(test)]\nmod evaluate;\n#[cfg(not(test))]\nmod evaluate;\n"
    ));
    assert!(!bridge_in(
        "cfg_testonly! {\n    mod evaluate;\n}\nmod evaluate;\n"
    ));
    assert!(!bridge_in("mod circuit;\n"));
}

#[test]
fn phases_never_cross() {
    use Phase::*;
    for (from, to) in [
        (Compile, Runtime),
        (Runtime, Compile),
        (Compile, Neutral),
        (Runtime, Neutral),
        (Shared, Neutral),
        (Compile, Bridge),
        (Runtime, Bridge),
        (Shared, Bridge),
        (Shared, Compile),
        (Shared, Runtime),
    ] {
        assert!(!phase_allows(from, to), "{from:?} may not use {to:?}");
    }
    for (from, to) in [
        (Compile, Compile),
        (Runtime, Runtime),
        (Compile, Shared),
        (Runtime, Shared),
        (Shared, Shared),
        (Bridge, Compile),
        (Bridge, Runtime),
        (Neutral, Compile),
        (Neutral, Runtime),
    ] {
        assert!(phase_allows(from, to), "{from:?} may use {to:?}");
    }
}

#[test]
fn circuit_halves_and_their_submodules_have_phases() {
    use Phase::*;
    for (path, expected) in [
        ("src/circuits/sha256/allocate.rs", Compile),
        ("src/mdoc/circuits/fields.rs", Compile),
        ("src/circuits/sha256/circuit/part.rs", Compile),
        ("src/circuits/sha256/concrete/fast.rs", Runtime),
        ("src/circuits/ecdsa2/evaluate/x.rs", Bridge),
        ("src/circuits/ec/points.rs", Shared),
        ("src/circuits/ecdsa2/shape.rs", Shared),
        ("src/circuits/sha256msg/shape/blocks.rs", Shared),
        ("src/circuits/sha256/constants/table.rs", Shared),
        ("src/mdoc/circuits/hash/allocate.rs", Compile),
        ("src/mdoc/circuits/hash.rs", Neutral),
        ("src/mdoc/circuits.rs", Neutral),
        ("src/runtime.rs", Neutral),
        ("src/mdoc/testcases/vectors.rs", Shared),
        ("src/mdoc/artifacts.rs", Neutral),
    ] {
        assert_eq!(phase(path), expected, "{path}");
    }
}

#[test]
fn circuit_files_of_unknown_kinds_have_no_phase() {
    for path in [
        "src/circuits/sha256/helpers.rs",
        "src/circuits/sha256/proto.rs",
        "src/circuits/ecdsa2/traits.rs",
        "src/mdoc/circuits/hash/glue/x.rs",
        "src/newtop/x.rs",
    ] {
        assert!(
            std::panic::catch_unwind(|| phase(path)).is_err(),
            "{path} should have no phase"
        );
    }
}

#[test]
fn facades_only_declare_and_reexport() {
    assert_eq!(
        facade_item(
            "// Copyright\n//! Docs.\n#![allow(x)]\nmod circuit;\npub use circuit::{A, B};\n\
             pub(crate) mod p;\n#[cfg(test)]\nmod tests;\n\
             cfg_testonly! {\n    /* note */ mod concrete;\n    pub use concrete::C;\n}\n"
        ),
        None
    );
    for (text, item) in [
        ("mod circuit;\npub fn f() {}\n", "pub fn f() {}"),
        ("impl A for B {}\n", "impl A for B {}"),
        ("pub const K: u8 = 1;\n", "pub const K: u8 = 1;"),
        ("pub struct S;\n", "pub struct S;"),
        (
            "macro_rules! m { () => {} }\n",
            "macro_rules! m { () => {} }",
        ),
        (
            "cfg_testonly! {\n    mod c;\n    impl T for U {}\n}\n",
            "impl T for U {}",
        ),
        ("pub(crate) type T = u8;\n", "pub(crate) type T = u8;"),
    ] {
        assert_eq!(facade_item(text).as_deref(), Some(item), "{text}");
    }
}

#[test]
fn contracts_reject_other_layers_of_their_version() {
    assert!(!proto_allows(
        "src/runtime/v1/proto/zk.rs",
        "src/runtime/v1/transcript.rs"
    ));
    assert!(!proto_allows(
        "src/runtime/v2/proto/zk.rs",
        "src/runtime/random/engine.rs"
    ));
    assert!(!proto_allows(
        "src/runtime/v1/proto/ligero.rs",
        "src/runtime/v1/ligero/param.rs"
    ));
    assert!(!proto_allows(
        "src/runtime/v2/proto/polygero.rs",
        "src/runtime/v2/merkle/hash.rs"
    ));
    assert!(proto_allows(
        "src/runtime/v2/proto/zk.rs",
        "src/util/array.rs"
    ));
    assert!(proto_allows(
        "src/runtime/v2/proto/zk.rs",
        "src/runtime/algebra/field.rs"
    ));
}
