// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{
    clippy::{BaselineKey, Counts},
    run::diagnostics,
    steps, Options,
};

#[test]
fn clippy_counts_are_read_per_target_and_round_trip() {
    let output = "\
warning: `longfellow-zk` (lib) generated 3 warnings
warning: `longfellow-zk` (lib test) generated 15 warnings (3 duplicates)
warning: `longfellow-zk-tools` (bin \"zk_tool\" test) generated 1 warning (run `cargo clippy --fix` \
to apply 1 suggestion)
warning: unused import: `x`
";
    let mut counts = Counts::of_output(output, "longfellow-zk", "");
    assert_eq!(counts.to_string(), "lib=3,lib-test=15");
    counts.add(Counts::of_output(output, "longfellow-zk-tools", "tools-"));
    assert_eq!(
        counts.to_string(),
        "lib=3,lib-test=15,tools-bin-zk_tool-test=1"
    );
    assert_eq!(Counts::parse(&counts.to_string()).unwrap(), counts);
    assert_eq!(Counts::of_output("", "x", "").to_string(), "none");
    assert_eq!(Counts::parse("none").unwrap(), Counts::default());
    assert!(Counts::parse("lib").is_err());
    assert!(Counts::parse("lib=x").is_err());
}

#[test]
fn only_increases_over_the_baseline_fail() {
    let baseline = Counts::parse("lib=3,lib-test=15").unwrap();
    let fewer = Counts::parse("lib=2").unwrap();
    assert!(fewer.increases(&baseline).is_empty());
    let more = Counts::parse("lib=3,lib-test=16,bin-zk_tool=1").unwrap();
    assert_eq!(
        more.increases(&baseline),
        [
            ("bin-zk_tool".to_owned(), 0, 1),
            ("lib-test".to_owned(), 15, 16)
        ]
    );
}

#[test]
fn test_totals_sum_every_result_line() {
    let output = "\
test result: ok. 679 passed; 0 failed; 2 ignored; 0 measured; 0 filtered out; finished in 92.54s
running 0 tests
test result: FAILED. 9 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s
";
    assert_eq!(steps::test_totals(output), (688, 1, 2));
}

#[test]
fn diagnostics_are_the_warning_and_error_blocks() {
    let output = "   Compiling x\nwarning: unused\n  --> a.rs:1\n\n    Finished\nerror: bad\n";
    assert_eq!(
        diagnostics(output, 10),
        ["warning: unused", "  --> a.rs:1", "error: bad"]
    );
    assert_eq!(diagnostics(output, 1), ["warning: unused"]);
    assert!(diagnostics("   Compiling x\n    Finished\n", 1).is_empty());
}

#[test]
fn options_name_existing_steps() {
    let parse = |args: &[&str]| Options::parse(args.iter().map(|a| (*a).to_owned()));
    let options = parse(&["--keep-going", "--only", "fmt,clippy", "--base", "HEAD~2"]).unwrap();
    assert!(options.keep_going);
    assert_eq!(options.only.unwrap(), ["fmt", "clippy"]);
    assert_eq!(options.base.as_deref(), Some("HEAD~2"));
    assert!(parse(&["--only", "fmt,nonesuch"]).is_err());
    assert!(parse(&["--base"]).is_err());
    assert!(parse(&["--frobnicate"]).is_err());
    let formal = steps::all().into_iter().filter(|s| s.formal).count();
    assert_eq!(formal, 5);
}

#[test]
fn a_saved_baseline_is_reused_only_in_the_same_environment() {
    let rustc = "rustc 1.91.0 (f8297e351 2025-10-28)\nhost: x86_64-unknown-linux-gnu\n";
    let clippy = "clippy 0.1.91 (f8297e351a 2025-10-28)\n";
    let runs = ["clippy --all-targets", "clippy -p tools --all-targets"];
    let flags = ["RUSTFLAGS=-C target-cpu=x86-64-v2".to_owned()];
    let measured = BaselineKey::new("94f3de58", rustc, clippy, b"lock", &runs, &flags);
    let counts = Counts::parse("lib=2,lib-test=15").unwrap();
    let saved = measured.save(&counts);
    assert_eq!(measured.saved(&saved), Some(counts.clone()));
    assert_eq!(
        BaselineKey::new("94f3de58", rustc, clippy, b"lock", &runs, &flags).saved(&saved),
        Some(counts)
    );
    let other_rustc = rustc.replace("1.91.0", "1.92.0");
    let other_clippy = clippy.replace("0.1.91", "0.1.92");
    let fewer_runs = &runs[..1];
    let elsewhere = [
        BaselineKey::new("2323f5f6", rustc, clippy, b"lock", &runs, &flags),
        BaselineKey::new("94f3de58", &other_rustc, clippy, b"lock", &runs, &flags),
        BaselineKey::new("94f3de58", rustc, &other_clippy, b"lock", &runs, &flags),
        BaselineKey::new("94f3de58", rustc, clippy, b"lock2", &runs, &flags),
        BaselineKey::new("94f3de58", rustc, clippy, b"lock", fewer_runs, &flags),
        BaselineKey::new("94f3de58", rustc, clippy, b"lock", &runs, &[]),
    ];
    for other in &elsewhere {
        assert_ne!(other, &measured);
        assert_eq!(other.saved(&saved), None, "{other:?}");
    }
    // A file saved without a key (by an older runner) is measured again.
    assert_eq!(measured.saved("lib=2,lib-test=15\n"), None);
    assert_eq!(measured.saved(""), None);
}
