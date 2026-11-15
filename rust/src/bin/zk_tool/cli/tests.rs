// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
fn parse(words: &[&str]) -> Result<(String, Args)> {
    Args::from_iter(words.iter().map(|s| (*s).to_owned()))
}
#[test]
fn help_needs_no_external_tools() {
    assert_eq!(parse(&["--help"]).unwrap().0, "help");
}
#[test]
fn missing_option_value_rejects() {
    assert!(parse(&["check-profiles", "--protocol"]).is_err());
}
#[test]
fn duplicate_single_option_rejects() {
    let (_, args) = parse(&[
        "check-profiles",
        "--protocol",
        "polygero",
        "--protocol",
        "polygero",
    ])
    .unwrap();
    assert!(args.one("--protocol").is_err());
}
#[test]
fn unknown_option_rejects() {
    let (_, args) = parse(&["check-profiles", "--typo", "1"]).unwrap();
    assert!(args.validate(&["--protocol"]).is_err());
}
