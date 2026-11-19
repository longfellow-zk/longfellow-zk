//! Tests of the `MdocRoundShape.lean` parser.
use super::*;

const SOURCE: &str = "namespace LfzkV2.Current.MdocRoundShape

def binaryRounds : List ℕ := [5, 6]

def primeRounds : List ℕ := [4, 5]

theorem roundCount_eq : roundCount = 35 := by decide
";

#[test]
fn parses_the_definitions() {
    let lean = parse(SOURCE).unwrap();
    assert_eq!(lean.shape.binary, [5, 6]);
    assert_eq!(lean.shape.prime, [4, 5]);
    assert_eq!(lean.rounds, 35);
}

#[test]
fn blank_lines_comments_and_line_breaks_do_not_change_the_result() {
    let edited = SOURCE
        .replace(
            "def primeRounds : List ℕ := [4, 5]",
            "/-- The prime schedule.\n\nSee `binaryRounds`. -/\ndef primeRounds : List ℕ :=\n\n  [4, -- first\n\n   5]\n\n-- [99]",
        )
        .replace("= 35 := by decide", "=\n  35 := by decide");
    let lean = parse(&edited).unwrap();
    assert_eq!(lean.shape.binary, [5, 6]);
    assert_eq!(lean.shape.prime, [4, 5]);
    assert_eq!(lean.rounds, 35);
}

#[test]
fn unexpected_shapes_are_rejected() {
    for (from, to) in [
        ("def primeRounds : List ℕ := [4, 5]", ""),
        ("[4, 5]", "[4, 5] ++ [6]"),
        ("[5, 6]", "List.replicate 2 5"),
        ("roundCount = 35", "2 + roundCount = 37"),
        ("= 35 :=", "= 30 + 5 :="),
    ] {
        assert!(parse(&SOURCE.replace(from, to)).is_err(), "{to}");
    }
    let twice = format!("{SOURCE}\ndef primeRounds : List ℕ := [4, 5]\n");
    assert!(parse(&twice).is_err());
}

#[test]
fn the_comparison_reports_each_mismatch() {
    let lean = parse(SOURCE).unwrap();
    assert!(compare(&lean.shape, &lean).is_empty());
    let actual = Shape {
        binary: vec![12, 13],
        prime: vec![14],
    };
    let failures = compare(&actual, &lean);
    assert_eq!(failures.len(), 3, "{failures:?}");
    assert!(failures[0].contains("compiler binary schedule"));
    assert!(failures[1].contains("compiler prime schedule"));
    assert!(failures[2].contains("compiler schedule gives"));
}
