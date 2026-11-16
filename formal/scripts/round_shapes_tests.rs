//! Tests of the `MdocRoundShape.lean` parser.
use super::*;

const SOURCE: &str = "namespace LfzkV2.Current.MdocRoundShape

def binaryRounds (attributes : Fin 4) : List ℕ :=
  match attributes.val with
  | 0 => [5, 6]
  | 1 => [6, 7]
  | 2 => [7, 8]
  | _ => [8, 9]

def primeRounds : List ℕ := [4, 5]

theorem counts : List.ofFn roundCount = [1, 2, 3, 4] := by decide
";

#[test]
fn parses_the_definitions() {
    let lean = parse(SOURCE).unwrap();
    assert_eq!(lean.binary, [[5, 6], [6, 7], [7, 8], [8, 9]]);
    assert_eq!(lean.prime, [4, 5]);
    assert_eq!(lean.counts, [1, 2, 3, 4]);
}

#[test]
fn blank_lines_comments_and_line_breaks_do_not_change_the_result() {
    let edited = SOURCE
        .replace(
            "def primeRounds : List ℕ := [4, 5]",
            "/-- The prime schedule.\n\nSee `binaryRounds`. -/\ndef primeRounds : List ℕ :=\n\n  [4, -- first\n\n   5]\n\n-- [99]",
        )
        .replace("  | 1 => [6, 7]", "  -- | 1 => [0]\n\n  | 1 =>\n    [6, 7]");
    let lean = parse(&edited).unwrap();
    assert_eq!(lean.binary, [[5, 6], [6, 7], [7, 8], [8, 9]]);
    assert_eq!(lean.prime, [4, 5]);
}

#[test]
fn unexpected_shapes_are_rejected() {
    for (from, to) in [
        ("def primeRounds : List ℕ := [4, 5]", ""),
        ("[4, 5]", "[4, 5] ++ [6]"),
        ("| 2 =>", "| 3 =>"),
        ("attributes.val", "attributes"),
        ("List.ofFn roundCount", "List.ofFn binaryRounds"),
    ] {
        assert!(parse(&SOURCE.replace(from, to)).is_err(), "{to}");
    }
    let twice = format!("{SOURCE}\ndef primeRounds : List ℕ := [4, 5]\n");
    assert!(parse(&twice).is_err());
}

#[test]
fn the_comparison_reports_each_mismatch() {
    let lean = parse(SOURCE).unwrap();
    let rows: Vec<_> = (1..=4)
        .map(|attributes| Shape {
            attributes,
            binary: lean.binary[attributes - 1].clone(),
            prime: lean.prime.clone(),
        })
        .collect();
    let failures = compare(&rows, &lean);
    // The fixture's counts are not the schedules' totals.
    assert_eq!(failures.len(), 4, "{failures:?}");
    let totals: Vec<usize> = rows
        .iter()
        .map(|row| {
            row.binary.iter().sum::<usize>()
                + row.prime.iter().sum::<usize>()
                + 2 * (row.binary.len() + row.prime.len())
                + OTHER_ROUNDS
        })
        .collect();
    let lean = Lean {
        counts: totals,
        ..lean
    };
    assert!(compare(&rows, &lean).is_empty());
}
