//! Check the closed Lean mdoc round metadata against the current compiler.
//!
//! Extracts each supported shape's per-layer schedules from the compiler
//! (`mdoc_round_shapes.rs`), then compares them with the definitions of
//! `MdocRoundShape.binaryRounds`, `primeRounds` and `counts`. Build with the
//! adjacent Cargo manifest, which links the crate in `rust/` by path, and run
//! inside the repository.
mod mdoc_round_shapes;

use std::{fs, path::Path, process::Command};

use mdoc_round_shapes::{shapes, Shape};

/// Boundaries outside the frontends' layers: witness selection, the two
/// frontends' top weights, the adapter's conversion, packing, joint Polygero
/// batching and the shared opening. Each later stage's weights and the split's
/// `eta` extend a combine answer and open no boundary. The final seal is
/// counted separately.
const OTHER_ROUNDS: usize = 7;

/// Lean source with comments and string literals blanked, keeping lines.
fn code(source: &str) -> String {
    let chars: Vec<char> = source.chars().collect();
    let mut out = String::with_capacity(source.len());
    let (mut i, mut depth) = (0, 0usize);
    let blank = |c: char| if c == '\n' { '\n' } else { ' ' };
    while i < chars.len() {
        let pair = |a: char, b: char| chars[i] == a && chars.get(i + 1) == Some(&b);
        if pair('/', '-') {
            depth += 1;
            out.push_str("  ");
            i += 2;
        } else if depth > 0 {
            if pair('-', '/') {
                depth -= 1;
                out.push_str("  ");
                i += 2;
            } else {
                out.push(blank(chars[i]));
                i += 1;
            }
        } else if pair('-', '-') {
            while i < chars.len() && chars[i] != '\n' {
                out.push(' ');
                i += 1;
            }
        } else if chars[i] == '"' {
            out.push(' ');
            i += 1;
            while i < chars.len() && chars[i] != '"' {
                if chars[i] == '\\' && i + 1 < chars.len() {
                    out.push(blank(chars[i]));
                    i += 1;
                }
                out.push(blank(chars[i]));
                i += 1;
            }
            if i < chars.len() {
                out.push(' ');
                i += 1;
            }
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    out
}

/// The top-level commands of blanked Lean source: each starts on a line
/// that begins in the first column and runs until the next such line.
fn commands(code: &str) -> Vec<String> {
    let mut commands: Vec<String> = Vec::new();
    for line in code.lines() {
        if line.starts_with(|c: char| !c.is_whitespace()) {
            commands.push(String::new());
        }
        if let Some(command) = commands.last_mut() {
            command.push_str(line);
            command.push('\n');
        }
    }
    commands
}

/// The text after `keyword name` of the one command that declares `name`
/// with `keyword`; modifiers and attributes may precede the keyword.
fn declaration<'a>(commands: &'a [String], keyword: &str, name: &str) -> Result<&'a str, String> {
    let declared = |command: &'a String| -> Option<&'a str> {
        let mut rest = command.as_str();
        loop {
            let token = rest.trim_start();
            let end = token.find(char::is_whitespace)?;
            if &token[..end] == keyword {
                let declared = token[end..].trim_start();
                let end = declared
                    .find(|c: char| c.is_whitespace() || "(:{[".contains(c))
                    .unwrap_or(declared.len());
                return (&declared[..end] == name).then_some(&declared[end..]);
            }
            rest = &token[end..];
        }
    };
    let found: Vec<&str> = commands.iter().filter_map(declared).collect();
    match found[..] {
        [text] => Ok(text),
        [] => Err(format!("no `{keyword} {name}`")),
        _ => Err(format!("{} declarations `{keyword} {name}`", found.len())),
    }
}

/// The value of a declaration: the text after its first `:=`.
fn value(text: &str) -> Result<&str, String> {
    text.split_once(":=")
        .map(|(_, value)| value)
        .ok_or_else(|| "missing :=".into())
}

/// A list literal of naturals, `[a, b, ...]`, and nothing else.
fn list(text: &str) -> Result<Vec<usize>, String> {
    let inner = text
        .trim()
        .strip_prefix('[')
        .and_then(|rest| rest.strip_suffix(']'))
        .ok_or_else(|| format!("not a list literal: {:?}", text.trim()))?;
    if inner.trim().is_empty() {
        return Ok(Vec::new());
    }
    inner
        .split(',')
        .map(|entry| {
            entry
                .trim()
                .parse()
                .map_err(|_| format!("bad list entry {:?}", entry.trim()))
        })
        .collect()
}

/// `binaryRounds`: `match attributes.val with` and one arm per shape, the
/// arms `| 0`, `| 1`, ... in order and a final `| _`.
fn binary_rounds(commands: &[String]) -> Result<Vec<Vec<usize>>, String> {
    let body = value(declaration(commands, "def", "binaryRounds")?)?;
    let (head, arms) = body
        .split_once("with")
        .ok_or("binaryRounds is not a match")?;
    if head.split_whitespace().collect::<Vec<_>>() != ["match", "attributes.val"] {
        return Err(format!("binaryRounds matches on {:?}", head.trim()));
    }
    let arms: Vec<&str> = arms.split('|').collect();
    if !arms[0].trim().is_empty() {
        return Err(format!("text before the first arm: {:?}", arms[0].trim()));
    }
    let arms = &arms[1..];
    arms.iter()
        .enumerate()
        .map(|(index, arm)| {
            let (pattern, rounds) = arm
                .split_once("=>")
                .ok_or_else(|| format!("arm without =>: {:?}", arm.trim()))?;
            let expected = if index + 1 == arms.len() {
                "_".to_owned()
            } else {
                index.to_string()
            };
            if pattern.trim() != expected {
                return Err(format!(
                    "arm {index} matches {:?}, expected {expected}",
                    pattern.trim()
                ));
            }
            list(rounds)
        })
        .collect()
}

/// `counts : List.ofFn roundCount = [...]`.
fn counts(commands: &[String]) -> Result<Vec<usize>, String> {
    let statement = declaration(commands, "theorem", "counts")?
        .split_once(":=")
        .ok_or("counts has no proof")?
        .0;
    let (left, right) = statement
        .trim()
        .strip_prefix(':')
        .and_then(|statement| statement.split_once('='))
        .ok_or_else(|| format!("counts states {:?}", statement.trim()))?;
    if left.split_whitespace().collect::<Vec<_>>() != ["List.ofFn", "roundCount"] {
        return Err(format!("counts states {:?}", statement.trim()));
    }
    list(right)
}

/// The schedules and totals `MdocRoundShape.lean` states.
struct Lean {
    binary: Vec<Vec<usize>>,
    prime: Vec<usize>,
    counts: Vec<usize>,
}

fn parse(source: &str) -> Result<Lean, String> {
    let commands = commands(&code(source));
    Ok(Lean {
        binary: binary_rounds(&commands)?,
        prime: list(value(declaration(&commands, "def", "primeRounds")?)?)?,
        counts: counts(&commands)?,
    })
}

/// Compare the compiler's shapes with Lean's; returns the mismatches.
fn compare(rows: &[Shape], lean: &Lean) -> Vec<String> {
    let mut failures = Vec::new();
    if rows.len() != 4 || lean.binary.len() != 4 || lean.counts.len() != 4 {
        failures.push(format!(
            "expected four shapes: compiler {}, binaryRounds {}, counts {}",
            rows.len(),
            lean.binary.len(),
            lean.counts.len()
        ));
        return failures;
    }
    for (index, row) in rows.iter().enumerate() {
        let attributes = index + 1;
        if row.attributes != attributes {
            failures.push(format!(
                "row {index} has {} attributes, expected {attributes}",
                row.attributes
            ));
        }
        if row.binary != lean.binary[index] {
            failures.push(format!(
                "{attributes} attributes: compiler binary schedule {:?}, Lean binaryRounds {:?}",
                row.binary, lean.binary[index]
            ));
        }
        if row.prime != lean.prime {
            failures.push(format!(
                "{attributes} attributes: compiler prime schedule {:?}, Lean primeRounds {:?}",
                row.prime, lean.prime
            ));
        }
        let rounds = row.binary.iter().sum::<usize>()
            + row.prime.iter().sum::<usize>()
            + 2 * (row.binary.len() + row.prime.len())
            + OTHER_ROUNDS;
        if rounds != lean.counts[index] {
            failures.push(format!(
                "{attributes} attributes: compiler schedule gives {rounds} rounds, Lean counts states {}",
                lean.counts[index]
            ));
        }
    }
    failures
}

fn main() {
    let root = Command::new("git")
        .args(["rev-parse", "--show-toplevel"])
        .output()
        .unwrap();
    assert!(root.status.success(), "run inside the repository");
    let root = Path::new(std::str::from_utf8(&root.stdout).unwrap().trim()).to_owned();
    let path = root.join("formal/lfzk-v2/LfzkV2/Current/MdocRoundShape.lean");
    let lean = parse(&fs::read_to_string(&path).unwrap())
        .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
    let rows = shapes();
    let failures = compare(&rows, &lean);
    for failure in &failures {
        eprintln!("{failure}");
    }
    assert!(failures.is_empty(), "mdoc round-shape check failed");
    for (row, rounds) in rows.iter().zip(&lean.counts) {
        println!(
            "{} attributes: {rounds} rounds; compiler metadata matches Lean",
            row.attributes
        );
    }
}

#[cfg(test)]
mod round_shapes_tests;
