//! Check the closed Lean mdoc round metadata against the current compiler.
//!
//! Extracts the NEXT circuit's per-layer schedules from the compiler
//! (`mdoc_round_shapes.rs`), then compares them against
//! `MdocRoundShape.binaryRounds`, `primeRounds` and `roundCount_eq`. Build with the
//! adjacent Cargo manifest, which links the crate in `rust/` by path, and run
//! inside the repository.
mod mdoc_round_shapes;

use std::{fs, path::Path, process::Command};

use mdoc_round_shapes::{Shape, shape};

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

/// The literal total from `roundCount_eq : roundCount = ...`.
fn round_count(commands: &[String]) -> Result<usize, String> {
    let statement = declaration(commands, "theorem", "roundCount_eq")?
        .split_once(":=")
        .ok_or("roundCount_eq has no proof")?
        .0;
    let (left, right) = statement
        .trim()
        .strip_prefix(':')
        .and_then(|statement| statement.split_once('='))
        .ok_or_else(|| format!("roundCount_eq states {:?}", statement.trim()))?;
    if left.trim() != "roundCount" {
        return Err(format!("roundCount_eq states {:?}", statement.trim()));
    }
    right
        .trim()
        .parse()
        .map_err(|_| format!("roundCount_eq has no literal total: {:?}", right.trim()))
}

/// The schedules and total `MdocRoundShape.lean` states.
struct Lean {
    shape: Shape,
    rounds: usize,
}

fn parse(source: &str) -> Result<Lean, String> {
    let commands = commands(&code(source));
    Ok(Lean {
        shape: Shape {
            binary: list(value(declaration(&commands, "def", "binaryRounds")?)?)?,
            prime: list(value(declaration(&commands, "def", "primeRounds")?)?)?,
        },
        rounds: round_count(&commands)?,
    })
}

/// Compare the compiler's shape with Lean's, returning the mismatches.
fn compare(shape: &Shape, lean: &Lean) -> Vec<String> {
    let mut failures = Vec::new();
    if shape.binary != lean.shape.binary {
        failures.push(format!(
            "compiler binary schedule {:?}, Lean binaryRounds {:?}",
            shape.binary, lean.shape.binary
        ));
    }
    if shape.prime != lean.shape.prime {
        failures.push(format!(
            "compiler prime schedule {:?}, Lean primeRounds {:?}",
            shape.prime, lean.shape.prime
        ));
    }
    let rounds = shape.binary.iter().sum::<usize>()
        + shape.prime.iter().sum::<usize>()
        + 2 * (shape.binary.len() + shape.prime.len())
        + OTHER_ROUNDS;
    if rounds != lean.rounds {
        failures.push(format!(
            "compiler schedule gives {rounds} rounds, Lean roundCount_eq states {}",
            lean.rounds
        ));
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
    let failures = compare(&shape(), &lean);
    for failure in &failures {
        eprintln!("{failure}");
    }
    assert!(failures.is_empty(), "mdoc round-shape check failed");
    println!(
        "NEXT mdoc: {} rounds, compiler metadata matches Lean",
        lean.rounds
    );
}

#[cfg(test)]
mod round_shapes_tests;
