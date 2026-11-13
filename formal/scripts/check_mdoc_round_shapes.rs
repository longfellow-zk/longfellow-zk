//! Check the closed Lean mdoc round metadata against the current compiler.
//!
//! Builds the Rust library, compiles and runs `mdoc_round_shapes.rs` to extract
//! each supported shape's per-layer schedules, then compares them with
//! `MdocRoundShape.binaryRounds`, `primeRounds` and `counts`. Run inside the repo.
use std::{
    fs,
    path::Path,
    process::{Child, Command, Stdio},
    thread,
    time::{Duration, Instant},
};

/// Ordinary boundaries outside both frontends: witness selection, the split's
/// `eta`, the adapter's conversion, packing, joint Polygero batching and the
/// shared opening. The final seal is counted separately.
const OTHER_ROUNDS: usize = 6;

/// Wait for `child`, killing it after `seconds`.
fn finish(mut child: Child, what: &str, seconds: u64) {
    let deadline = Instant::now() + Duration::from_secs(seconds);
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            assert!(status.success(), "{what} failed: {status}");
            return;
        }
        if Instant::now() > deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("{what} exceeded {seconds} seconds");
        }
        thread::sleep(Duration::from_millis(100));
    }
}

/// The text after `"key":` in one extractor line.
fn field<'a>(line: &'a str, key: &str) -> &'a str {
    let pattern = format!("\"{key}\":");
    let start = line
        .find(&pattern)
        .unwrap_or_else(|| panic!("missing {key}: {line}"));
    &line[start + pattern.len()..]
}

/// The comma-separated naturals in the first `[...]` of `text`.
fn list(text: &str) -> Vec<usize> {
    let start = text.find('[').expect("missing list") + 1;
    let end = start + text[start..].find(']').expect("unterminated list");
    text[start..end]
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(|s| s.parse().unwrap_or_else(|_| panic!("bad entry {s:?}")))
        .collect()
}

struct Shape {
    attributes: usize,
    binary: Vec<usize>,
    prime: Vec<usize>,
}

fn shape(line: &str) -> Shape {
    let attributes = field(line, "attributes");
    let digits = attributes
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(attributes.len());
    Shape {
        attributes: attributes[..digits].parse().unwrap(),
        binary: list(field(line, "binary_rounds")),
        prime: list(field(line, "prime_rounds")),
    }
}

/// The text of `source` from `start` up to the next `end`.
fn between<'a>(source: &'a str, start: &str, end: &str) -> &'a str {
    let rest = &source[source
        .find(start)
        .unwrap_or_else(|| panic!("missing {start}"))..];
    &rest[..rest.find(end).unwrap_or(rest.len())]
}

/// The text after the first `marker` in `text`.
fn field_after<'a>(text: &'a str, marker: &str) -> &'a str {
    &text[text
        .find(marker)
        .unwrap_or_else(|| panic!("missing {marker}"))
        + marker.len()..]
}

fn main() {
    let root = Command::new("git")
        .args(["rev-parse", "--show-toplevel"])
        .output()
        .unwrap();
    assert!(root.status.success());
    let root = Path::new(std::str::from_utf8(&root.stdout).unwrap().trim()).to_owned();
    let (formal, rust) = (root.join("formal"), root.join("rust"));
    let work = formal.join(".lake/mdoc-round-shapes-check");
    fs::create_dir_all(&work).unwrap();

    // Compile current sources: never select an unchecked stale circuit library.
    let cargo = Command::new("cargo")
        .args(["build", "--release", "--lib", "--jobs", "2"])
        .current_dir(&rust)
        .spawn()
        .unwrap();
    finish(cargo, "cargo build", 600);
    let program = work.join("extract");
    let rustc = Command::new("rustc")
        .args([
            "--edition=2021",
            "-C",
            "panic=abort",
            "-C",
            "target-cpu=native",
        ])
        .arg(formal.join("scripts/mdoc_round_shapes.rs"))
        .arg("-L")
        .arg(format!(
            "dependency={}",
            rust.join("target/release/deps").display()
        ))
        .arg("--extern")
        .arg(format!(
            "longfellow_zk={}",
            rust.join("target/release/liblongfellow_zk.rlib").display()
        ))
        .arg("-o")
        .arg(&program)
        .current_dir(&rust)
        .spawn()
        .unwrap();
    finish(rustc, "rustc", 180);
    let shapes = work.join("compiler-shapes.jsonl");
    let extract = Command::new(&program)
        .stdout(Stdio::from(fs::File::create(&shapes).unwrap()))
        .spawn()
        .unwrap();
    finish(extract, "round-shape extraction", 180);
    let rows: Vec<_> = fs::read_to_string(&shapes)
        .unwrap()
        .lines()
        .map(shape)
        .collect();

    let lean = formal.join("lfzk-v2/LfzkV2/Current/MdocRoundShape.lean");
    let source = fs::read_to_string(&lean).unwrap();
    let binary: Vec<_> = between(&source, "def binaryRounds", "def primeRounds")
        .split("=>")
        .skip(1)
        .map(list)
        .collect();
    let prime = list(between(&source, "def primeRounds", "\n\n"));
    let counts = list(field_after(between(&source, "theorem counts", "\n"), "="));

    assert!(
        rows.len() == 4 && binary.len() == 4 && counts.len() == 4,
        "expected four shapes: compiler {}, binaryRounds {}, counts {}",
        rows.len(),
        binary.len(),
        counts.len()
    );
    let mut failures = 0;
    let mut fail = |message: String| {
        eprintln!("{message}");
        failures += 1;
    };
    for (index, row) in rows.iter().enumerate() {
        let attributes = index + 1;
        let mut matches = row.attributes == attributes;
        if !matches {
            fail(format!(
                "row {index} has {} attributes, expected {attributes}",
                row.attributes
            ));
        }
        if row.binary != binary[index] {
            matches = false;
            fail(format!(
                "{attributes} attributes: compiler binary schedule {:?}, Lean binaryRounds {:?}",
                row.binary, binary[index]
            ));
        }
        if row.prime != prime {
            matches = false;
            fail(format!(
                "{attributes} attributes: compiler prime schedule {:?}, Lean primeRounds {prime:?}",
                row.prime
            ));
        }
        let rounds = row.binary.iter().sum::<usize>()
            + row.prime.iter().sum::<usize>()
            + 3 * (row.binary.len() + row.prime.len())
            + OTHER_ROUNDS;
        if rounds != counts[index] {
            matches = false;
            fail(format!(
                "{attributes} attributes: compiler schedule gives {rounds} rounds, Lean counts states {}",
                counts[index]
            ));
        }
        if matches {
            println!("{attributes} attributes: {rounds} rounds; compiler metadata matches Lean");
        }
    }
    assert_eq!(failures, 0, "mdoc round-shape check failed");
}
