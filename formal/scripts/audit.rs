//! Scan repository Lean sources for unchecked proof constructs and check local
//! Markdown links in the formal and Rust documentation. Run inside the repo.
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
    process::Command,
};

fn code(source: &str) -> String {
    let mut bytes = source.as_bytes().to_vec();
    let (mut i, mut depth, mut line, mut string) = (0, 0, false, false);
    while i < bytes.len() {
        if bytes[i] == b'\n' {
            line = false;
            i += 1;
            continue;
        }
        if line {
            bytes[i] = b' ';
            i += 1;
            continue;
        }
        if string {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                bytes[i] = b' ';
                bytes[i + 1] = b' ';
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                string = false;
            }
            bytes[i] = b' ';
            i += 1;
            continue;
        }
        if i + 1 < bytes.len() && bytes[i..i + 2] == *b"/-" {
            depth += 1;
            bytes[i] = b' ';
            bytes[i + 1] = b' ';
            i += 2;
            continue;
        }
        if depth > 0 {
            if i + 1 < bytes.len() && bytes[i..i + 2] == *b"-/" {
                depth -= 1;
                bytes[i] = b' ';
                bytes[i + 1] = b' ';
                i += 2;
                continue;
            }
            bytes[i] = b' ';
            i += 1;
            continue;
        }
        if i + 1 < bytes.len() && bytes[i..i + 2] == *b"--" {
            line = true;
            continue;
        }
        if bytes[i] == b'"' {
            string = true;
            bytes[i] = b' ';
        }
        i += 1;
    }
    String::from_utf8(bytes).unwrap()
}

fn imports(source: &str) -> Vec<String> {
    let mut result = Vec::new();
    for line in source.lines() {
        let mut words = line.split_whitespace().peekable();
        while matches!(words.peek(), Some(&"public" | &"private" | &"meta")) {
            words.next();
        }
        if words.next() != Some("import") {
            continue;
        }
        if words.peek() == Some(&"all") {
            words.next();
        }
        result.extend(words.map(str::to_owned));
    }
    result
}

const CURRENT_ENDPOINTS: &[&str] = &[
    "LfzkV2.Current.MdocSoundness",
    "LfzkV2.Current.ZeroKnowledge.MdocStrandZeroKnowledge",
    "LfzkV2.Current.ZeroKnowledge.MdocStrandVerifierPrivacy",
    "LfzkV2.Current.ZeroKnowledge.StrandHonestRuntime",
];

const HISTORICAL_CURRENT_IMPORTS: &[&str] = &[
    "LfzkV2.Current.WholeAnswerMerkle",
    "LfzkV2.AssertedSoundness",
    "LfzkV2.Program",
    "LfzkV2.Soundness",
    "LfzkV2.Circuit",
];

fn check_current_boundaries(dependencies: &BTreeMap<String, Vec<String>>) -> usize {
    let mut failures = 0;
    for &root in CURRENT_ENDPOINTS {
        if !dependencies.contains_key(root) {
            eprintln!("Missing current endpoint {root}");
            failures += 1;
            continue;
        }
        let mut pending = vec![(root.to_owned(), vec![root.to_owned()])];
        let mut seen = BTreeSet::new();
        while let Some((module, path)) = pending.pop() {
            if !seen.insert(module.clone()) {
                continue;
            }
            if HISTORICAL_CURRENT_IMPORTS
                .iter()
                .any(|prefix| module == *prefix || module.starts_with(&format!("{prefix}.")))
            {
                eprintln!(
                    "Historical model import in current endpoint: {}",
                    path.join(" -> ")
                );
                failures += 1;
                break;
            }
            if let Some(imports) = dependencies.get(&module) {
                for next in imports {
                    let mut next_path = path.clone();
                    next_path.push(next.clone());
                    pending.push((next.clone(), next_path));
                }
            }
        }
    }
    failures
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn historical_models_are_rejected_transitively() {
        let mut graph: BTreeMap<_, _> = CURRENT_ENDPOINTS
            .iter()
            .map(|name| ((*name).to_owned(), Vec::new()))
            .collect();
        assert_eq!(check_current_boundaries(&graph), 0);
        graph.insert(CURRENT_ENDPOINTS[1].to_owned(), vec!["Helper".to_owned()]);
        for prefix in HISTORICAL_CURRENT_IMPORTS {
            for module in [(*prefix).to_owned(), format!("{prefix}.Future")] {
                graph.insert("Helper".to_owned(), vec![module]);
                assert_eq!(check_current_boundaries(&graph), 1);
            }
        }
    }

    #[test]
    fn only_actual_import_commands_are_followed() {
        let source = "/- import Fake -/\npublic import all Wanted\n-- import Fake\nprivate meta import AlsoWanted\n";
        assert_eq!(imports(&code(source)), ["Wanted", "AlsoWanted"]);
    }
}

fn main() {
    let root = Command::new("git")
        .args(["rev-parse", "--show-toplevel"])
        .output()
        .unwrap();
    assert!(root.status.success());
    std::env::set_current_dir(std::str::from_utf8(&root.stdout).unwrap().trim()).unwrap();
    let output = Command::new("git")
        .args([
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
        ])
        .output()
        .unwrap();
    assert!(output.status.success());
    let paths: BTreeSet<_> = std::str::from_utf8(&output.stdout)
        .unwrap()
        .split('\0')
        .filter(|p| !p.is_empty() && Path::new(p).is_file())
        .collect();
    let (mut lean_count, mut link_count, mut failures) = (0, 0, 0);
    let mut roots = vec!["formal/".to_owned()];
    for line in fs::read_to_string("formal/lakefile.toml").unwrap().lines() {
        if let Some(directory) = line.trim().strip_prefix("srcDir = ") {
            let directory = directory.trim_matches('"');
            if directory != "." {
                roots.push(format!("formal/{directory}/"));
            }
        }
    }
    roots.sort_by_key(|root| std::cmp::Reverse(root.len()));
    roots.dedup();
    let mut dependencies = BTreeMap::new();
    // Every current test must be a direct aggregate import. A transitive
    // dependency on a sibling test must not be its only build coverage.
    let test_barrel =
        code(&fs::read_to_string("formal/lfzk-v2/LfzkV2/Current/Tests/APITest.lean").unwrap());
    let test_imports: BTreeSet<_> = test_barrel
        .lines()
        .filter_map(|line| line.trim().strip_prefix("import "))
        .collect();
    for name in &paths {
        if name.starts_with("formal/lfzk-v2/LfzkV2/Current/Tests/")
            && name.ends_with(".lean")
            && !name.ends_with("/APITest.lean")
        {
            let module = name
                .strip_prefix("formal/lfzk-v2/")
                .unwrap()
                .trim_end_matches(".lean")
                .replace('/', ".");
            if !test_imports.contains(module.as_str()) {
                eprintln!("Current test {module} is missing from Tests.APITest");
                failures += 1;
            }
        }
    }
    for name in paths {
        let path = Path::new(name);
        if name.starts_with("formal/") && name.ends_with(".lean") {
            lean_count += 1;
            let source = code(&fs::read_to_string(path).unwrap());
            let relative = roots
                .iter()
                .find_map(|root| name.strip_prefix(root.as_str()))
                .unwrap();
            let module = relative.trim_end_matches(".lean").replace('/', ".");
            assert!(
                dependencies.insert(module, imports(&source)).is_none(),
                "duplicate Lean module"
            );
            for (line, text) in source.lines().enumerate() {
                for word in text.split(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'') {
                    if ["sorry", "sorryAx", "admit", "axiom", "unsafe"].contains(&word) {
                        eprintln!("{name}:{}: unchecked construct {word}", line + 1);
                        failures += 1;
                    }
                }
            }
        }
        if name.ends_with(".md")
            && (name.starts_with("formal/") || name.starts_with("rust/") || name == "README.md")
        {
            let source = fs::read_to_string(path).unwrap();
            for (line, text) in source.lines().enumerate() {
                for suffix in text.split("](").skip(1) {
                    let Some((target, _)) = suffix.split_once(')') else {
                        continue;
                    };
                    let target = target.trim().trim_matches(['<', '>']);
                    if target.starts_with('#')
                        || target.contains("://")
                        || target.starts_with("mailto:")
                    {
                        continue;
                    }
                    let file = target.split('#').next().unwrap();
                    if file.is_empty() {
                        continue;
                    }
                    link_count += 1;
                    if !path.parent().unwrap().join(file).exists() {
                        eprintln!("{name}:{}: missing link target {target}", line + 1);
                        failures += 1;
                    }
                }
            }
        }
    }
    failures += check_current_boundaries(&dependencies);
    println!("Scanned {lean_count} Lean sources and {link_count} local documentation links.");
    assert!(lean_count > 0, "no Lean sources found");
    assert_eq!(failures, 0, "source/documentation audit failed");
}
