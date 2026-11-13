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

fn unchecked_constructs(source: &str) -> Vec<(usize, &str)> {
    source
        .lines()
        .enumerate()
        .flat_map(|(line, text)| {
            text.split(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'')
                .filter(|word| {
                    matches!(
                        *word,
                        "sorry" | "sorryAx" | "admit" | "axiom" | "unsafe" | "skipKernelTC"
                    )
                })
                .map(move |word| (line + 1, word))
        })
        .collect()
}

const CURRENT_ENDPOINTS: &[&str] = &[
    "LfzkV2.Current.Mdoc.Soundness",
    "LfzkV2.Current.Mdoc.ZeroKnowledge",
    "LfzkV2.Current.Mdoc.VerifierPrivacy",
    "LfzkV2.Current.Mdoc.Completeness",
];

const HISTORICAL_CURRENT_IMPORTS: &[&str] = &[
    "LfzkV2.Current.WholeAnswerMerkle",
    "LfzkV2.Current.CommitmentOracle",
    "LfzkV2.Current.MerkleReplay",
    "LfzkV2.Current.GlobalCharges",
    "LfzkV2.AssertedSoundness",
    "LfzkV2.Program",
    "LfzkV2.Soundness",
    "LfzkV2.Circuit",
    "LfzkV2.Current.ChainedFS",
    "LfzkV2.Current.ChainedSupport",
    "LfzkV2.Current.RuntimeAdaptiveReduction",
    "LfzkV2.Current.SurvivalPrefix",
    "Survival.PrefixCache",
    "Survival.ChargeMonitor",
    "Survival.Saturation",
    "LfzkV2.Current.RuntimeBackend",
    "LfzkV2.Current.RuntimeCover",
    "LfzkV2.Current.RuntimeSelection",
    "LfzkV2.Current.RuntimeRoles",
    "LfzkV2.Current.RuntimeParameters",
    "LfzkV2.Current.CanonicalVerifierAgreement",
    "LfzkV2.Current.ProtocolProbability",
    "LfzkV2.Current.Soundness.ProfileBudget",
    "LfzkV2.Current.Mdoc.SetupFamily",
    "LfzkV2.Current.ZeroKnowledge.CompleteBody",
    "LfzkV2.Current.ZeroKnowledge.CompleteBackend",
    "LfzkV2.Current.ZeroKnowledge.CompleteOpening",
    "LfzkV2.Current.ZeroKnowledge.CompleteSimulationBody",
    "LfzkV2.Current.ZeroKnowledge.FrontendOpeningState",
    "LfzkV2.Current.ZeroKnowledge.OracleProgramming",
    "LfzkV2.Current.ZeroKnowledge.OracleRuntime",
    "LfzkV2.Current.ZeroKnowledge.OracleResponse",
    "LfzkV2.Current.ZeroKnowledge.HonestTranscriptMdoc",
    "LfzkV2.Current.ZeroKnowledge.HonestTranscriptLayer",
    "LfzkV2.Current.ZeroKnowledge.HonestTranscriptProgress",
    "LfzkV2.Current.ZeroKnowledge.HonestTranscriptCircuit",
    "LfzkV2.Current.ZeroKnowledge.HonestTranscriptQueries",
    "LfzkV2.Current.ZeroKnowledge.HonestTranscriptRank",
    "LfzkV2.Current.ZeroKnowledge.HonestTranscriptRoles",
    "LfzkV2.Current.ZeroKnowledge.HonestTranscriptWire",
    "LfzkV2.Current.ZeroKnowledge.StrandCanonicalPrograms",
    "TranscriptV2.SharedReduction",
];

fn violates_owner(root: &str, dependency: &str) -> bool {
    let soundness = dependency.starts_with("LfzkV2.Current.Soundness.")
        || [
            "LfzkV2.Current.Mdoc.Soundness",
            "LfzkV2.Current.Mdoc.RuntimeSoundness",
            "LfzkV2.Current.Mdoc.OracleSoundness",
        ]
        .contains(&dependency);
    let privacy = dependency.starts_with("LfzkV2.Current.ZeroKnowledge.")
        || [
            "LfzkV2.Current.Mdoc.ZeroKnowledge",
            "LfzkV2.Current.Mdoc.VerifierPrivacy",
        ]
        .contains(&dependency);
    if root.starts_with("LfzkV2.Current.Protocol.") {
        soundness || privacy || dependency.starts_with("LfzkV2.Current.Mdoc.")
    } else if root.starts_with("LfzkV2.Current.Soundness.") || root == CURRENT_ENDPOINTS[0] {
        privacy
    } else if root.starts_with("LfzkV2.Current.ZeroKnowledge.")
        || [CURRENT_ENDPOINTS[1], CURRENT_ENDPOINTS[2]].contains(&root)
    {
        soundness || dependency == "LfzkV2.Current.Protocol.Sampling"
    } else if root == CURRENT_ENDPOINTS[3] {
        soundness
            || dependency == "LfzkV2.Current.Protocol.Sampling"
            || [
                CURRENT_ENDPOINTS[1],
                CURRENT_ENDPOINTS[2],
                "LfzkV2.Current.ZeroKnowledge.StrandCanonicalHiding",
            ]
            .contains(&dependency)
    } else {
        false
    }
}

fn check_current_boundaries(dependencies: &BTreeMap<String, Vec<String>>) -> usize {
    let mut failures = 0;
    let roots: BTreeSet<&str> = CURRENT_ENDPOINTS
        .iter()
        .copied()
        .chain(dependencies.keys().map(String::as_str).filter(|name| {
            [
                "LfzkV2.Current.Protocol.",
                "LfzkV2.Current.Soundness.",
                "LfzkV2.Current.ZeroKnowledge.",
            ]
            .iter()
            .any(|prefix| name.starts_with(prefix))
        }))
        .collect();
    for root in roots {
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
            if violates_owner(root, &module)
                || HISTORICAL_CURRENT_IMPORTS
                    .iter()
                    .any(|prefix| module == *prefix || module.starts_with(&format!("{prefix}.")))
            {
                eprintln!(
                    "Proof ownership or retired-interface violation: {}",
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
    fn kernel_check_bypass_is_rejected_in_option_and_meta_commands() {
        for source in [
            "set_option debug.skipKernelTC true in\ntheorem bad : False := by exact False.elim (by assumption)",
            "set_option debug.skipKernelTC false",
            "run_cmd modifyOptions (Lean.debug.skipKernelTC.set · true)",
            "set_option «debug.skipKernelTC» true",
        ] {
            assert_eq!(unchecked_constructs(&code(source)), [(1, "skipKernelTC")]);
        }
    }

    #[test]
    fn bypass_mentions_in_comments_and_strings_are_not_commands() {
        let source = "/- debug.skipKernelTC /- nested -/ -/\n\
            -- set_option debug.skipKernelTC true\n\
            def message := \"debug.skipKernelTC\"\n\
            def skipKernelTC_description := 0\n";
        assert!(unchecked_constructs(&code(source)).is_empty());
    }

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

    #[test]
    fn proof_owners_remain_separate() {
        assert!(violates_owner(
            "LfzkV2.Current.Protocol.Setup",
            "LfzkV2.Current.Soundness.Setup"
        ));
        assert!(violates_owner(CURRENT_ENDPOINTS[0], CURRENT_ENDPOINTS[1]));
        assert!(violates_owner(CURRENT_ENDPOINTS[1], CURRENT_ENDPOINTS[0]));
        assert!(violates_owner(CURRENT_ENDPOINTS[3], CURRENT_ENDPOINTS[1]));
        assert!(!violates_owner(
            CURRENT_ENDPOINTS[0],
            "LfzkV2.Current.Protocol.Setup"
        ));
        assert!(!violates_owner(
            CURRENT_ENDPOINTS[1],
            "LfzkV2.Current.Mdoc.Runtime"
        ));
        assert!(violates_owner(
            CURRENT_ENDPOINTS[1],
            "LfzkV2.Current.Protocol.Sampling"
        ));
        assert!(violates_owner(
            CURRENT_ENDPOINTS[3],
            "LfzkV2.Current.Protocol.Sampling"
        ));
        assert!(!violates_owner(
            CURRENT_ENDPOINTS[1],
            "LfzkV2.Current.Protocol.ExecutionSampler"
        ));
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
    // Tests need direct aggregate imports: a sibling's transitive import must
    // not be their only coverage under the normal build.
    for (base, directory, barrel) in [
        (
            "formal/lfzk-v2/",
            "LfzkV2/Current/Tests/",
            "LfzkV2/Current/Tests/APITest.lean",
        ),
        (
            "formal/transcript-v2/",
            "TranscriptV2/Tests/",
            "TranscriptV2/APITest.lean",
        ),
        (
            "formal/sumcheck-v2/",
            "SumcheckV2/Tests/",
            "SumcheckV2/APITest.lean",
        ),
    ] {
        let aggregate = code(&fs::read_to_string(format!("{base}{barrel}")).unwrap());
        let imported: BTreeSet<_> = imports(&aggregate).into_iter().collect();
        for name in &paths {
            if name.starts_with(&format!("{base}{directory}"))
                && name.ends_with(".lean")
                && !name.ends_with("/APITest.lean")
            {
                let module = name
                    .strip_prefix(base)
                    .unwrap()
                    .trim_end_matches(".lean")
                    .replace('/', ".");
                if !imported.contains(&module) {
                    eprintln!("Test {module} is missing from {base}{barrel}");
                    failures += 1;
                }
            }
        }
    }
    for name in paths {
        let path = Path::new(name);
        if name.starts_with("formal/") && name.ends_with(".lean") {
            lean_count += 1;
            let source = code(&fs::read_to_string(path).unwrap());
            if name.starts_with("formal/lfzk-v2/LfzkV2/Current/")
                && !name.contains("/Tests/")
                && source
                    .lines()
                    .any(|line| line.trim_start().starts_with("export "))
            {
                eprintln!(
                    "{name}: use the declaration's owning namespace instead of export aliases"
                );
                failures += 1;
            }
            let relative = roots
                .iter()
                .find_map(|root| name.strip_prefix(root.as_str()))
                .unwrap();
            let module = relative.trim_end_matches(".lean").replace('/', ".");
            assert!(
                dependencies.insert(module, imports(&source)).is_none(),
                "duplicate Lean module"
            );
            for (line, word) in unchecked_constructs(&source) {
                eprintln!("{name}:{line}: unchecked construct {word}");
                failures += 1;
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
