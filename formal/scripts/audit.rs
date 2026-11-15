//! Scan repository Lean sources for unchecked proof constructs and check local
//! Markdown links in the formal and Rust documentation. Run inside the repo.
//! It also pins the offline Hahn certificate sources under `parameters/`, and
//! checks that the Lean names and Rust test names the Rust designs cite exist.
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
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

/// Modules whose numerical facts keep the documented native-evaluation
/// allowance; `scripts/Audit.lean` accepts native axioms from exactly these.
/// No other module may use native evaluation. `scripts.Audit` names
/// `ofReduceBool` only to reject it.
const NATIVE_EVALUATION_ROOTS: &[&str] = &["LfzkV1", "examples.Ligero.Longfellow"];

fn native_evaluation_allowed(module: &str) -> bool {
    module == "scripts.Audit"
        || NATIVE_EVALUATION_ROOTS
            .iter()
            .any(|root| module == *root || module.starts_with(&format!("{root}.")))
}

/// Native-evaluation routes: `native_decide`, `decide +native` or
/// `native := true`, and any mention of `ofReduceBool`/`reduceBool`.
fn native_evaluation(source: &str) -> Vec<(usize, &'static str)> {
    let mut found = Vec::new();
    for (line, text) in source.lines().enumerate() {
        let words: Vec<_> = text
            .split(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'' && c != '.')
            .collect();
        if words.iter().any(|w| w.split('.').any(|part| part == "native_decide")) {
            found.push((line + 1, "native_decide"));
        }
        if words.iter().any(|w| {
            w.split('.')
                .any(|part| part == "ofReduceBool" || part == "reduceBool")
        }) {
            found.push((line + 1, "ofReduceBool"));
        }
        let compact: String = text.chars().filter(|c| !c.is_whitespace()).collect();
        if compact.contains("+native") || compact.contains("native:=true") {
            found.push((line + 1, "native decide option"));
        }
    }
    found
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
    fn native_evaluation_is_found_and_allowed_only_for_the_legacy_rows() {
        for source in [
            "theorem t : 2 + 2 = 4 := by native_decide",
            "example : True := by decide +native",
            "example : True := by decide (config := { native := true })",
            "#check Lean.ofReduceBool",
        ] {
            assert!(!native_evaluation(&code(source)).is_empty(), "{source}");
        }
        for source in [
            "-- native_decide in a comment",
            "def s := \"native_decide\"",
            "theorem t : 2 + 2 = 4 := by decide +kernel",
            "def native_decided := 0",
        ] {
            assert!(native_evaluation(&code(source)).is_empty(), "{source}");
        }
        assert!(native_evaluation_allowed("LfzkV1"));
        assert!(native_evaluation_allowed("LfzkV1.Arith"));
        assert!(native_evaluation_allowed("examples.Ligero.Longfellow.Rows"));
        assert!(!native_evaluation_allowed("LfzkV2.Current.Mdoc"));
        assert!(!native_evaluation_allowed("LfzkV1Extra"));
        assert!(!native_evaluation_allowed("examples.Ligero.Other"));
    }

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
    let (citation_failures, citation_count) = check_design_citations(&paths);
    failures += citation_failures;
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
        // Lean sources, including the offline Hahn certificates, live here.
        if name.ends_with(".lean") && !name.starts_with("formal/") {
            eprintln!("{name}: Lean sources belong under formal/");
            failures += 1;
        }
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
                dependencies.insert(module.clone(), imports(&source)).is_none(),
                "duplicate Lean module"
            );
            if !native_evaluation_allowed(&module) {
                for (line, route) in native_evaluation(&source) {
                    eprintln!(
                        "{name}:{line}: native evaluation ({route}) outside the legacy allowance"
                    );
                    failures += 1;
                }
            }
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
    check_hahn_certificate_sources();
    println!(
        "Scanned {lean_count} Lean sources, {link_count} local documentation links and \
         {citation_count} Lean and test citations in the Rust designs."
    );
    assert!(lean_count > 0, "no Lean sources found");
    assert_eq!(failures, 0, "source/documentation audit failed");
}

/// Offline certificate sources: shared Hahn sources contain only packing
/// arithmetic, and protocol bridges remain separate from the mdoc facade.
fn check_hahn_certificate_sources() {
    fn collect(directory: &Path, out: &mut BTreeSet<PathBuf>) {
        for entry in fs::read_dir(directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                collect(&path, out);
            } else if path.extension().and_then(|s| s.to_str()) == Some("lean") {
                out.insert(path);
            }
        }
    }

    let formal = Path::new("formal/parameters").to_path_buf();
    let shared = formal.join("hahn");
    let mut expected = BTreeSet::from([
        shared.join("RuntimeHahn/Budget.lean"),
        shared.join("RuntimeHahn/HahnPolynomial.lean"),
        shared.join("RuntimeHahn/APITest.lean"),
        shared.join("RuntimeHahn/CheckedPolynomial.lean"),
        shared.join("RuntimeHahn/Coefficients.lean"),
        shared.join("RuntimeHahn/IntegralKernel.lean"),
        shared.join("RuntimeHahn/PolynomialIdentity.lean"),
    ]);
    for (name, degrees, certificate) in [
        ("Hash", 23, true),
        ("Signature", 23, true),
        ("LigeroV7Sig", 9, true),
        ("LigeroV7SigFS", 25, true),
        ("LigeroV7Hash1", 11, true),
        ("LigeroV7Hash2", 11, true),
        ("LigeroV7Hash3", 11, true),
        ("LigeroV7Hash4", 11, true),
        ("MdocRate7Active", 25, false),
        ("MdocRate7Binary", 13, false),
        ("MdocRate7Prime", 15, false),
        ("Benchmark2109", 23, false),
        ("Benchmark2119", 21, false),
        ("Benchmark2129", 19, false),
        ("Benchmark2140", 17, false),
        ("Benchmark2152", 15, false),
    ] {
        if certificate {
            expected.insert(shared.join(format!("RuntimeHahn/{name}.lean")));
        }
        let prefix = "RuntimeHahn/Kernels";
        expected.insert(shared.join(format!("{prefix}/Kernels{name}.lean")));
        let mut first = 1;
        for end in [12, 17, 20, 22, 24, degrees] {
            let last = end.min(degrees);
            let module = if first == last {
                format!("Degree{first:02}")
            } else {
                format!("Degrees{first:02}To{last:02}")
            };
            expected.insert(shared.join(format!("{prefix}/{name}Kernels/{module}.lean")));
            if last == degrees {
                break;
            }
            first = last + 1;
        }
    }
    let mut actual = BTreeSet::new();
    collect(&shared, &mut actual);
    assert_eq!(actual, expected, "update the Hahn source registry");
    for file in actual {
        let source = fs::read_to_string(&file).unwrap();
        for imported in source
            .lines()
            .filter_map(|line| line.strip_prefix("import "))
        {
            assert!(
                imported.starts_with("Mathlib.")
                    || imported.starts_with("RuntimeHahn.")
                    || imported.starts_with("CodingTheory.")
                    // The audit aggregates certificate checks from both libraries.
                    || (file == shared.join("RuntimeHahn/APITest.lean")
                        && imported == "polygero.Benchmarks.HahnRateSixteenth.Certificates"),
                "protocol dependency in shared packing arithmetic {}: {imported}",
                file.display()
            );
        }
    }
    let protocol = formal.join("polygero");
    let mut protocol_files = BTreeSet::new();
    collect(&protocol, &mut protocol_files);
    assert_eq!(
        protocol_files,
        BTreeSet::from([
            protocol.join("MdocJointProfile.lean"),
            protocol.join("PolygeroRustHahn.lean"),
            protocol.join("TunedProfiles.lean"),
        ])
    );
    for generic in ["PolygeroRustHahn.lean", "TunedProfiles.lean"] {
        let source = fs::read_to_string(protocol.join(generic)).unwrap();
        assert!(
            !source
                .lines()
                .filter_map(|line| line.strip_prefix("import "))
                .any(|module| module.starts_with("LfzkV2.")),
            "application certificate belongs in the separate mdoc facade: {generic}"
        );
    }
    assert!(fs::read_to_string(protocol.join("MdocJointProfile.lean"))
        .unwrap()
        .lines()
        .any(|line| line == "import LfzkV2.Current.Parameters.Rate7"));
}
/// Rust source with comments and string literals blanked, like `code` for Lean.
fn rust_code(source: &str) -> String {
    let bytes = source.as_bytes();
    let mut out = bytes.to_vec();
    let mut i = 0;
    let blank = |out: &mut Vec<u8>, from: usize, to: usize| {
        for b in &mut out[from..to] {
            if *b != b'\n' {
                *b = b' ';
            }
        }
    };
    while i < bytes.len() {
        if bytes[i..].starts_with(b"//") {
            let end = bytes[i..]
                .iter()
                .position(|&b| b == b'\n')
                .map_or(bytes.len(), |n| i + n);
            blank(&mut out, i, end);
            i = end;
        } else if bytes[i..].starts_with(b"/*") {
            let (mut depth, mut j) = (1, i + 2);
            while j < bytes.len() && depth > 0 {
                if bytes[j..].starts_with(b"/*") {
                    depth += 1;
                    j += 2;
                } else if bytes[j..].starts_with(b"*/") {
                    depth -= 1;
                    j += 2;
                } else {
                    j += 1;
                }
            }
            blank(&mut out, i, j);
            i = j;
        } else if bytes[i] == b'r'
            && (i == 0 || !(bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_'))
            && bytes[i + 1..].starts_with(b"#")
            || bytes[i..].starts_with(b"r\"")
                && (i == 0 || !(bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_'))
        {
            // A raw string: r"...", r#"..."#, and so on.
            let hashes = bytes[i + 1..].iter().take_while(|&&b| b == b'#').count();
            let open = i + 1 + hashes;
            if bytes.get(open) != Some(&b'"') {
                i += 1;
                continue;
            }
            let mut close = b"\"".to_vec();
            close.extend(std::iter::repeat_n(b'#', hashes));
            let end = (open + 1..bytes.len())
                .find(|&j| bytes[j..].starts_with(&close))
                .map_or(bytes.len(), |j| j + close.len());
            blank(&mut out, i, end);
            i = end;
        } else if bytes[i] == b'"' {
            let mut j = i + 1;
            while j < bytes.len() && bytes[j] != b'"' {
                j += if bytes[j] == b'\\' { 2 } else { 1 };
            }
            let end = (j + 1).min(bytes.len());
            blank(&mut out, i, end);
            i = end;
        } else {
            i += 1;
        }
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn identifiers(text: &str) -> impl Iterator<Item = &str> {
    text.split(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'')
        .filter(|word| word.starts_with(|c: char| c.is_alphabetic() || c == '_'))
}

/// The names a Lean source (comments and strings blanked) declares: each
/// component of a declared name, constructors and structure fields.
fn lean_declarations(code: &str, out: &mut BTreeSet<String>) {
    const KEYWORDS: &[&str] = &[
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "structure",
        "inductive",
        "class",
        "instance",
        "opaque",
        "namespace",
        "section",
    ];
    for line in code.lines() {
        let mut words = line.split_whitespace();
        while let Some(word) = words.next() {
            if KEYWORDS.contains(&word)
                && let Some(name) = words.clone().next()
            {
                let name = name.split(['(', '[', '{', ':']).next().unwrap();
                out.extend(name.split('.').filter(|c| !c.is_empty()).map(str::to_owned));
            }
        }
        let trimmed = line.trim_start();
        let first = |text: &str| identifiers(text).next().map(str::to_owned);
        if let Some(rest) = trimmed.strip_prefix('|') {
            out.extend(first(rest));
        } else if trimmed.len() < line.len()
            && let Some((field, _)) = trimmed.split_once(':')
            && identifiers(field).count() == 1
            && field
                .trim()
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
        {
            out.extend(first(field));
        }
    }
}

/// Inline code spans of a Markdown file outside fenced blocks, with the line
/// each starts on. A span may continue onto the next line.
fn code_spans(markdown: &str) -> Vec<(usize, String)> {
    let mut spans = Vec::new();
    let mut paragraph: Vec<(usize, &str)> = Vec::new();
    let mut fenced = false;
    let mut flush = |paragraph: &mut Vec<(usize, &str)>| {
        let mut open: Option<(usize, String)> = None;
        for &(line, text) in paragraph.iter() {
            for (k, piece) in text.split('`').enumerate() {
                if k > 0 {
                    match open.take() {
                        Some(span) => spans.push(span),
                        None => open = Some((line, String::new())),
                    }
                }
                if let Some((_, span)) = &mut open {
                    if k == 0 && !span.is_empty() {
                        span.push(' ');
                    }
                    span.push_str(piece);
                }
            }
        }
        paragraph.clear();
    };
    for (line, text) in markdown.lines().enumerate() {
        if text.trim_start().starts_with("```") {
            flush(&mut paragraph);
            fenced = !fenced;
        } else if !fenced {
            if text.trim().is_empty() || text.starts_with('|') {
                flush(&mut paragraph);
            }
            paragraph.push((line + 1, text));
            if text.starts_with('|') {
                flush(&mut paragraph);
            }
        }
    }
    flush(&mut paragraph);
    spans
}

/// A dotted Lean name, `Namespace.Sub.name`: CamelCase namespaces, then a
/// declaration name. File names such as `DESIGN.md` are not.
fn lean_citation(span: &str) -> Option<&str> {
    let (namespaces, name) = span.rsplit_once('.')?;
    let camel = |part: &str| {
        part.starts_with(|c: char| c.is_ascii_uppercase())
            && part.chars().all(|c| c.is_ascii_alphanumeric() || c == '\'')
    };
    let file = ["rs", "md", "txt", "lean", "toml", "json", "py", "sh"].contains(&name);
    (!file
        && namespaces.split('.').all(camel)
        && name.starts_with(|c: char| c.is_alphabetic() || c == '_')
        && name
            .chars()
            .all(|c| c.is_alphanumeric() || "_'!?".contains(c)))
    .then_some(name)
}

/// A snake-case name of three or more words, as Rust test names are; a
/// trailing `*` cites every name with that prefix.
fn test_citation(span: &str) -> Option<&str> {
    let name = span.strip_suffix('*').unwrap_or(span);
    let words: Vec<_> = name.split('_').collect();
    (words.len() >= 3
        && words[0].starts_with(|c: char| c.is_ascii_lowercase())
        && words.iter().all(|word| {
            !word.is_empty()
                && word
                    .chars()
                    .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit())
        }))
    .then_some(span)
}

/// Every Lean name a `rust/**/DESIGN.md` cites must be declared in some Lean
/// source, matching on its last component (a cited namespace may abbreviate
/// or nest differently), and every Rust test name it cites must exist in the
/// Rust code, a Lean source, or as a file. Returns the failures and the
/// number of citations checked.
fn check_design_citations(paths: &BTreeSet<&str>) -> (usize, usize) {
    let (mut lean, mut rust) = (BTreeSet::new(), BTreeSet::new());
    for name in paths {
        let path = Path::new(name);
        let is_lean = name.starts_with("formal/") && name.ends_with(".lean");
        let is_rust =
            name.ends_with(".rs") && (name.starts_with("rust/") || name.starts_with("formal/"));
        if !is_lean && !is_rust {
            continue;
        }
        let stems = name.trim_end_matches(".lean").trim_end_matches(".rs");
        let names = if is_lean { &mut lean } else { &mut rust };
        names.extend(stems.split('/').map(str::to_owned));
        let source = fs::read_to_string(path).unwrap();
        if is_lean {
            lean_declarations(&code(&source), &mut lean);
        } else {
            rust.extend(identifiers(&rust_code(&source)).map(str::to_owned));
        }
    }
    let (mut failures, mut checked) = (0, 0);
    for name in paths {
        if !(name.starts_with("rust/") && name.ends_with("/DESIGN.md")) {
            continue;
        }
        for (line, span) in code_spans(&fs::read_to_string(name).unwrap()) {
            let span = span.trim();
            if let Some(last) = lean_citation(span) {
                checked += 1;
                if !lean.contains(last) {
                    eprintln!("{name}:{line}: cites `{span}`, but no Lean source declares {last}");
                    failures += 1;
                }
            } else if let Some(test) = test_citation(span) {
                checked += 1;
                let found = match test.strip_suffix('*') {
                    Some(prefix) => rust.iter().any(|n| n.starts_with(prefix)),
                    None => rust.contains(test) || lean.contains(test),
                };
                if !found {
                    eprintln!(
                        "{name}:{line}: cites `{span}`, which no Rust or Lean source defines"
                    );
                    failures += 1;
                }
            }
        }
    }
    (failures, checked)
}
