// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The steps, in the order they run.
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

use crate::{
    clippy::{BaselineKey, Counts},
    context::Context,
    run::{diagnostics, tail, why, Log, Outcome, Run},
};

pub(crate) struct Step {
    pub(crate) name: &'static str,
    pub(crate) what: &'static str,
    /// Whether the step is one of the formal checks, run with `--formal`.
    pub(crate) formal: bool,
    pub(crate) run: fn(&Context, &mut Log) -> Outcome,
}

pub(crate) fn all() -> Vec<Step> {
    let step = |name, what, run| Step {
        name,
        what,
        formal: false,
        run,
    };
    let formal = |name, what, run| Step {
        name,
        what,
        formal: true,
        run,
    };
    vec![
        step("fmt", "cargo fmt and rustfmt of the cfg_*! modules", fmt),
        step(
            "features",
            "every role and feature build, warning-free",
            features,
        ),
        step("deps", "the dependency check", deps),
        step(
            "roles",
            "standalone roles pull no compiler or tool crates",
            roles,
        ),
        step("clippy", "clippy warnings do not increase", clippy),
        step("tests", "release tests", tests),
        step(
            "doctests",
            "doctests: nightly testonly (compile_fail codes) and stable default features",
            doctests,
        ),
        step("cross", "other backends, when arch code changed", cross),
        step("inspectors", "the formal/lfzk-v1 inspectors", inspectors),
        step("round-shapes", "check_mdoc_round_shapes", round_shapes),
        formal("lake", "lake build", lake),
        formal("security-audit", "lake build SecurityAudit", security_audit),
        formal("source-audit", "formal/scripts/audit.rs", source_audit),
        formal(
            "certify-hahn",
            "zk_tool certify-hahn, fresh cache",
            certify_hahn,
        ),
        formal("check-profiles", "zk_tool check-profiles", check_profiles),
    ]
}

/// The role and feature combinations that must build warning-free alone. The
/// generic v2 roles build without the mdoc application, the prover and the
/// verifier each without the other, and without v1 nothing needs the v1
/// runtime or AES; the compiler builds check this for offline code too.
const FEATURE_SETS: [&str; 11] = [
    "",
    "verifier",
    "prover",
    "verifier,prover",
    "verifier,mdoc",
    "prover,mdoc",
    "prover,verifier,mdoc",
    "verifier,mdoc,v1",
    "prover,mdoc,v1",
    "compiler",
    "compiler,mdoc",
];

/// The standalone prover and verifier, deployed (v1) and v2.
const ROLE_SETS: [&str; 6] = [
    "prover,mdoc,v1",
    "verifier,mdoc,v1",
    "prover,mdoc",
    "verifier,mdoc",
    "prover",
    "verifier",
];

/// The compiler's crates, which no proof role may pull.
const COMPILER_CRATES: [&str; 4] = ["bumpalo", "num-bigint", "num-traits", "rustc-hash"];

/// The tools' own crates, which the library never pulls.
const TOOL_CRATES: [&str; 3] = ["protobuf", "scip", "serde_json"];

/// The tools, a second member of the workspace in `rust/tools`.
const TOOLS: &str = "longfellow-zk-tools";

/// The cross and alternative-backend checks: x86-64 does not compile them.
const CROSS_CHECKS: [&str; 6] = [
    "--target aarch64-unknown-linux-gnu --lib --tests --no-default-features --features \
     testonly",
    "--target armv7-unknown-linux-gnueabihf --lib --tests --benches --features testonly",
    "--target armv7-unknown-linux-gnueabihf --lib --tests --features testonly,arm-neon",
    "--target i686-unknown-linux-gnu --lib --tests --benches --features testonly",
    "--lib --tests --features testonly,force-generic-arch",
    "--lib --tests --features testonly,limb32",
];

/// Paths and source text that make a change architecture-specific.
const ARCH_PATHS: [&str; 2] = ["runtime/algebra/arch", "runtime/algebra/limb"];
const ARCH_WORDS: [&str; 5] = [
    "target_arch",
    "target_pointer_width",
    "limb32",
    "force-generic-arch",
    "arm-neon",
];

/// A step that passes when every command runs clean: succeeds and prints no
/// diagnostics. `commands` pairs each command with its label. Every command
/// runs, so that a failure names all the unclean ones; the detail shows the
/// first one's diagnostics.
fn all_clean(log: &mut Log, commands: Vec<(String, Command)>, summary: String) -> Outcome {
    let total = commands.len();
    let mut unclean = Vec::new();
    let mut detail = String::new();
    for (label, mut command) in commands {
        let run = log.run(&mut command);
        if !run.success || !diagnostics(&run.output, 1).is_empty() {
            if unclean.is_empty() {
                detail = format!("{label}:\n{}", why(&run));
            }
            unclean.push(label);
        }
    }
    if unclean.is_empty() {
        Outcome::Passed(format!("{summary} ({total} commands)"))
    } else {
        Outcome::Failed(
            format!(
                "{} of {total} not clean: {}",
                unclean.len(),
                unclean.join("; ")
            ),
            detail,
        )
    }
}

fn fmt(cx: &Context, log: &mut Log) -> Outcome {
    let check = cx.options.fmt_check;
    let mut cargo_fmt = cx.command(&cx.rust, "cargo");
    cargo_fmt.args(["+nightly", "fmt", "--all"]);
    if check {
        cargo_fmt.args(["--", "--check"]);
    }
    let run = log.run(&mut cargo_fmt);
    if !run.success {
        return Outcome::Failed("cargo +nightly fmt".into(), tail(&run.output, 20));
    }
    // `cargo fmt` does not reach modules declared inside the `cfg_*!` macros.
    let Some(files) = cx.git_text(&["-C", "rust", "ls-files", "src/*.rs", "benches/*.rs"]) else {
        return Outcome::Failed("git ls-files failed".into(), String::new());
    };
    let mut rustfmt = cx.command(&cx.rust, "rustfmt");
    rustfmt.args([
        "+nightly",
        "--edition",
        "2021",
        "--config",
        "skip_children=true",
    ]);
    if check {
        rustfmt.arg("--check");
    }
    rustfmt.args(files.lines());
    let second = log.run(&mut rustfmt);
    if !second.success {
        return Outcome::Failed(
            "rustfmt of the cfg_*! modules".into(),
            tail(&second.output, 20),
        );
    }
    Outcome::Passed(
        if check {
            "formatted"
        } else {
            "formatted in place"
        }
        .into(),
    )
}

fn features(cx: &Context, log: &mut Log) -> Outcome {
    let mut commands: Vec<_> = FEATURE_SETS
        .iter()
        .map(|set| {
            let mut command = cx.cargo("check --lib --bins --no-default-features --features");
            command.arg(set);
            (format!("[{set}]"), command)
        })
        .collect();
    // The tests without the mdoc application, which the `--lib` role builds
    // do not compile.
    for args in [
        "check --lib --tests --no-default-features --features testonly",
        "check --features testonly --tests --benches --bins",
        "check --all-targets",
    ] {
        commands.push((args.to_owned(), cx.cargo(args)));
    }
    // The tools, with the library features they ask for.
    let tools = format!("check -p {TOOLS} --all-targets");
    commands.push((tools.clone(), cx.cargo(&tools)));
    all_clean(log, commands, "warning-free".into())
}

fn deps(cx: &Context, log: &mut Log) -> Outcome {
    let run = log.run(&mut cx.cargo(&format!("run --release -p {TOOLS} --bin dependency_check")));
    let summary = run
        .output
        .lines()
        .rfind(|line| line.contains(" files, "))
        .unwrap_or("")
        .to_owned();
    if run.success {
        Outcome::Passed(summary)
    } else {
        Outcome::Failed("dependency check failed".into(), tail(&run.output, 20))
    }
}

fn roles(cx: &Context, log: &mut Log) -> Outcome {
    for set in ROLE_SETS {
        let mut command =
            cx.cargo("tree -q -e normal --prefix none --no-default-features --features");
        command.arg(set);
        let run = log.run(&mut command);
        if !run.success {
            return Outcome::Failed(format!("cargo tree [{set}] failed"), tail(&run.output, 20));
        }
        let mut pulled: Vec<_> = run
            .output
            .lines()
            .filter_map(|line| line.split(' ').next())
            .filter(|name| COMPILER_CRATES.contains(name) || TOOL_CRATES.contains(name))
            .collect();
        pulled.sort_unstable();
        pulled.dedup();
        if !pulled.is_empty() {
            return Outcome::Failed(
                format!(
                    "[{set}] pulls compiler or tool crates: {}",
                    pulled.join(", ")
                ),
                String::new(),
            );
        }
    }
    Outcome::Passed(format!(
        "{} role builds pull none of {}, {}",
        ROLE_SETS.len(),
        COMPILER_CRATES.join(", "),
        TOOL_CRATES.join(", ")
    ))
}

/// The clippy runs whose warnings count, each for its own package: the
/// library with its default features, and the tools (whose run also lints
/// the library, with the features the tools ask for; those warnings belong
/// to the first run). A tools label starts with `tools-`.
const CLIPPY_RUNS: [(&str, &str, &str); 2] = [
    ("clippy --all-targets", "longfellow-zk", ""),
    (
        "clippy -p longfellow-zk-tools --all-targets",
        TOOLS,
        "tools-",
    ),
];

/// The warning counts of every run of [`CLIPPY_RUNS`] in `directory`, with
/// `target` as the target directory; a run whose package `directory` lacks
/// (the tools, before they were a workspace member) counts none.
fn clippy_counts(log: &mut Log, directory: &Path, target: &Path) -> Result<Counts, Run> {
    let mut counts = Counts::default();
    for (args, package, prefix) in CLIPPY_RUNS {
        if package == TOOLS && !directory.join("tools/Cargo.toml").is_file() {
            continue;
        }
        let mut command = Command::new("cargo");
        command
            .current_dir(directory)
            .env("CARGO_TARGET_DIR", target)
            .args(args.split_whitespace());
        let run = log.run(&mut command);
        if !run.success {
            return Err(run);
        }
        counts.add(Counts::of_output(&run.output, package, prefix));
    }
    Ok(counts)
}

fn clippy(cx: &Context, log: &mut Log) -> Outcome {
    let counts = match clippy_counts(log, &cx.rust, &cx.target) {
        Ok(counts) => counts,
        Err(run) => return Outcome::Failed("cargo clippy failed".into(), why(&run)),
    };
    let (baseline, source) = match &cx.options.clippy_counts {
        Some(given) => (given.clone(), "given".to_owned()),
        None => match cx
            .base()
            .and_then(|base| base_counts(cx, log, &base).map(|c| (c, base)))
        {
            Ok((measured, base)) => (measured, base[..12].to_owned()),
            Err(error) => {
                return Outcome::Failed(format!("clippy {counts}; {error}"), String::new())
            }
        },
    };
    let increases = counts.increases(&baseline);
    let summary = format!("{counts} (baseline {source}: {baseline})");
    if increases.is_empty() {
        Outcome::Passed(summary)
    } else {
        let detail = increases
            .iter()
            .map(|(label, before, after)| format!("{label}: {before} -> {after}"))
            .collect::<Vec<_>>()
            .join("\n");
        Outcome::Failed(format!("more warnings: {summary}"), detail)
    }
}

/// The variables through which the environment adds compiler flags to the
/// clippy runs.
const CLIPPY_FLAG_VARIABLES: [&str; 4] = [
    "RUSTFLAGS",
    "CARGO_ENCODED_RUSTFLAGS",
    "CARGO_BUILD_RUSTFLAGS",
    "CLIPPY_CONF_DIR",
];

/// The key of the clippy baseline of `base` in this environment: the
/// toolchain that runs clippy in `rust/`, this checkout's `Cargo.lock`, the
/// clippy runs and the flags the environment adds.
fn baseline_key(cx: &Context, base: &str) -> Result<BaselineKey, String> {
    let version = |program: &str, args: &str| {
        let output = cx
            .command(&cx.rust, program)
            .args(args.split_whitespace())
            .output()
            .map_err(|e| format!("{program} {args}: {e}"))?;
        if !output.status.success() {
            return Err(format!("{program} {args} failed"));
        }
        Ok(String::from_utf8_lossy(&output.stdout).into_owned())
    };
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
    let lock_path = cx.rust.join("Cargo.lock");
    let lock = fs::read(&lock_path).map_err(|e| format!("{}: {e}", lock_path.display()))?;
    let runs: Vec<_> = CLIPPY_RUNS.iter().map(|(args, _, _)| *args).collect();
    let flags: Vec<_> = CLIPPY_FLAG_VARIABLES
        .iter()
        .filter_map(|name| {
            std::env::var_os(name).map(|value| format!("{name}={}", value.to_string_lossy()))
        })
        .collect();
    Ok(BaselineKey::new(
        base,
        &version(&rustc, "-vV")?,
        &version("cargo", "clippy -V")?,
        &lock,
        &runs,
        &flags,
    ))
}

/// The clippy counts of commit `base`, measured on an export of its `rust/`
/// with this checkout's `Cargo.lock`, and saved by commit with the
/// [`BaselineKey`] they were measured under; saved counts are reused only
/// under the same key.
fn base_counts(cx: &Context, log: &mut Log, base: &str) -> Result<Counts, String> {
    let directory = cx.work.join("clippy-base");
    let saved = directory.join(format!("{base}.counts"));
    let key = baseline_key(cx, base)?;
    if let Ok(text) = fs::read_to_string(&saved) {
        if let Some(counts) = key.saved(&text) {
            log.note(&format!(
                "baseline counts of {base} from {}",
                saved.display()
            ));
            return Ok(counts);
        }
        log.note(&format!(
            "{} was measured in another environment; measuring again",
            saved.display()
        ));
    }
    let source = directory.join("src");
    let _ = fs::remove_dir_all(&source);
    fs::create_dir_all(&source).map_err(|e| format!("{}: {e}", source.display()))?;
    log.note(&format!("exporting {base}:rust to {}", source.display()));
    let mut archive = cx
        .git(&["archive", "--format=tar", base, "rust"])
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|e| format!("git archive: {e}"))?;
    let unpacked = archive.stdout.take().map(|tar| {
        Command::new("tar")
            .arg("-x")
            .arg("-C")
            .arg(&source)
            .stdin(tar)
            .status()
    });
    let archived = archive.wait().map(|s| s.success()).unwrap_or(false);
    if !archived || !matches!(unpacked, Some(Ok(status)) if status.success()) {
        return Err(format!("cannot export {base}"));
    }
    let crate_dir = source.join("rust");
    let _ = fs::copy(cx.rust.join("Cargo.lock"), crate_dir.join("Cargo.lock"));
    let counts = clippy_counts(log, &crate_dir, &directory.join("target"))
        .map_err(|_| format!("clippy of {base} failed; see the log"))?;
    let _ = fs::write(&saved, key.save(&counts));
    let _ = fs::remove_dir_all(&source);
    Ok(counts)
}

/// The totals of the harness's `test result:` lines.
pub(crate) fn test_totals(output: &str) -> (usize, usize, usize) {
    let mut totals = (0, 0, 0);
    for line in output.lines().filter(|l| l.starts_with("test result:")) {
        let number = |word: &str| {
            line.split(';')
                .find(|part| part.trim_end().ends_with(word))
                .and_then(|part| part.split_whitespace().rev().nth(1))
                .and_then(|n| n.parse::<usize>().ok())
                .unwrap_or(0)
        };
        totals.0 += number("passed");
        totals.1 += number("failed");
        totals.2 += number("ignored");
    }
    totals
}

/// A test run passes when it succeeds, every result line has no failures,
/// and its build printed no diagnostics.
fn test_outcome(run: &Run) -> Outcome {
    let (passed, failed, ignored) = test_totals(&run.output);
    let summary = format!("{passed} passed, {failed} failed, {ignored} ignored");
    let clean = diagnostics(&run.output, 1).is_empty();
    if run.success && failed == 0 && passed > 0 && clean {
        Outcome::Passed(summary)
    } else {
        let failures: Vec<_> = run
            .output
            .lines()
            .filter(|line| line.contains("FAILED") || line.contains("panicked"))
            .take(20)
            .collect();
        let detail = if failures.is_empty() {
            why(run)
        } else {
            failures.join("\n")
        };
        Outcome::Failed(summary, detail)
    }
}

fn tests(cx: &Context, log: &mut Log) -> Outcome {
    // The library's tests, then the tools'.
    let library = log.run(&mut cx.cargo("test --release --features testonly"));
    let tools = log.run(&mut cx.cargo(&format!("test --release -p {TOOLS}")));
    test_outcome(&Run {
        success: library.success && tools.success,
        output: library.output + &tools.output,
    })
}

fn doctests(cx: &Context, log: &mut Log) -> Outcome {
    // On nightly with testonly, which checks the compile_fail error codes;
    // then on stable with the default features, as a plain `cargo test`
    // builds them.
    let mut nightly_command = cx.cargo_into(
        &cx.work.join("nightly"),
        "+nightly test --release --features testonly --doc",
    );
    let nightly = log.run(&mut nightly_command);
    let default = log.run(&mut cx.cargo("test --release --doc"));
    test_outcome(&Run {
        success: nightly.success && default.success,
        output: nightly.output + &default.output,
    })
}

/// Whether the change since `base` touches architecture-specific code: a
/// path under the backends or limbs, or a changed line of the library, the
/// benches or the build configuration naming an architecture or a backend
/// switch (the tools, which name them as text, are left out). Untracked
/// files count as changes.
fn arch_changed(cx: &Context, base: &str) -> bool {
    let names = cx
        .git_text(&["diff", "--name-only", base])
        .unwrap_or_default();
    let untracked = cx
        .git_text(&["ls-files", "--others", "--exclude-standard"])
        .unwrap_or_default();
    let paths = names.lines().chain(untracked.lines());
    if paths
        .clone()
        .any(|path| ARCH_PATHS.iter().any(|a| path.contains(a)))
    {
        return true;
    }
    let names_word = |text: &str| ARCH_WORDS.iter().any(|word| text.contains(word));
    let code = |path: &str| {
        let library = [
            "rust/src/",
            "rust/benches/",
            "rust/.cargo/",
            "rust/Cargo.toml",
        ]
        .iter()
        .any(|p| path.starts_with(p));
        library && !path.starts_with("rust/src/bin/")
    };
    let mut diff = cx.git(&["diff", base, "--"]);
    diff.args(CODE_PATHSPECS);
    let changed = diff
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).into_owned())
        .unwrap_or_default()
        .lines()
        .filter(|line| !line.starts_with("+++") && !line.starts_with("---"))
        .filter(|line| line.starts_with('+') || line.starts_with('-'))
        .any(names_word);
    changed
        || untracked
            .lines()
            .filter(|path| code(path) && path.ends_with(".rs"))
            .any(|path| fs::read_to_string(cx.root.join(path)).is_ok_and(|text| names_word(&text)))
}

/// The library, benches and build configuration, without the tools.
const CODE_PATHSPECS: [&str; 5] = [
    "rust/src",
    "rust/benches",
    "rust/.cargo",
    "rust/Cargo.toml",
    ":(exclude)rust/src/bin",
];

/// The C compiler for aarch64 (sha2's assembly needs one): the configured
/// one, the GNU cross compiler, or clang targeting aarch64.
fn aarch64_cc() -> Option<String> {
    let found = |program: &str| {
        Command::new(program)
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok_and(|s| s.success())
    };
    if std::env::var_os("CC_aarch64_unknown_linux_gnu").is_some() || found("aarch64-linux-gnu-gcc")
    {
        return None;
    }
    ["clang-19", "clang"]
        .into_iter()
        .find(|clang| found(clang))
        .map(|clang| format!("{clang} --target=aarch64-linux-gnu"))
}

fn cross(cx: &Context, log: &mut Log) -> Outcome {
    let reason = match cx.options.cross {
        Some(false) => return Outcome::Skipped("skipped (--no-cross)".into()),
        Some(true) => "--cross".to_owned(),
        None => match cx.base() {
            Ok(base) if arch_changed(cx, &base) => {
                format!("arch code changed since {}", &base[..12])
            }
            Ok(base) => {
                return Outcome::Skipped(format!(
                    "skipped (no architecture-specific change since {})",
                    &base[..12]
                ))
            }
            Err(error) => format!("{error}; checking anyway"),
        },
    };
    let target = cx.work.join("cross");
    let aarch64 = aarch64_cc();
    let commands = CROSS_CHECKS
        .iter()
        .map(|args| {
            let mut command = cx.cargo_into(&target, "check -q");
            command.args(args.split_whitespace());
            if let Some(cc) = &aarch64 {
                command.env("CC_aarch64_unknown_linux_gnu", cc);
                command.env("AR_aarch64_unknown_linux_gnu", "ar");
            }
            ((*args).to_owned(), command)
        })
        .collect();
    all_clean(log, commands, format!("warning-free ({reason})"))
}

fn inspectors(cx: &Context, log: &mut Log) -> Outcome {
    let scripts = cx.root.join("formal/lfzk-v1/scripts");
    let target = cx.work.join("inspectors");
    let mut build = cx.command(&scripts, "cargo");
    build
        .env("CARGO_TARGET_DIR", &target)
        .args(["build", "--release"]);
    let built = log.run(&mut build);
    if !built.success || !diagnostics(&built.output, 1).is_empty() {
        return Outcome::Failed("inspector build not clean".into(), why(&built));
    }
    let mut last = String::new();
    for inspector in ["inspect-v7-profile", "inspect-v7-assertions"] {
        let binary: PathBuf = target.join("release").join(inspector);
        let run = log.run(&mut cx.command(&scripts, &binary));
        if !run.success {
            return Outcome::Failed(format!("{inspector} failed"), tail(&run.output, 20));
        }
        if inspector == "inspect-v7-profile" {
            last = tail(&run.output, 1);
        }
    }
    Outcome::Passed(last)
}

/// Compile a standalone formal script into the work directory.
fn script(cx: &Context, log: &mut Log, source: &str) -> Result<PathBuf, Outcome> {
    let stem = Path::new(source).file_stem().unwrap_or_default();
    let binary = cx.work.join(stem);
    let mut rustc = cx.command(&cx.root, "rustc");
    rustc
        .args(["--edition", "2024", "-O", source, "-o"])
        .arg(&binary);
    let run = log.run(&mut rustc);
    if run.success {
        Ok(binary)
    } else {
        Err(Outcome::Failed(
            format!("cannot compile {source}"),
            why(&run),
        ))
    }
}

/// Run a compiled script at the repository root; it passes when it
/// succeeds, and reports its last line.
fn run_script(cx: &Context, log: &mut Log, binary: &Path) -> Outcome {
    let mut command = cx.command(&cx.root, binary);
    // The scripts build the crate into `rust/target` themselves.
    command.env_remove("CARGO_TARGET_DIR");
    let run = log.run(&mut command);
    if run.success {
        Outcome::Passed(tail(&run.output, 1))
    } else {
        Outcome::Failed(
            format!("{} failed", binary.display()),
            tail(&run.output, 20),
        )
    }
}

fn round_shapes(cx: &Context, log: &mut Log) -> Outcome {
    match script(cx, log, "formal/scripts/check_mdoc_round_shapes.rs") {
        Ok(binary) => run_script(cx, log, &binary),
        Err(outcome) => outcome,
    }
}

fn source_audit(cx: &Context, log: &mut Log) -> Outcome {
    match script(cx, log, "formal/scripts/audit.rs") {
        Ok(binary) => run_script(cx, log, &binary),
        Err(outcome) => outcome,
    }
}

/// `lake build [target]` in `formal/`.
fn lake_build(cx: &Context, log: &mut Log, target: Option<&str>) -> Outcome {
    let mut command = cx.command(&cx.root.join("formal"), "lake");
    command.arg("build").args(target);
    let run = log.run(&mut command);
    // Lean reports a `sorry` as a warning; nothing may use one.
    if run.success && !run.output.contains("declaration uses 'sorry'") {
        Outcome::Passed(tail(&run.output, 1))
    } else {
        let errors: Vec<_> = run
            .output
            .lines()
            .filter(|line| line.starts_with("error") || line.contains("sorry"))
            .take(20)
            .collect();
        let detail = if errors.is_empty() {
            tail(&run.output, 20)
        } else {
            errors.join("\n")
        };
        Outcome::Failed("lake build failed".into(), detail)
    }
}

fn lake(cx: &Context, log: &mut Log) -> Outcome {
    lake_build(cx, log, None)
}

fn security_audit(cx: &Context, log: &mut Log) -> Outcome {
    lake_build(cx, log, Some("SecurityAudit"))
}

/// The Hahn certificate cache of this run, which `certify-hahn` refills.
fn hahn_cache(cx: &Context) -> PathBuf {
    cx.work.join("hahn-cache")
}

/// `zk_tool` with `args`, run from `rust/`.
fn zk_tool(cx: &Context, log: &mut Log, args: &str, cache: &Path) -> Outcome {
    let mut command = cx.cargo(&format!("run -q --release -p {TOOLS} --bin zk_tool --"));
    command.args(args.split_whitespace()).arg(cache);
    let run = log.run(&mut command);
    if run.success {
        Outcome::Passed(tail(&run.output, 1))
    } else {
        Outcome::Failed("zk_tool failed".into(), tail(&run.output, 20))
    }
}

fn certify_hahn(cx: &Context, log: &mut Log) -> Outcome {
    let cache = hahn_cache(cx);
    let _ = fs::remove_dir_all(&cache);
    zk_tool(cx, log, "certify-hahn --formal ../formal --cache", &cache)
}

fn check_profiles(cx: &Context, log: &mut Log) -> Outcome {
    let cache = hahn_cache(cx);
    if !cache.is_dir() {
        return Outcome::Failed(
            "no Hahn cache; run certify-hahn first".into(),
            String::new(),
        );
    }
    zk_tool(
        cx,
        log,
        "check-profiles --protocol polygero --check-lean ../formal --hahn-cache",
        &cache,
    )
}
