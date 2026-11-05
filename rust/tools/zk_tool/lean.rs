// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Reproducible Lean checks for generic packing bounds and the v2 verifier.
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::Mutex,
};

use serde_json::json;

use crate::{
    cache,
    exact::choose,
    profiles::{self, Audit, Profile, Protocol},
    require, root, Args, Result,
};

type Environment = BTreeMap<String, String>;
fn library_environment(project: &Path) -> Result<Environment> {
    let toolchain = fs::read_to_string(project.join("lean-toolchain"))?
        .trim()
        .to_owned();
    let out = Command::new("lake")
        .args(["-d"])
        .arg(project)
        .args(["env", "printenv", "LEAN_PATH"])
        .env("ELAN_TOOLCHAIN", &toolchain)
        .output()?;
    require(
        out.status.success(),
        format!(
            "lake environment failed: {}",
            String::from_utf8_lossy(&out.stderr)
        ),
    )?;
    let raw = String::from_utf8(out.stdout)?;
    let paths: Vec<_> = std::env::split_paths(raw.trim())
        .map(|p| if p.is_absolute() { p } else { project.join(p) })
        .collect();
    Ok(BTreeMap::from([
        ("ELAN_TOOLCHAIN".into(), toolchain),
        (
            "LEAN_PATH".into(),
            std::env::join_paths(paths)?
                .into_string()
                .map_err(|_| "non-UTF8 Lean path")?,
        ),
    ]))
}
fn prepend(env: &mut Environment, paths: impl IntoIterator<Item = PathBuf>) -> Result<()> {
    let mut all: Vec<_> = paths.into_iter().collect();
    all.extend(std::env::split_paths(
        env.get("LEAN_PATH").ok_or("missing LEAN_PATH")?,
    ));
    env.insert(
        "LEAN_PATH".into(),
        std::env::join_paths(all)?
            .into_string()
            .map_err(|_| "non-UTF8 Lean path")?,
    );
    Ok(())
}
fn compile(cache: &Path, relative: &Path, env: &Environment) -> Result<()> {
    let source = cache.join("modules").join(relative);
    let target = source.with_extension("olean");
    if fs::symlink_metadata(&target).is_ok_and(|m| m.file_type().is_symlink()) {
        fs::remove_file(&target)?;
    }
    let log = cache.join("logs").join(relative).with_extension("log");
    fs::create_dir_all(log.parent().unwrap())?;
    let stream = fs::File::create(&log)?;
    let status = Command::new("lean")
        .args([
            "-j2",
            "-DwarningAsError=true",
            "-DautoImplicit=false",
            "-DrelaxedAutoImplicit=false",
            "-R",
        ])
        .arg(cache.join("modules"))
        .arg("-o")
        .arg(target)
        .arg(&source)
        .envs(env)
        .stdout(Stdio::from(stream.try_clone()?))
        .stderr(Stdio::from(stream))
        .status()?;
    require(
        status.success(),
        format!(
            "Lean rejected {}; inspect {}",
            relative.display(),
            log.display()
        ),
    )?;
    println!("Checked {}", relative.display());
    Ok(())
}

/// Invalidate completed status before staging; retain prior hashes for safe leaf reuse.
fn stage_modules(
    cache: &Path,
    files: &BTreeMap<PathBuf, PathBuf>,
    reuse: Option<&Path>,
) -> Result<(BTreeMap<String, String>, BTreeSet<String>)> {
    let state_path = cache.join("build-state.json");
    let previous = if state_path.is_file() {
        cache::read_json(&state_path)?
    } else {
        json!({})
    };
    // Preserve only previously checked hashes for expensive leaf reuse after a failed rebuild.
    let previous_hashes = previous["source_sha256"]
        .as_object()
        .cloned()
        .unwrap_or_default();
    cache::write_json(
        &state_path,
        &json!({"status":"building","source_sha256":previous_hashes}),
    )?;
    let modules = cache.join("modules");
    let mut hashes = BTreeMap::new();
    let mut ready = BTreeSet::new();
    for (relative, source) in files {
        let key = relative.to_string_lossy().into_owned();
        let candidate = reuse.map(|p| p.join(relative));
        let (hash, checked) = cache::stage(
            source,
            &modules.join(relative),
            &modules,
            previous_hashes.get(&key).and_then(|v| v.as_str()),
            candidate.as_deref(),
        )?;
        hashes.insert(key.clone(), hash);
        if checked {
            ready.insert(key);
        }
    }
    Ok((hashes, ready))
}

/// Keep all generated modules in a private overlay of the formal library.
fn environment(cache: &Path, formal: &Path) -> Result<Environment> {
    let mut env = library_environment(formal)?;
    prepend(&mut env, [cache.join("modules")])?;
    cache::write_json(&cache.join("environment.json"), &json!(env))?;
    Ok(env)
}

/// Compile missing Gram leaves with a bounded pool; all failures reach the caller.
fn compile_leaves(
    cache: &Path,
    env: &Environment,
    pending: Vec<PathBuf>,
    jobs: usize,
) -> Result<()> {
    let queue = Mutex::new(pending);
    std::thread::scope(|scope| -> Result<()> {
        let mut workers = Vec::new();
        for _ in 0..jobs {
            workers.push(scope.spawn(|| -> Result<()> {
                loop {
                    let job = queue.lock().map_err(|_| "poisoned job queue")?.pop();
                    match job {
                        Some(p) => compile(cache, &p, env)?,
                        None => return Ok(()),
                    }
                }
            }));
        }
        for worker in workers {
            worker.join().map_err(|_| "Lean worker panicked")??;
        }
        Ok(())
    })?;
    Ok(())
}

pub fn certify(args: &Args) -> Result<()> {
    let formal = args.required_path("--formal")?.canonicalize()?;
    let requested = args
        .path("--cache")?
        .unwrap_or_else(|| PathBuf::from(cache::DEFAULT_CACHE));
    let cache = cache::private_path(&requested)?;
    fs::create_dir_all(&cache)?;
    let jobs: usize = args.one("--jobs")?.unwrap_or("2").parse()?;
    require(jobs > 0, "jobs must be positive")?;
    for row in profiles::manifest()? {
        profiles::check_hahn(&row)?;
    }
    let files = cache::sources(&formal)?;
    let reuse = args.path("--reuse-checked-cache")?;
    let (hashes, ready) = stage_modules(&cache, &files, reuse.as_deref())?;
    let gero = environment(&cache, &formal)?;
    for file in [
        "RuntimeHahn/HahnPolynomial.lean",
        "RuntimeHahn/Budget.lean",
        "RuntimeHahn/Packing.lean",
    ] {
        compile(&cache, Path::new(file), &gero)?;
    }
    let pending: Vec<_> = files
        .keys()
        .filter(|p| {
            p.file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with("Degree")
                && !ready.contains(p.to_str().unwrap())
        })
        .cloned()
        .collect();
    compile_leaves(&cache, &gero, pending, jobs)?;
    for file in files.keys().filter(|p| {
        p.file_name()
            .unwrap()
            .to_string_lossy()
            .starts_with("Kernels")
    }) {
        compile(&cache, file, &gero)?;
    }
    for name in ["Hash", "Signature"] {
        compile(
            &cache,
            Path::new(&format!("RuntimeHahn/{name}.lean")),
            &gero,
        )?;
    }
    compile(&cache, Path::new("PolygeroRustHahn.lean"), &gero)?;
    let status = "Lean checked: two packing bounds, the concrete FS bridge and axiom audits";
    cache::write_json(
        &cache.join("build-state.json"),
        &json!({"status":status,"source_sha256":hashes,"manifest_sha256":cache::digest(&root().join("tools/parameters/hahn/profiles.json"))?}),
    )?;
    println!("{status}");
    Ok(())
}

fn choices(p: Profile) -> BTreeSet<(usize, usize)> {
    let Profile { k, s, n, t } = p;
    BTreeSet::from([
        (n, k + 2 * s + 1),
        (usize::max(k + 2 * s + 1, 2 * k + s) - 1, t),
        (k + 2 * s - 1, t),
        (n, t),
    ])
}
/// Emit arithmetic instances for the independent Polygero Lean bridge.
fn numeric_source(
    protocol: Protocol,
    audit: &Audit,
    selected: &[Profile],
    project: &Path,
) -> Result<String> {
    use std::fmt::Write;
    let namespace = protocol.namespace();
    let bridge = format!("{namespace}RustHahn");
    let mut body = format!(
        "import {bridge}\n{}\nnamespace {namespace}.RustProfiles\n",
        fs::read_to_string(
            project.join(format!("parameters/{}/TunedProfiles.lean", protocol.name()))
        )?
    );
    let mut facts = BTreeSet::new();
    for &p in selected {
        if !audit.hahn.contains_key(&p) {
            facts.extend(choices(p));
        }
    }
    for &(n, r) in &facts {
        writeln!(&mut body,"private theorem choose_{n}_{r} : Nat.choose {n} {r} = {} := by\n  norm_num [Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial]",choose(n,r))?;
    }
    for &p in selected {
        let Profile { k, s, n, t } = p;
        let label = p.label();
        if let Some(row) = audit.hahn.get(&p) {
            let name = row["name"].as_str().ok_or("missing manifest name")?;
            writeln!(&mut body,"def profile_{label} : {namespace}.RustHahnProfiles.Profile {n} {k} {s} {t} .universal := {namespace}.RustHahnProfiles.{name}.profile")?;
        } else {
            let names = choices(p)
                .iter()
                .map(|(a, b)| format!("choose_{a}_{b}"))
                .collect::<Vec<_>>()
                .join(", ");
            writeln!(&mut body,"theorem profile_{label} : Profile {n} {k} {s} {t} := by\n  constructor <;> norm_num [theta, {names}]")?;
        }
    }
    writeln!(
        &mut body,
        "end {namespace}.RustProfiles\nopen Lean Elab Command\nrun_cmd do"
    )?;
    let names = selected
        .iter()
        .map(|p| format!("``{namespace}.RustProfiles.profile_{}", p.label()))
        .collect::<Vec<_>>()
        .join(",");
    writeln!(&mut body,"  for endpoint in #[{names}] do\n    for ax in ← collectAxioms endpoint do\n      unless #[``propext,``Classical.choice,``Quot.sound].contains ax do\n        throwError \"Unexpected axiom in numeric verifier endpoint {{endpoint}}: {{ax}}\"")?;
    Ok(body)
}
pub fn check_profiles(
    protocol: Protocol,
    audit: &Audit,
    project: &Path,
    args: &Args,
) -> Result<()> {
    let selected = if args.all("--profile").is_empty() {
        audit.profiles.clone()
    } else {
        args.all("--profile")
            .iter()
            .map(|p| {
                let v: Vec<usize> = p
                    .split(',')
                    .map(str::parse)
                    .collect::<std::result::Result<_, _>>()?;
                require(v.len() == 4, "profile must be k,s,n,t")?;
                Ok(Profile {
                    k: v[0],
                    s: v[1],
                    n: v[2],
                    t: v[3],
                })
            })
            .collect::<Result<Vec<_>>>()?
    };
    require(
        !selected.is_empty() && selected.iter().all(|p| audit.profiles.contains(p)),
        "selected profile is not in catalog",
    )?;
    let cache = args
        .path("--hahn-cache")?
        .unwrap_or_else(|| PathBuf::from(cache::DEFAULT_CACHE));
    let project_root = project.canonicalize()?;
    let env = cache::environment(&cache, protocol, &project_root)?;
    let temp = cache::TempDir::new("rust-profiles")?;
    let proof = temp.path.join("Profiles.lean");
    fs::write(
        &proof,
        numeric_source(protocol, audit, &selected, &project_root)?,
    )?;
    let status = Command::new("lean")
        .args(["-j2", "-DwarningAsError=true"])
        .arg(proof)
        .envs(env)
        .status()?;
    require(status.success(), "Lean rejected numerical profiles")?;
    println!("{} numeric records and the concrete FS endpoint checked by Lean; foundational axiom audit passed.",selected.len());
    Ok(())
}
