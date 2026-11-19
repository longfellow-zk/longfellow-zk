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
//!
//! The certificate modules are ordinary targets of the formal project: `lake
//! build` checks them, and the generated numeric files import them through
//! `lake env`.
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{Duration, Instant},
};

use longfellow_zk::{mdoc::v2::MDOC_JOINT_PROFILE, runtime::v2::proto::polygero::PolygeroConfig};

use crate::{
    exact::choose,
    profiles::{self, Audit, Protocol},
    require, Args, Result,
};

/// The lake targets the numeric checks import: the universal Hahn
/// certificates, the Polygero bridge and mdoc joint profile, and the rate-7
/// certificate behind the joint profile.
const CERTIFICATE_TARGETS: &[&str] = &[
    "RuntimeHahn",
    "RustPolygeroProfiles",
    "+LfzkV2.Current.ParameterBounds",
    "+LfzkV2.Current.CertifiedProfile",
    "+LfzkV2.Current.Parameters.Rate7",
    "+LfzkV2.Current.Parameters.Rate7.Active",
    "+LfzkV2.Current.Parameters.Rate7.Binary",
    "+LfzkV2.Current.Parameters.Rate7.Prime",
];

type Environment = BTreeMap<String, String>;

/// The project's toolchain, pinned for every `lake` and `lean` this tool runs.
fn toolchain(project: &Path) -> Result<String> {
    Ok(fs::read_to_string(project.join("lean-toolchain"))?
        .trim()
        .to_owned())
}

/// Build the certificate targets with `lake build`; Lean checks each module
/// with the project's options, and up-to-date modules are not rebuilt.
fn build_certificates(project: &Path) -> Result<()> {
    let status = Command::new("lake")
        .arg("-d")
        .arg(project)
        .arg("build")
        .args(CERTIFICATE_TARGETS)
        .env("ELAN_TOOLCHAIN", toolchain(project)?)
        .status()?;
    require(status.success(), "lake build of the certificates failed")
}

/// The `lake env` search path of the project, so that a generated file
/// imports the modules `lake build` checked.
fn library_environment(project: &Path) -> Result<Environment> {
    let toolchain = toolchain(project)?;
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

fn run_lean(mut command: Command, description: &str) -> Result<std::process::ExitStatus> {
    let mut process = command.spawn()?;
    let started = Instant::now();
    loop {
        if let Some(status) = process.try_wait()? {
            return Ok(status);
        }
        if started.elapsed() > Duration::from_secs(60) {
            process.kill()?;
            process.wait()?;
            return Err(format!("Lean exceeded 60 seconds for {description}").into());
        }
        std::thread::sleep(Duration::from_millis(50));
    }
}

/// Elaborate a generated file against the project's environment, with the
/// options the certificate libraries use.
fn check_generated(file: &Path, env: &Environment, description: &str) -> Result<()> {
    let mut command = Command::new("lean");
    command
        .args([
            "-j2",
            "-M4096",
            "-DwarningAsError=true",
            "-DautoImplicit=false",
            "-DrelaxedAutoImplicit=false",
        ])
        .arg(file)
        .envs(env);
    let status = run_lean(command, description)?;
    require(status.success(), format!("Lean rejected {description}"))
}

/// A directory of generated Lean files, removed when dropped.
struct TempDir {
    path: PathBuf,
}
impl TempDir {
    /// Create `<temp>/<prefix>-<pid>-<n>` for the first `n` whose directory
    /// does not exist yet. `create_dir` is atomic, so two directories alive at
    /// once, in this process or another, never share a path.
    fn new(prefix: &str) -> Result<Self> {
        for attempt in 0..100 {
            let path =
                std::env::temp_dir().join(format!("{prefix}-{}-{attempt}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Ok(Self { path }),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(e.into()),
            }
        }
        Err("could not create a private temporary directory".into())
    }
}
impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

pub(crate) fn certify(args: &Args) -> Result<()> {
    let formal = args.required_path("--formal")?.canonicalize()?;
    for row in profiles::manifest()? {
        profiles::check_hahn(&row)?;
    }
    profiles::check_joint(&profiles::joint_manifest()?)?;
    build_certificates(&formal)?;
    let env = library_environment(&formal)?;
    let production = profiles::audit(Protocol::Polygero)?;
    let temp = TempDir::new("mdoc-joint-catalog")?;
    let catalog = temp.path.join("MdocJointCatalog.lean");
    fs::write(
        &catalog,
        numeric_source(
            Protocol::Polygero,
            &production,
            &[MDOC_JOINT_PROFILE],
            &formal,
        )?,
    )?;
    check_generated(&catalog, &env, "MdocJointCatalog.lean")?;
    println!("Lean checked: universal packing bounds, production joint mdoc certificate, concrete FS bridge and axiom audits");
    Ok(())
}

fn choices(p: PolygeroConfig) -> BTreeSet<(usize, usize)> {
    let PolygeroConfig { k, s, n, t } = p;
    BTreeSet::from([
        (n, k + 2 * s + 1),
        (usize::max(k + 2 * s + 1, 2 * k + s) - 1, t),
        (k + 2 * s - 1, t),
        (n, t),
    ])
}
/// Profiles checked per Lean process; see `check_profiles`.
const PROFILES_PER_LEAN_RUN: usize = 16;

/// Emit arithmetic instances for the independent Polygero Lean bridge.
fn numeric_source(
    protocol: Protocol,
    audit: &Audit,
    selected: &[PolygeroConfig],
    project: &Path,
) -> Result<String> {
    use std::fmt::Write;
    let namespace = protocol.namespace();
    let bridge = format!("{namespace}RustHahn");
    let mut body = format!(
        "import {bridge}\nimport MdocJointProfile\n{}\nnamespace {namespace}.RustProfiles\n",
        fs::read_to_string(
            project.join(format!("parameters/{}/TunedProfiles.lean", protocol.name()))
        )?
    );
    let mut facts = BTreeSet::new();
    for &p in selected {
        if !audit.hahn.contains_key(&p) && p != MDOC_JOINT_PROFILE {
            facts.extend(choices(p));
        }
    }
    // The kernel evaluates `fast_choose` directly; unfolding `descFactorial`
    // and `factorial` with `norm_num` exceeds simp's recursion depth once the
    // lower index reaches a few hundred.
    for &(n, r) in &facts {
        writeln!(&mut body,"private theorem choose_{n}_{r} : Nat.choose {n} {r} = {} := by\n  rw [Nat.choose_eq_fast_choose]; decide +kernel",choose(n,r))?;
    }
    for &p in selected {
        let PolygeroConfig { k, s, n, t } = p;
        let label = profiles::label(p);
        if p == MDOC_JOINT_PROFILE {
            writeln!(
                &mut body,
                "def profile_{label} : LfzkV2.Current.CertifiedProfile := MdocJointProfile.profile"
            )?;
            for (field, value) in [("k", p.k), ("s", p.s), ("n", p.n), ("t", p.t)] {
                writeln!(
                    &mut body,
                    "example : profile_{label}.{field} = {value} := by decide +kernel"
                )?;
            }
            for (key, field) in [
                ("active_cutoff", "activeCutoff"),
                ("active_list", "activeList"),
                ("binary_cutoff", "binaryCutoff"),
                ("binary_list", "binaryList"),
                ("prime_cutoff", "primeCutoff"),
                ("prime_list", "primeList"),
            ] {
                let value = profiles::integer(&audit.joint[key])?;
                writeln!(
                    &mut body,
                    "example : profile_{label}.{field} = {value} := by decide +kernel"
                )?;
            }
        } else if let Some(row) = audit.hahn.get(&p) {
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
        .map(|p| format!("``{namespace}.RustProfiles.profile_{}", profiles::label(*p)))
        .collect::<Vec<_>>()
        .join(",");
    writeln!(&mut body,"  for endpoint in #[{names}] do\n    for ax in ← collectAxioms endpoint do\n      unless #[``propext,``Classical.choice,``Quot.sound].contains ax do\n        throwError \"Unexpected axiom in numeric verifier endpoint {{endpoint}}: {{ax}}\"")?;
    Ok(body)
}
pub(crate) fn check_profiles(
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
                Ok(PolygeroConfig {
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
    let project_root = project.canonicalize()?;
    build_certificates(&project_root)?;
    let env = library_environment(&project_root)?;
    let temp = TempDir::new("rust-profiles")?;
    // Importing the certificate environment takes about 2.6 GiB, and each
    // profile adds about 25 MiB, so the full catalog in one file sat at the
    // 4 GiB limit and failed intermittently. Bounded chunks keep every Lean
    // process well below the limit.
    for (i, chunk) in selected.chunks(PROFILES_PER_LEAN_RUN).enumerate() {
        let proof = temp.path.join(format!("Profiles{i}.lean"));
        fs::write(
            &proof,
            numeric_source(protocol, audit, chunk, &project_root)?,
        )?;
        check_generated(&proof, &env, "the numerical profiles")?;
    }
    println!(
        "{} parameter records checked by Lean; foundational axiom audit passed.",
        selected.len()
    );
    Ok(())
}
