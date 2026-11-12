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

//! Private certificate caches, source-bound reuse, and Lean environments.
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
};

#[cfg(test)]
use serde_json::json;
use serde_json::Value;
use sha2::{Digest, Sha256};

use crate::{require, root, Result};

pub(crate) const DEFAULT_CACHE: &str = "/tmp/runtime-hahn-cache";
pub(crate) fn digest(path: &Path) -> Result<String> {
    Ok(format!("{:x}", Sha256::digest(fs::read(path)?)))
}
/// Locate certificate modules in the formal project selected by the caller.
/// Module names stay stable so a source-identical checked cache remains usable.
pub(crate) fn sources(project: &Path) -> Result<BTreeMap<PathBuf, PathBuf>> {
    fn collect(base: &Path, dir: &Path, out: &mut BTreeMap<PathBuf, PathBuf>) -> Result<()> {
        for entry in fs::read_dir(dir)? {
            let p = entry?.path();
            if p.is_dir() {
                collect(base, &p, out)?;
            } else if p.extension().is_some_and(|x| x == "lean") {
                out.insert(p.strip_prefix(base)?.to_owned(), p);
            }
        }
        Ok(())
    }
    let base = project.join("parameters/hahn");
    let mut out = BTreeMap::new();
    collect(&base, &base, &mut out)?;
    out.insert(
        "PolygeroRustHahn.lean".into(),
        project.join("parameters/polygero/PolygeroRustHahn.lean"),
    );
    Ok(out)
}
pub(crate) fn read_json(path: &Path) -> Result<Value> {
    Ok(serde_json::from_slice(&fs::read(path)?)?)
}
pub(crate) fn write_json(path: &Path, value: &Value) -> Result<()> {
    let tmp = path.with_extension("json.pending");
    fs::write(&tmp, serde_json::to_vec_pretty(value)?)?;
    fs::rename(tmp, path)?;
    Ok(())
}
fn linked(path: &Path) -> bool {
    fs::symlink_metadata(path).is_ok_and(|m| m.file_type().is_symlink())
}
#[cfg(unix)]
fn link(source: &Path, target: &Path) -> Result<()> {
    Ok(std::os::unix::fs::symlink(source, target)?)
}
#[cfg(not(unix))]
fn link(source: &Path, target: &Path) -> Result<()> {
    if source.is_dir() {
        return Err("directory cache overlays require symlink support".into());
    }
    fs::copy(source, target)?;
    Ok(())
}

/// Make each output directory local before adding a module below a dependency overlay.
fn owned_parent(root: &Path, parent: &Path) -> Result<()> {
    let relative = parent.strip_prefix(root)?;
    require(
        relative
            .components()
            .all(|c| matches!(c, std::path::Component::Normal(_))),
        "invalid module output path",
    )?;
    fn materialize(path: &Path) -> Result<()> {
        if linked(path) {
            let dependency = path.canonicalize()?;
            fs::remove_file(path)?;
            fs::create_dir(path)?;
            overlay(&dependency, path)?;
        } else {
            fs::create_dir_all(path)?;
        }
        Ok(())
    }
    materialize(root)?;
    let mut current = root.to_owned();
    for component in relative.components() {
        current.push(component.as_os_str());
        materialize(&current)?;
    }
    Ok(())
}

/// Replace stale objects only with trusted objects accompanied by identical source.
pub(crate) fn stage(
    source: &Path,
    target: &Path,
    module_root: &Path,
    previous: Option<&str>,
    reuse: Option<&Path>,
) -> Result<(String, bool)> {
    owned_parent(module_root, target.parent().ok_or("missing target parent")?)?;
    let bytes = fs::read(source)?;
    let hash = digest(source)?;
    let object = target.with_extension("olean");
    let mut ready = previous == Some(hash.as_str()) && object.is_file();
    if !ready {
        if let Some(candidate) = reuse {
            let candidate_object = candidate.with_extension("olean");
            if candidate.is_file() && fs::read(candidate)? == bytes && candidate_object.is_file() {
                let object_location = fs::canonicalize(&object).unwrap_or(
                    target
                        .parent()
                        .unwrap()
                        .canonicalize()?
                        .join(object.file_name().unwrap()),
                );
                if candidate_object.canonicalize()? != object_location {
                    if object.exists() || linked(&object) {
                        fs::remove_file(&object)?;
                    }
                    link(&candidate_object.canonicalize()?, &object)?;
                    ready = true;
                }
            }
        }
    }
    if !target.is_file() || fs::read(target)? != bytes {
        if linked(target) {
            fs::remove_file(target)?;
        }
        fs::write(target, bytes)?;
    }
    Ok((hash, ready))
}
/// Overlay dependencies without replacing locally staged modules or writing through links.
pub(crate) fn overlay(source: &Path, target: &Path) -> Result<()> {
    fs::create_dir_all(target)?;
    for entry_result in fs::read_dir(source)? {
        let entry = entry_result?;
        let p = entry.path();
        let destination = target.join(entry.file_name());
        if matches!(
            p.extension().and_then(|s| s.to_str()),
            Some("olean" | "ilean")
        ) && destination.with_extension("lean").exists()
        {
            continue;
        }
        if destination.exists() || linked(&destination) {
            if p.is_dir() && destination.is_dir() && !linked(&destination) {
                overlay(&p, &destination)?;
            }
        } else {
            link(&p.canonicalize()?, &destination)?;
        }
    }
    Ok(())
}

pub(crate) fn environment(
    cache: &Path,
    protocol: crate::profiles::Protocol,
    project: &Path,
) -> Result<BTreeMap<String, String>> {
    validated_environment(cache, protocol, project, &sources(project)?)
}
fn validated_environment(
    cache: &Path,
    protocol: crate::profiles::Protocol,
    project: &Path,
    inventory: &BTreeMap<PathBuf, PathBuf>,
) -> Result<BTreeMap<String, String>> {
    let state = read_json(&cache.join("build-state.json"))?;
    require(
        state["status"]
            .as_str()
            .is_some_and(|s| s.starts_with("Lean checked:")),
        "certificate cache is not checked; run certify-hahn",
    )?;
    let hashes = state["source_sha256"]
        .as_object()
        .ok_or("missing source inventory")?;
    require(
        inventory.len() == hashes.len()
            && inventory
                .keys()
                .all(|p| hashes.contains_key(&p.to_string_lossy().into_owned())),
        "certificate source inventory changed; run certify-hahn",
    )?;
    require(
        state["manifest_sha256"] == digest(&root().join("tools/parameters/hahn/profiles.json"))?,
        "manifest changed; run certify-hahn",
    )?;
    for (relative, source) in inventory {
        let expected = &hashes[&relative.to_string_lossy().into_owned()];
        let staged = cache.join("modules").join(relative);
        require(
            *expected == digest(source)?,
            "proof source changed; run certify-hahn",
        )?;
        require(
            staged.is_file()
                && *expected == digest(&staged)?
                && staged.with_extension("olean").is_file(),
            "incomplete certificate cache",
        )?;
    }
    let name = match protocol {
        crate::profiles::Protocol::Polygero => "environment.json",
    };
    let env = read_json(&cache.join(name))?;
    let values = env.as_object().ok_or("invalid environment")?;
    let out: BTreeMap<_, _> = values
        .iter()
        .map(|(k, v)| {
            Ok((
                k.clone(),
                v.as_str().ok_or("invalid environment value")?.to_owned(),
            ))
        })
        .collect::<Result<_>>()?;
    require(
        out.get("ELAN_TOOLCHAIN").map(String::as_str)
            == Some(fs::read_to_string(project.join("lean-toolchain"))?.trim()),
        "Lean toolchain mismatch",
    )?;
    let expected = project.join(".lake/build/lib/lean").canonicalize()?;
    require(
        std::env::split_paths(out.get("LEAN_PATH").ok_or("missing LEAN_PATH")?).any(|p| {
            p.canonicalize()
                .is_ok_and(|canonical| canonical == expected)
        }),
        "Lean project path mismatch",
    )?;
    Ok(out)
}

/// Resolve a proposed cache location without creating any directory first.
pub(crate) fn private_path(requested: &Path) -> Result<PathBuf> {
    use std::path::Component;
    let absolute = std::path::absolute(requested)?;
    let mut resolved = PathBuf::new();
    for component in absolute.components() {
        match component {
            Component::ParentDir => {
                resolved.pop();
            }
            Component::CurDir => {}
            other => {
                resolved.push(other.as_os_str());
                if fs::symlink_metadata(&resolved).is_ok() {
                    resolved = resolved.canonicalize()?;
                }
            }
        }
    }
    let temp = std::env::temp_dir().canonicalize()?;
    require(
        resolved.starts_with(&temp) && resolved != temp,
        "cache must be private under the temporary directory",
    )?;
    Ok(resolved)
}

pub(crate) struct TempDir {
    pub path: PathBuf,
}
impl TempDir {
    pub(crate) fn new(prefix: &str) -> Result<Self> {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        for _ in 0..100 {
            let path = std::env::temp_dir().join(format!(
                "{prefix}-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
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

#[cfg(test)]
mod tests {
    use super::*;
    struct Fixture {
        dir: TempDir,
        source: PathBuf,
        target: PathBuf,
        candidate: PathBuf,
    }
    impl Fixture {
        fn new() -> Self {
            let dir = TempDir::new("hahn-test").unwrap();
            let source = dir.path.join("source.lean");
            let target = dir.path.join("modules/Proof.lean");
            let candidate = dir.path.join("reuse/Proof.lean");
            fs::write(&source, "theorem current : True := trivial\n").unwrap();
            fs::create_dir_all(target.parent().unwrap()).unwrap();
            fs::create_dir_all(candidate.parent().unwrap()).unwrap();
            Self {
                dir,
                source,
                target,
                candidate,
            }
        }
    }
    #[test]
    fn matching_previous_source_reuses_object() {
        let f = Fixture::new();
        fs::write(f.target.with_extension("olean"), b"checked").unwrap();
        assert!(
            stage(
                &f.source,
                &f.target,
                f.target.parent().unwrap(),
                Some(&digest(&f.source).unwrap()),
                None
            )
            .unwrap()
            .1
        );
    }
    #[test]
    fn missing_object_requires_recheck() {
        let f = Fixture::new();
        assert!(
            !stage(
                &f.source,
                &f.target,
                f.target.parent().unwrap(),
                Some(&digest(&f.source).unwrap()),
                None
            )
            .unwrap()
            .1
        );
    }
    #[test]
    fn candidate_replaces_stale_object() {
        let f = Fixture::new();
        fs::write(f.target.with_extension("olean"), b"stale").unwrap();
        fs::copy(&f.source, &f.candidate).unwrap();
        fs::write(f.candidate.with_extension("olean"), b"checked").unwrap();
        assert!(
            stage(
                &f.source,
                &f.target,
                f.target.parent().unwrap(),
                None,
                Some(&f.candidate)
            )
            .unwrap()
            .1
        );
        assert_eq!(
            fs::read(f.target.with_extension("olean")).unwrap(),
            b"checked"
        );
    }
    #[test]
    fn different_candidate_source_rejects() {
        let f = Fixture::new();
        fs::write(&f.candidate, b"old").unwrap();
        fs::write(f.candidate.with_extension("olean"), b"old object").unwrap();
        assert!(
            !stage(
                &f.source,
                &f.target,
                f.target.parent().unwrap(),
                None,
                Some(&f.candidate)
            )
            .unwrap()
            .1
        );
    }
    #[test]
    fn target_cannot_reuse_itself() {
        let f = Fixture::new();
        fs::copy(&f.source, &f.target).unwrap();
        fs::write(f.target.with_extension("olean"), b"unchecked").unwrap();
        assert!(
            !stage(
                &f.source,
                &f.target,
                f.target.parent().unwrap(),
                None,
                Some(&f.target)
            )
            .unwrap()
            .1
        );
    }
    fn certificate_fixture(f: &Fixture) -> (BTreeMap<PathBuf, PathBuf>, PathBuf) {
        stage(&f.source, &f.target, f.target.parent().unwrap(), None, None).unwrap();
        fs::write(f.target.with_extension("olean"), b"checked").unwrap();
        let project = f.dir.path.join("project");
        fs::create_dir_all(project.join(".lake/build/lib/lean")).unwrap();
        fs::write(project.join("lean-toolchain"), "fixture-toolchain").unwrap();
        let env = json!({"ELAN_TOOLCHAIN":"fixture-toolchain","LEAN_PATH":project.join(".lake/build/lib/lean").to_str().unwrap()});
        write_json(&f.dir.path.join("environment.json"), &env).unwrap();
        write_json(&f.dir.path.join("build-state.json"),&json!({"status":"Lean checked: fixture","source_sha256":{"Proof.lean":digest(&f.source).unwrap()},"manifest_sha256":digest(&root().join("tools/parameters/hahn/profiles.json")).unwrap()})).unwrap();
        (
            BTreeMap::from([(PathBuf::from("Proof.lean"), f.source.clone())]),
            project,
        )
    }
    #[test]
    fn complete_cache_is_accepted() {
        let f = Fixture::new();
        let (inventory, project) = certificate_fixture(&f);
        validated_environment(
            &f.dir.path,
            crate::profiles::Protocol::Polygero,
            &project,
            &inventory,
        )
        .unwrap();
    }
    #[test]
    fn changed_staged_source_rejects() {
        let f = Fixture::new();
        let (inventory, project) = certificate_fixture(&f);
        fs::write(&f.target, b"changed").unwrap();
        assert!(validated_environment(
            &f.dir.path,
            crate::profiles::Protocol::Polygero,
            &project,
            &inventory
        )
        .unwrap_err()
        .to_string()
        .contains("incomplete"));
    }
    #[test]
    fn missing_checked_object_rejects() {
        let f = Fixture::new();
        let (inventory, project) = certificate_fixture(&f);
        fs::remove_file(f.target.with_extension("olean")).unwrap();
        assert!(validated_environment(
            &f.dir.path,
            crate::profiles::Protocol::Polygero,
            &project,
            &inventory
        )
        .is_err());
    }
    #[test]
    fn changed_source_rejects() {
        let f = Fixture::new();
        let (inventory, project) = certificate_fixture(&f);
        fs::write(&f.source, b"changed").unwrap();
        assert!(validated_environment(
            &f.dir.path,
            crate::profiles::Protocol::Polygero,
            &project,
            &inventory
        )
        .is_err());
    }
    #[test]
    fn escaping_cache_path_is_rejected_before_writes() {
        let temporary = TempDir::new("hahn-path").unwrap();
        let missing = temporary.path.join("never-created");
        let proposed = missing
            .join("..")
            .join("..")
            .join("..")
            .join("escaped-hahn-cache");
        assert!(private_path(&proposed).is_err());
        assert!(!missing.exists());
    }
    #[cfg(unix)]
    #[test]
    fn staging_detaches_dependency_directories_before_writing() {
        let f = Fixture::new();
        let modules = f.target.parent().unwrap();
        let external = f.dir.path.join("external-library");
        fs::create_dir(&external).unwrap();
        fs::write(external.join("Existing.lean"), b"external source").unwrap();
        let directory = modules.join("Dependency");
        link(&external, &directory).unwrap();
        let target = directory.join("New.lean");
        stage(&f.source, &target, modules, None, None).unwrap();
        assert!(!external.join("New.lean").exists());
        assert_eq!(fs::read(&target).unwrap(), fs::read(&f.source).unwrap());
        assert_eq!(
            fs::read(directory.join("Existing.lean")).unwrap(),
            b"external source"
        );
        assert!(!linked(&directory));
    }
    #[test]
    fn inventory_uses_requested_formal_project() {
        let project = TempDir::new("hahn-formal-project").unwrap();
        let packing = project
            .path
            .join("parameters/hahn/RuntimeHahn/Packing.lean");
        let bridge = project
            .path
            .join("parameters/polygero/PolygeroRustHahn.lean");
        for path in [&packing, &bridge] {
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, "theorem fixture : True := trivial\n").unwrap();
        }
        assert_eq!(
            sources(&project.path).unwrap(),
            BTreeMap::from([
                (PathBuf::from("RuntimeHahn/Packing.lean"), packing),
                (PathBuf::from("PolygeroRustHahn.lean"), bridge),
            ])
        );
        assert!(sources(&project.path.join("missing")).is_err());
    }
    #[test]
    fn incomplete_inventory_rejects() {
        let f = Fixture::new();
        let (inventory, project) = certificate_fixture(&f);
        write_json(
            &f.dir.path.join("build-state.json"),
            &json!({"status":"Lean checked: fixture","source_sha256":{}}),
        )
        .unwrap();
        assert!(validated_environment(
            &f.dir.path,
            crate::profiles::Protocol::Polygero,
            &project,
            &inventory
        )
        .unwrap_err()
        .to_string()
        .contains("inventory"));
    }
    #[test]
    fn unchecked_build_rejects() {
        let f = Fixture::new();
        let (inventory, project) = certificate_fixture(&f);
        write_json(
            &f.dir.path.join("build-state.json"),
            &json!({"status":"building"}),
        )
        .unwrap();
        assert!(validated_environment(
            &f.dir.path,
            crate::profiles::Protocol::Polygero,
            &project,
            &inventory
        )
        .is_err());
    }
}
