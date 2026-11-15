// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
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
    write_json(&f.dir.path.join("build-state.json"),&json!({"status":"Lean checked: fixture","source_sha256":{"Proof.lean":digest(&f.source).unwrap()},"manifest_sha256":digest(&root().join("src/bin/zk_tool/parameters/hahn/profiles.json")).unwrap()})).unwrap();
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
    let inventory = sources(&project.path).unwrap();
    assert_eq!(inventory[Path::new("RuntimeHahn/Packing.lean")], packing);
    assert_eq!(inventory[Path::new("PolygeroRustHahn.lean")], bridge);
    assert!(inventory.contains_key(Path::new("MdocJointProfile.lean")));
    assert!(inventory.contains_key(Path::new("LfzkV2/Current/Parameters/Rate7.lean")));
    assert!(inventory
        .values()
        .all(|path| path.starts_with(&project.path)));
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
