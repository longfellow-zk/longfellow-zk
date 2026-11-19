// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Clippy warning counts per target, and their comparison with a baseline.
use std::{
    collections::BTreeMap,
    fmt, fs,
    path::{Component, Path, PathBuf},
};

use sha2::{Digest, Sha256};

/// Warnings per cargo target, labeled as cargo labels them with the quotes
/// dropped and spaces turned into `-`, after a prefix naming the package
/// outside the library: `lib`, `lib-test`, `tools-bin-zk_tool`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Counts(pub(crate) BTreeMap<String, usize>);

impl Counts {
    /// The counts of `package`'s targets in clippy's output, from its lines
    /// ``warning: `longfellow-zk` (lib test) generated 15 warnings (9 duplicates)``,
    /// each label after `prefix`.
    pub(crate) fn of_output(output: &str, package: &str, prefix: &str) -> Self {
        let mut counts = BTreeMap::new();
        let start = format!("warning: `{package}` (");
        for line in output.lines() {
            let Some(rest) = line.strip_prefix(start.as_str()) else {
                continue;
            };
            let Some((label, generated)) = rest.split_once(") generated ") else {
                continue;
            };
            let number = generated.split(' ').next().unwrap_or("");
            if let Ok(n) = number.parse::<usize>() {
                counts.insert(
                    format!("{prefix}{}", label.replace('"', "").replace(' ', "-")),
                    n,
                );
            }
        }
        Self(counts)
    }

    /// Add `other`'s counts, which label other targets.
    pub(crate) fn add(&mut self, other: Self) {
        self.0.extend(other.0);
    }

    /// `label=N,...`, as [`Counts`] displays; `none` or an empty string has no
    /// warnings.
    pub(crate) fn parse(text: &str) -> Result<Self, String> {
        let mut counts = BTreeMap::new();
        if text.trim() == "none" {
            return Ok(Self(counts));
        }
        for item in text.split(',').map(str::trim).filter(|s| !s.is_empty()) {
            let (label, number) = item
                .split_once('=')
                .ok_or(format!("clippy count {item:?} is not LABEL=N"))?;
            let n = number
                .parse()
                .map_err(|_| format!("clippy count {item:?} is not LABEL=N"))?;
            counts.insert(label.to_owned(), n);
        }
        Ok(Self(counts))
    }

    /// Every target whose count exceeds its baseline count (zero for a
    /// target the baseline does not list), with both counts.
    pub(crate) fn increases(&self, baseline: &Self) -> Vec<(String, usize, usize)> {
        self.0
            .iter()
            .filter_map(|(label, &n)| {
                let before = baseline.0.get(label).copied().unwrap_or(0);
                (n > before).then(|| (label.clone(), before, n))
            })
            .collect()
    }
}

impl fmt::Display for Counts {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            return f.write_str("none");
        }
        let items: Vec<_> = self
            .0
            .iter()
            .map(|(label, n)| format!("{label}={n}"))
            .collect();
        f.write_str(&items.join(","))
    }
}

/// What a baseline was measured with: the base commit, the toolchain
/// (`rustc -vV` and `cargo clippy -V`), the lock file, the clippy command
/// lines with the flags the environment adds, and the contents of the clippy
/// configuration from outside the base commit. A saved baseline is reused
/// only under an equal key, so a new toolchain, new dependencies, new flags or
/// a changed configuration measure the baseline again.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BaselineKey(String);

impl BaselineKey {
    /// The key of `base`, measured with `rustc` and `clippy` (the versions
    /// the tools print), the lock file `lock`, the clippy runs `runs`, the
    /// environment's flags `flags` (`NAME=value`) and the contents of the
    /// clippy configuration `config` ([`config`]), `None` when there is none.
    pub(crate) fn new(
        base: &str,
        rustc: &str,
        clippy: &str,
        lock: &[u8],
        runs: &[&str],
        flags: &[String],
        config: Option<&[u8]>,
    ) -> Self {
        let mut key = format!("base {base}\n");
        for (tag, text) in [("rustc", rustc), ("clippy", clippy)] {
            for line in text.lines() {
                key.push_str(&format!("{tag} {line}\n"));
            }
        }
        key.push_str(&format!("lock {}\n", hex_digest(lock)));
        for run in runs {
            key.push_str(&format!("run {run}\n"));
        }
        for flag in flags {
            key.push_str(&format!("flag {flag:?}\n"));
        }
        match config {
            Some(contents) => key.push_str(&format!("config {}\n", hex_digest(contents))),
            None => key.push_str("config none\n"),
        }
        Self(key)
    }

    /// The saved file of `counts` measured under this key.
    pub(crate) fn save(&self, counts: &Counts) -> String {
        format!("{}counts {counts}\n", self.0)
    }

    /// The counts in `saved`, when they were measured under this key.
    pub(crate) fn saved(&self, saved: &str) -> Option<Counts> {
        let counts = saved.strip_prefix(&self.0)?.strip_prefix("counts ")?;
        Counts::parse(counts.trim()).ok()
    }
}

/// The SHA-256 digest of `bytes`, in hex.
fn hex_digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

/// The names of a clippy configuration file, in clippy's order of
/// preference within one directory.
const CONFIG_NAMES: [&str; 2] = [".clippy.toml", "clippy.toml"];

/// The contents of the clippy configuration that a clippy run searching from
/// `start` reads, or `None` when it finds none. Clippy searches from
/// `CLIPPY_CONF_DIR`, or else from the package's manifest directory, through
/// each parent in turn, and reads the first of [`CONFIG_NAMES`] that is a file
/// in the first directory that has one. This search passes over the
/// directories under `skip`, whose files the caller accounts for otherwise.
pub(crate) fn config(start: &Path, skip: &Path) -> Result<Option<Vec<u8>>, String> {
    let folded = start
        .components()
        .fold(PathBuf::new(), |mut path, component| {
            match component {
                Component::CurDir => {}
                Component::ParentDir => {
                    path.pop();
                }
                other => path.push(other),
            }
            path
        });
    let first = folded.canonicalize().unwrap_or(folded);
    for directory in first.ancestors().filter(|d| !d.starts_with(skip)) {
        for name in CONFIG_NAMES {
            let file = directory.join(name);
            if file.is_file() {
                return fs::read(&file)
                    .map(Some)
                    .map_err(|e| format!("{}: {e}", file.display()));
            }
        }
    }
    Ok(None)
}
