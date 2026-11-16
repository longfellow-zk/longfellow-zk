// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The options and the context every step runs in.
use std::{
    ffi::OsStr,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

use crate::clippy::Counts;

/// The command line.
#[derive(Default)]
pub(crate) struct Options {
    pub(crate) keep_going: bool,
    pub(crate) fmt_check: bool,
    pub(crate) base: Option<String>,
    pub(crate) clippy_counts: Option<Counts>,
    pub(crate) cross: Option<bool>,
    pub(crate) formal: bool,
    pub(crate) only: Option<Vec<String>>,
    pub(crate) skip: Vec<String>,
    pub(crate) list: bool,
}

/// What every step needs: where things are, and the options.
pub(crate) struct Context {
    /// The repository root.
    pub(crate) root: PathBuf,
    /// `root/rust`, the crate.
    pub(crate) rust: PathBuf,
    /// The crate's cargo target directory.
    pub(crate) target: PathBuf,
    /// `target/precommit`: logs and the auxiliary target directories.
    pub(crate) work: PathBuf,
    pub(crate) options: Options,
    /// The base commit, or why there is none.
    base: Result<String, String>,
}

impl Context {
    pub(crate) fn new(options: Options) -> Result<Self, String> {
        let output = Command::new("git")
            .args(["rev-parse", "--show-toplevel"])
            .output()
            .map_err(|e| format!("git: {e}"))?;
        if !output.status.success() {
            return Err("run the checks inside the repository".into());
        }
        let root = PathBuf::from(String::from_utf8_lossy(&output.stdout).trim());
        let rust = root.join("rust");
        if !rust.join("Cargo.toml").is_file() {
            return Err(format!("{} has no rust/Cargo.toml", root.display()));
        }
        let target = std::env::var_os("CARGO_TARGET_DIR")
            .map(PathBuf::from)
            .map(|t| if t.is_absolute() { t } else { rust.join(t) })
            .unwrap_or_else(|| rust.join("target"));
        let work = target.join("precommit");
        std::fs::create_dir_all(&work).map_err(|e| format!("{}: {e}", work.display()))?;
        let mut context = Self {
            root,
            rust,
            target,
            work,
            options,
            base: Err(String::new()),
        };
        context.base = context.resolve_base();
        Ok(context)
    }
}

impl Context {
    /// `program` in `directory`.
    pub(crate) fn command(&self, directory: &Path, program: impl AsRef<OsStr>) -> Command {
        let mut command = Command::new(program);
        command.current_dir(directory);
        command
    }

    /// Cargo in `rust/`, building into `target`.
    pub(crate) fn cargo_into(&self, target: &Path, args: &str) -> Command {
        let mut command = self.command(&self.rust, "cargo");
        command.env("CARGO_TARGET_DIR", target);
        command.args(args.split_whitespace());
        command
    }

    /// Cargo in `rust/`, building into the crate's target directory.
    pub(crate) fn cargo(&self, args: &str) -> Command {
        self.cargo_into(&self.target, args)
    }

    /// A git command at the repository root.
    pub(crate) fn git(&self, args: &[&str]) -> Command {
        let mut command = self.command(&self.root, "git");
        command.args(args);
        command
    }

    /// The text git prints, or `None` when it fails.
    pub(crate) fn git_text(&self, args: &[&str]) -> Option<String> {
        let output = self.git(args).stderr(Stdio::null()).output().ok()?;
        output
            .status
            .success()
            .then(|| String::from_utf8_lossy(&output.stdout).into_owned())
    }

    /// The commit the change is measured against: `--base`, or else `HEAD`
    /// when the working tree has changes and `HEAD^` when it has none. The
    /// runner resolves it once, before any step can change the tree.
    fn resolve_base(&self) -> Result<String, String> {
        let revision = match &self.options.base {
            Some(revision) => revision.clone(),
            None => {
                let status = self
                    .git_text(&["status", "--porcelain"])
                    .unwrap_or_default();
                if status.trim().is_empty() {
                    "HEAD^"
                } else {
                    "HEAD"
                }
                .to_owned()
            }
        };
        self.git_text(&["rev-parse", "--verify", &format!("{revision}^{{commit}}")])
            .map(|sha| sha.trim().to_owned())
            .ok_or(format!(
                "no base commit {revision}; pass --base or --clippy-counts"
            ))
    }

    pub(crate) fn base(&self) -> Result<String, String> {
        self.base.clone()
    }
}
