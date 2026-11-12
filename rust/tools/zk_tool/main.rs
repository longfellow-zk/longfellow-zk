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

//! Offline exact audits, Lean certification, and specification generation.
mod cache;
mod exact;
mod generate;
mod lean;
mod profiles;
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error + Send + Sync>>;
pub fn require(value: bool, message: impl Into<String>) -> Result<()> {
    if value {
        Ok(())
    } else {
        Err(message.into().into())
    }
}
pub fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

/// Small explicit CLI; no shell interpolation or additional parser dependency.
#[derive(Default)]
pub struct Args {
    values: BTreeMap<String, Vec<String>>,
}
impl Args {
    fn parse() -> Result<(String, Self)> {
        Self::from_iter(std::env::args().skip(1))
    }
    fn from_iter(mut iter: impl Iterator<Item = String>) -> Result<(String, Self)> {
        let command = iter
            .next()
            .ok_or("expected check-profiles, certify-hahn, or generate-v2-specs")?;
        if matches!(command.as_str(), "help" | "--help" | "-h") {
            return Ok(("help".into(), Self::default()));
        }
        let mut args = Self::default();
        while let Some(key) = iter.next() {
            if matches!(key.as_str(), "--help" | "-h") {
                return Ok(("help".into(), Self::default()));
            }
            require(key.starts_with("--"), format!("unexpected argument: {key}"))?;
            let value = iter
                .next()
                .ok_or_else(|| format!("missing value for {key}"))?;
            require(!value.starts_with("--"), format!("missing value for {key}"))?;
            args.values.entry(key).or_default().push(value);
        }
        Ok((command, args))
    }
    pub fn one(&self, key: &str) -> Result<Option<&str>> {
        match self.values.get(key) {
            None => Ok(None),
            Some(v) if v.len() == 1 => Ok(Some(&v[0])),
            _ => Err(format!("duplicate {key}").into()),
        }
    }
    pub fn path(&self, key: &str) -> Result<Option<PathBuf>> {
        Ok(self.one(key)?.map(PathBuf::from))
    }
    pub fn required_path(&self, key: &str) -> Result<PathBuf> {
        self.path(key)?
            .ok_or_else(|| format!("missing {key}").into())
    }
    pub fn all(&self, key: &str) -> &[String] {
        self.values.get(key).map(Vec::as_slice).unwrap_or(&[])
    }
    fn validate(&self, allowed: &[&str]) -> Result<()> {
        for key in self.values.keys() {
            require(
                allowed.contains(&key.as_str()),
                format!("unknown option {key}"),
            )?;
        }
        Ok(())
    }
}
fn run() -> Result<()> {
    let (command, args) = Args::parse()?;
    match command.as_str() {
        "help" => {
            println!("zk_tool commands:\n  check-profiles --protocol polygero [--check-lean PROJECT] [--hahn-cache CACHE] [--profile k,s,n,t]\n  certify-hahn --formal PROJECT [--cache CACHE] [--jobs N] [--reuse-checked-cache MODULES]\n  generate-v2-specs (requires compiler,mdoc features)");
            Ok(())
        }
        "check-profiles" => {
            args.validate(&["--protocol", "--check-lean", "--hahn-cache", "--profile"])?;
            let protocol =
                profiles::Protocol::parse(args.one("--protocol")?.ok_or("missing --protocol")?)?;
            let checked = profiles::audit(protocol)?;
            println!(
                "{} {} profiles: exact budgets passed; {} universal Hahn manifests and the joint mdoc budget.",
                checked.profiles.len(),
                protocol.name(),
                checked.hahn.len()
            );
            if let Some(project) = args.path("--check-lean")? {
                lean::check_profiles(protocol, &checked, &project, &args)?;
            }
            Ok(())
        }
        "certify-hahn" => {
            args.validate(&["--formal", "--cache", "--jobs", "--reuse-checked-cache"])?;
            lean::certify(&args)
        }
        "generate-v2-specs" => {
            args.validate(&[])?;
            generate::run()
        }
        _ => Err(format!("unknown command {command}").into()),
    }
}
fn main() {
    if let Err(error) = run() {
        eprintln!("zk_tool: {error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn parse(words: &[&str]) -> Result<(String, Args)> {
        Args::from_iter(words.iter().map(|s| (*s).to_owned()))
    }
    #[test]
    fn help_needs_no_external_tools() {
        assert_eq!(parse(&["--help"]).unwrap().0, "help");
    }
    #[test]
    fn missing_option_value_rejects() {
        assert!(parse(&["check-profiles", "--protocol"]).is_err());
    }
    #[test]
    fn duplicate_single_option_rejects() {
        let (_, args) = parse(&[
            "check-profiles",
            "--protocol",
            "polygero",
            "--protocol",
            "polygero",
        ])
        .unwrap();
        assert!(args.one("--protocol").is_err());
    }
    #[test]
    fn unknown_option_rejects() {
        let (_, args) = parse(&["check-profiles", "--typo", "1"]).unwrap();
        assert!(args.validate(&["--protocol"]).is_err());
    }
}
