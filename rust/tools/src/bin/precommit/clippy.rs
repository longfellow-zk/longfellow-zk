// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Clippy warning counts per target, and their comparison with a baseline.
use std::{collections::BTreeMap, fmt};

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
