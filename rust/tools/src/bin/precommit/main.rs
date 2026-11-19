// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The checks to run before every commit (AGENTS.md), in one command.
//!
//! ```sh
//! cargo run --release -p longfellow-zk-tools --bin precommit -- [options]
//! ```
//!
//! Run it from anywhere in the repository. It runs the steps below in order
//! and prints one line per step. It stops at the first failing step, or with
//! `--keep-going` runs them all; it exits nonzero when a step failed. Each
//! step's complete output is in `<target>/precommit/<step>.log`, where
//! `<target>` is `CARGO_TARGET_DIR`, or `rust/target`. Cargo's own
//! `CARGO_BUILD_JOBS` and the test harness's `RUST_TEST_THREADS` limit the
//! parallelism of every step.
//!
//! Options:
//! - `--keep-going`: run every step even after one fails.
//! - `--fmt-check`: check the formatting instead of rewriting it (for CI).
//! - `--base REV`: the commit the change is measured against, for the clippy counts and for
//!   deciding whether to run the cross builds. By default `HEAD` when the working tree has changes,
//!   and `HEAD^` when it has none.
//! - `--clippy-counts LABEL=N,...`: the baseline clippy warning counts per target (as the clippy
//!   step prints them), instead of measuring `--base`.
//! - `--cross` / `--no-cross`: always, or never, run the cross builds.
//! - `--formal`: also run the formal checks, which need Lean (`lake`).
//! - `--only STEP,...` / `--skip STEP,...`: run only, or skip, these steps.
//! - `--list`: print the steps and exit.
mod clippy;
mod context;
mod run;
mod steps;

use std::{process::ExitCode, time::Instant};

use clippy::Counts;
use context::{Context, Options};
use run::{Log, Outcome};

impl Options {
    fn parse(mut args: impl Iterator<Item = String>) -> Result<Self, String> {
        let mut options = Self::default();
        while let Some(arg) = args.next() {
            let mut value = || args.next().ok_or(format!("{arg} needs a value"));
            match arg.as_str() {
                "--keep-going" => options.keep_going = true,
                "--fmt-check" => options.fmt_check = true,
                "--base" => options.base = Some(value()?),
                "--clippy-counts" => options.clippy_counts = Some(Counts::parse(&value()?)?),
                "--cross" => options.cross = Some(true),
                "--no-cross" => options.cross = Some(false),
                "--formal" => options.formal = true,
                "--only" => options.only = Some(names(&value()?)?),
                "--skip" => options.skip = names(&value()?)?,
                "--list" => options.list = true,
                "-h" | "--help" => return Err(String::new()),
                _ => return Err(format!("unknown argument {arg}")),
            }
        }
        Ok(options)
    }

    /// Whether to run `step`, and if not, why.
    fn selects(&self, step: &steps::Step) -> Result<(), &'static str> {
        if self.skip.iter().any(|s| s == step.name) {
            return Err("skipped (--skip)");
        }
        match &self.only {
            Some(only) if only.iter().any(|s| s == step.name) => Ok(()),
            Some(_) => Err("skipped (--only)"),
            None if step.formal && !self.formal => Err("skipped (needs --formal)"),
            None => Ok(()),
        }
    }
}

/// A comma-separated list of step names, each of which must exist.
fn names(list: &str) -> Result<Vec<String>, String> {
    let all = steps::all();
    list.split(',')
        .map(|name| {
            if all.iter().any(|step| step.name == name) {
                Ok(name.to_owned())
            } else {
                Err(format!("no step {name:?}; --list prints the steps"))
            }
        })
        .collect()
}

fn usage() -> String {
    let mut text = String::from(
        "usage: precommit [--keep-going] [--fmt-check] [--base REV] [--clippy-counts LABEL=N,...]\n\
         \x20                [--cross | --no-cross] [--formal] [--only STEP,...] [--skip STEP,...] \
         [--list]\nsteps:\n",
    );
    for step in steps::all() {
        let formal = if step.formal { " (--formal)" } else { "" };
        text.push_str(&format!("  {:<15} {}{formal}\n", step.name, step.what));
    }
    text
}

fn main() -> ExitCode {
    let options = match Options::parse(std::env::args().skip(1)) {
        Ok(options) => options,
        Err(error) => {
            if !error.is_empty() {
                eprintln!("precommit: {error}");
            }
            eprint!("{}", usage());
            return ExitCode::from(2);
        }
    };
    if options.list {
        print!("{}", usage());
        return ExitCode::SUCCESS;
    }
    let context = match Context::new(options) {
        Ok(context) => context,
        Err(error) => {
            eprintln!("precommit: {error}");
            return ExitCode::from(2);
        }
    };
    let start = Instant::now();
    let mut failed = Vec::new();
    for step in steps::all() {
        if let Err(why) = context.options.selects(&step) {
            println!("skip {:<15} {why}", step.name);
            continue;
        }
        if !failed.is_empty() && !context.options.keep_going {
            println!("skip {:<15} not run after a failure", step.name);
            continue;
        }
        let began = Instant::now();
        let mut log = match Log::create(&context.work, step.name) {
            Ok(log) => log,
            Err(error) => {
                eprintln!("precommit: {error}");
                return ExitCode::from(2);
            }
        };
        let outcome = (step.run)(&context, &mut log);
        let seconds = began.elapsed().as_secs();
        match outcome {
            Outcome::Passed(summary) => println!("ok   {:<15} {summary} ({seconds} s)", step.name),
            Outcome::Skipped(why) => println!("skip {:<15} {why}", step.name),
            Outcome::Failed(summary, detail) => {
                println!("FAIL {:<15} {summary} ({seconds} s)", step.name);
                for line in detail.lines().take(20) {
                    println!("       {line}");
                }
                println!("       log: {}", log.path().display());
                failed.push(step.name);
            }
        }
    }
    let minutes = start.elapsed().as_secs_f64() / 60.0;
    if failed.is_empty() {
        println!("precommit: all selected steps passed ({minutes:.1} min)");
        ExitCode::SUCCESS
    } else {
        println!(
            "precommit: FAILED: {} ({minutes:.1} min)",
            failed.join(", ")
        );
        ExitCode::FAILURE
    }
}

#[cfg(test)]
mod tests;
