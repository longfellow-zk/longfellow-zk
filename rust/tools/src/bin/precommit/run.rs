// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Running commands into a step's log, and reading their output back.
use std::{
    fs::{File, OpenOptions},
    io::{Read, Seek, SeekFrom, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

/// How a step ended: its one-line summary, and for a failure the lines
/// that show why.
pub(crate) enum Outcome {
    Passed(String),
    Skipped(String),
    Failed(String, String),
}

/// One step's log file, which receives every command's output.
pub(crate) struct Log {
    path: PathBuf,
    file: File,
}

/// A finished command: whether it succeeded, and what it printed (stdout and
/// stderr, interleaved).
pub(crate) struct Run {
    pub(crate) success: bool,
    pub(crate) output: String,
}

impl Log {
    pub(crate) fn create(directory: &Path, step: &str) -> Result<Self, String> {
        let path = directory.join(format!("{step}.log"));
        let file = OpenOptions::new()
            .create(true)
            .truncate(true)
            .read(true)
            .write(true)
            .open(&path)
            .map_err(|e| format!("{}: {e}", path.display()))?;
        Ok(Self { path, file })
    }

    pub(crate) fn path(&self) -> &Path {
        &self.path
    }

    /// Note a line in the log.
    pub(crate) fn note(&mut self, text: &str) {
        let _ = writeln!(self.file, "{text}");
    }

    /// Run `command` to completion with its output in the log. A command
    /// that cannot start fails, with the reason as its output.
    pub(crate) fn run(&mut self, command: &mut Command) -> Run {
        self.note(&format!("$ {command:?}"));
        let start = self.file.seek(SeekFrom::End(0)).unwrap_or(0);
        let streams = self
            .file
            .try_clone()
            .and_then(|out| Ok((out, self.file.try_clone()?)));
        let finished = streams.and_then(|(out, err)| {
            command
                .stdin(Stdio::null())
                .stdout(out)
                .stderr(err)
                .status()
        });
        let mut output = String::new();
        if self.file.seek(SeekFrom::Start(start)).is_ok() {
            let mut bytes = Vec::new();
            let _ = (&self.file).read_to_end(&mut bytes);
            output = String::from_utf8_lossy(&bytes).into_owned();
        }
        let _ = self.file.seek(SeekFrom::End(0));
        match finished {
            Ok(status) => {
                self.note(&format!("({status})"));
                Run {
                    success: status.success(),
                    output,
                }
            }
            Err(error) => {
                let reason = format!("cannot run {:?}: {error}", command.get_program());
                self.note(&reason);
                Run {
                    success: false,
                    output: reason,
                }
            }
        }
    }
}

/// Compiler diagnostics in cargo output: each line that starts with
/// `warning` or `error`, with the lines after it up to the next blank line,
/// at most `limit` lines in all.
pub(crate) fn diagnostics(output: &str, limit: usize) -> Vec<&str> {
    let mut found = Vec::new();
    let mut inside = false;
    for line in output.lines() {
        if line.starts_with("warning") || line.starts_with("error") {
            inside = true;
        } else if line.trim().is_empty() {
            inside = false;
        }
        if inside {
            found.push(line);
            if found.len() == limit {
                break;
            }
        }
    }
    found
}

/// The last `count` lines of `output`.
pub(crate) fn tail(output: &str, count: usize) -> String {
    let lines: Vec<_> = output.lines().collect();
    lines[lines.len().saturating_sub(count)..].join("\n")
}

/// The diagnostics of a failed or noisy command, or else its last lines.
pub(crate) fn why(run: &Run) -> String {
    let found = diagnostics(&run.output, 20);
    if found.is_empty() {
        tail(&run.output, 20)
    } else {
        found.join("\n")
    }
}
