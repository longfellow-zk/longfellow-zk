// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! NEXT circuits for tests, compiled once per test binary.
//!
//! Compiling a NEXT circuit takes about 8 s and 1.5 GB at its peak, and many
//! tests need one. [`next_circuit`] saves each compiled circuit with
//! [`write_next`] in a directory beside the test binary, named by a digest of
//! the running binary, and later calls read it back with [`read_next`]. A
//! rebuilt binary has another digest, so it never reads a bundle that an
//! older compiler wrote; its first call removes the older bundles.
//!
//! A bundle is written to a temporary file and renamed into place, so a
//! reader sees no bundle or a complete one: tests that race may each
//! compile, in this binary or in another process, but never read a partial
//! bundle. Every compilation holds [`one_compilation`], so the tests add at
//! most one NEXT compilation to the peak memory of the test run.
use std::{
    fs::{self, File},
    io::{self, BufReader, BufWriter, Read},
    path::{Path, PathBuf},
    sync::{Mutex, MutexGuard, PoisonError},
};

use sha2::{Digest, Sha256};

use super::super::{compile_next, read_next, write_next};
use crate::mdoc::v2::provider::ProvidedCircuit;

/// Held by every test compilation of a NEXT circuit.
static COMPILING: Mutex<()> = Mutex::new(());

/// Wait until no other test compiles a NEXT circuit, and keep it so while
/// the guard lives.
pub(crate) fn one_compilation() -> MutexGuard<'static, ()> {
    COMPILING.lock().unwrap_or_else(PoisonError::into_inner)
}

/// The NEXT circuit of `num_attributes` attributes: the saved bundle of this
/// test binary if there is one, otherwise a fresh compilation, which it
/// saves. A cache that cannot be read or written only costs compilations.
pub(crate) fn next_circuit(num_attributes: usize) -> ProvidedCircuit {
    let path = cache_directory().map(|d| d.join(format!("next-{num_attributes}.bundle")));
    let saved = || path.as_deref().and_then(read);
    if let Some(provided) = saved() {
        return provided;
    }
    let _one = one_compilation();
    // Another test may have saved it while this one waited.
    if let Some(provided) = saved() {
        return provided;
    }
    let provided = compile_next(num_attributes).unwrap();
    if let Some(destination) = &path {
        // The cache is an optimization: a failed save leaves the next call
        // to compile again.
        let _ = save(destination, &provided);
    }
    provided
}

fn read(path: &Path) -> Option<ProvidedCircuit> {
    read_next(BufReader::new(File::open(path).ok()?)).ok()
}

/// Write the bundle beside `path` and rename it into place.
fn save(path: &Path, provided: &ProvidedCircuit) -> io::Result<()> {
    let temporary = path.with_extension(format!("{}.partial", std::process::id()));
    let written = (|| {
        let mut writer = BufWriter::new(File::create(&temporary)?);
        write_next(&mut writer, provided).map_err(io::Error::other)?;
        writer
            .into_inner()
            .map_err(io::IntoInnerError::into_error)?;
        fs::rename(&temporary, path)
    })();
    if written.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    written
}

/// `<test binary>.next/<digest>`, created if needed, after removing the
/// bundles of other binaries that had the same path.
fn cache_directory() -> Option<PathBuf> {
    let executable = std::env::current_exe().ok()?;
    let mut name = executable.file_name()?.to_owned();
    name.push(".next");
    let root = executable.with_file_name(name);
    let digest = running_binary_digest()?;
    let directory = root.join(&digest);
    if !directory.is_dir() {
        for entry in fs::read_dir(&root).into_iter().flatten().flatten() {
            if entry.file_name() != digest.as_str() {
                let _ = fs::remove_dir_all(entry.path());
            }
        }
        fs::create_dir_all(&directory).ok()?;
    }
    Some(directory)
}

/// A digest of the binary this process runs. On Linux it reads the running
/// image, which stays the same when a rebuild replaces the file meanwhile.
fn running_binary_digest() -> Option<String> {
    let mut file = File::open("/proc/self/exe")
        .or_else(|_| File::open(std::env::current_exe()?))
        .ok()?;
    let mut hasher = Sha256::new();
    let mut buffer = vec![0; 1 << 20];
    loop {
        match file.read(&mut buffer) {
            Ok(0) => break,
            Ok(n) => hasher.update(&buffer[..n]),
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(_) => return None,
        }
    }
    Some(hex::encode(&hasher.finalize()[..16]))
}
