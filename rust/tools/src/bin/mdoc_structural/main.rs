// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! File-based NEXT mdoc application. The request manifest is the verifier's
//! public statement; credential bytes are needed only by `prove`.
use std::{
    fs::File,
    io::Read,
    path::{Path, PathBuf},
    time::Instant,
};

use longfellow_zk::{
    mdoc::{
        development_provider,
        v2::{self, RequestedAttribute},
    },
    runtime::random::SecureRandomEngine,
};
use serde_json::{json, Value};

const USAGE: &str = "mdoc_structural compile <attribute-count> <bundle>\nmdoc_structural prove <bundle> <request.json> <proof>\nmdoc_structural verify <bundle> <request.json> <proof>";

fn read(path: &Path, limit: u64) -> Result<Vec<u8>, String> {
    let mut data = Vec::new();
    File::open(path)
        .map_err(|e| format!("{}: {e}", path.display()))?
        .take(limit + 1)
        .read_to_end(&mut data)
        .map_err(|e| e.to_string())?;
    if data.len() as u64 > limit {
        return Err(format!("{} exceeds {limit} bytes", path.display()));
    }
    Ok(data)
}

fn decode_hex(encoded: &str) -> Result<Vec<u8>, String> {
    let value = encoded.strip_prefix("0x").unwrap_or(encoded);
    if !value.len().is_multiple_of(2) {
        return Err("CBOR hex must contain complete bytes".into());
    }
    value
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            let digit = |byte: u8| (byte as char).to_digit(16).ok_or("invalid CBOR hex");
            Ok(((digit(pair[0])? << 4) | digit(pair[1])?) as u8)
        })
        .collect()
}

fn text<'a>(json: &'a Value, name: &str) -> Result<&'a str, String> {
    json.get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("missing string: {name}"))
}

struct Request {
    issuer_x: String,
    issuer_y: String,
    now: String,
    doc_type: String,
    mdoc: Option<PathBuf>,
    transcript: Vec<u8>,
    attrs: Vec<RequestedAttribute>,
}

impl Request {
    fn read(path: &Path) -> Result<Self, String> {
        let json: Value =
            serde_json::from_slice(&read(path, 1 << 20)?).map_err(|e| e.to_string())?;
        let directory = path.parent().unwrap_or(Path::new(".")).to_path_buf();
        let transcript = read(&directory.join(text(&json, "transcript")?), 1 << 20)?;
        let attrs = json
            .get("attributes")
            .and_then(Value::as_array)
            .ok_or("missing attributes array")?
            .iter()
            .map(|attr| {
                Ok(v2::req_attr(
                    text(attr, "namespace")?,
                    text(attr, "id")?,
                    decode_hex(text(attr, "value_cbor")?)?,
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        if !(1..=4).contains(&attrs.len()) {
            return Err("request must contain 1..=4 attributes".into());
        }
        Ok(Self {
            issuer_x: text(&json, "issuer_x")?.into(),
            issuer_y: text(&json, "issuer_y")?.into(),
            now: text(&json, "now")?.into(),
            doc_type: text(&json, "doc_type")?.into(),
            mdoc: json
                .get("mdoc")
                .and_then(Value::as_str)
                .map(|credential| directory.join(credential)),
            transcript,
            attrs,
        })
    }
}

fn run() -> Result<(), String> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() == 1 && matches!(args[0].as_str(), "--help" | "-h") {
        println!("{USAGE}");
        return Ok(());
    }
    let started = Instant::now();
    match args.first().map(String::as_str) {
        Some("compile") if args.len() == 3 => {
            let count = args[1].parse().map_err(|_| "invalid attribute count")?;
            let provided = development_provider::compile_next(count)?;
            development_provider::write_next(
                File::create(&args[2]).map_err(|e| e.to_string())?,
                &provided,
            )?;
            println!(
                "{}",
                json!({"version":provided.spec().version, "attributes":count,
                "archive_bytes":provided.compressed().len(), "elapsed_ms":started.elapsed().as_secs_f64()*1000.0})
            );
        }
        Some(command @ ("prove" | "verify")) if args.len() == 4 => {
            let provided =
                development_provider::read_next(File::open(&args[1]).map_err(|e| e.to_string())?)?;
            let request = Request::read(Path::new(&args[2]))?;
            if request.attrs.len() != provided.spec().num_attributes {
                return Err("request and circuit attribute counts differ".into());
            }
            let proof = if command == "prove" {
                let mdoc = read(
                    request.mdoc.as_deref().ok_or("missing string: mdoc")?,
                    1 << 20,
                )?;
                v2::run_mdoc_prover_inner(
                    provided.spec(),
                    provided.compressed(),
                    &mdoc,
                    &request.issuer_x,
                    &request.issuer_y,
                    &request.transcript,
                    &request.attrs,
                    &request.now,
                    &request.doc_type,
                    &mut SecureRandomEngine::new(),
                )
                .map_err(|e| format!("proving failed: {e:?}"))?
            } else {
                read(Path::new(&args[3]), 32 << 20)?
            };
            v2::run_mdoc_verifier(
                provided.spec(),
                provided.compressed(),
                &request.issuer_x,
                &request.issuer_y,
                &request.transcript,
                &request.attrs,
                &request.now,
                &request.doc_type,
                &proof,
            )
            .map_err(|e| format!("verification failed: {e:?}"))?;
            if command == "prove" {
                std::fs::write(&args[3], &proof).map_err(|e| e.to_string())?;
            }
            println!(
                "{}",
                json!({"version":provided.spec().version, "command":command, "verified":true,
                "proof_bytes":proof.len(), "elapsed_ms":started.elapsed().as_secs_f64()*1000.0})
            );
        }
        _ => return Err(USAGE.into()),
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests;
