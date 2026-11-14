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
mod catalog;
mod cli;
mod exact;
mod generate;
mod lean;
mod profiles;
use cli::{require, root, Args, Result};

fn run() -> Result<()> {
    let (command, args) = Args::parse()?;
    match command.as_str() {
        "help" => {
            println!("zk_tool commands:\n  check-profiles --protocol polygero [--check-lean PROJECT] [--hahn-cache CACHE] [--profile k,s,n,t]\n  certify-hahn --formal PROJECT [--cache CACHE] [--jobs N] [--reuse-checked-cache MODULES]\n  tune-polygero --witnesses N --field-bytes B [--rate 4|7] [--max-n N]\n  generate-v2-specs (requires compiler,mdoc features)");
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
        "tune-polygero" => {
            args.validate(&["--witnesses", "--field-bytes", "--rate", "--max-n"])?;
            let number = |key: &str| -> Result<Option<usize>> {
                args.one(key)?
                    .map(|v| v.parse::<usize>().map_err(|e| format!("{key}: {e}").into()))
                    .transpose()
            };
            let nw = number("--witnesses")?.ok_or("missing --witnesses")?;
            let field_bytes = number("--field-bytes")?.ok_or("missing --field-bytes")?;
            // The interpolation backend's capacity bounds n; the caller supplies it.
            let max_n = number("--max-n")?.unwrap_or(usize::MAX);
            let accept = |config: longfellow_zk::runtime::v2::proto::polygero::PolygeroConfig| {
                config.n <= max_n
            };
            let config = match number("--rate")? {
                None => catalog::tune_large_field(nw, field_bytes, accept),
                Some(rate) => catalog::tune_large_field_at_rate(rate, nw, field_bytes, accept),
            }
            .ok_or("no catalog profile fits")?;
            let bytes = catalog::estimated_proof_bytes(config, nw, field_bytes)
                .ok_or("invalid geometry")?;
            println!(
                "k={} s={} n={} t={} estimated_proof_bytes={bytes}",
                config.k, config.s, config.n, config.t
            );
            Ok(())
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
