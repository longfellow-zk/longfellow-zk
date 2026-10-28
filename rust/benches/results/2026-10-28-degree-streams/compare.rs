// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Standalone paired benchmark driver; compile with rustc --edition=2021.
use std::{collections::BTreeMap, fs, process::Command};
#[derive(Clone, Copy)]
struct Sample {
    p: f64,
    v: f64,
    b: usize,
}
fn run(app: &str, version: &str, paths: &[String]) -> (Sample, String) {
    let before = version == "before";
    let bin = &paths[usize::from(!before)];
    let mut c = Command::new("taskset");
    c.args(["-c", "2"]);
    if let Some(attrs) = app.strip_prefix("v9-") {
        c.arg(format!("{bin}/{}", "v9"));
        c.env("MDOC_V9_QUICK", "1")
            .env("MDOC_V9_SAMPLES", "1")
            .env("MDOC_V9_ATTRIBUTES", attrs)
            .env("MDOC_V9_CACHE", &paths[2 + usize::from(!before)]);
    } else {
        c.arg(format!("{bin}/{}", "mldsa"))
            .arg(app.strip_prefix("mldsa-").unwrap());
        c.env("MLDSA_BENCH_REPEATS", "1")
            .env("MLDSA_BENCH_ARCHIVE_DIR", &paths[4 + usize::from(!before)]);
    }
    let out = c.output().unwrap();
    let stdout = String::from_utf8(out.stdout).unwrap();
    let stderr = String::from_utf8(out.stderr).unwrap();
    assert!(out.status.success(), "{app} {version}: {stderr}");
    let raw = format!("{stderr}{stdout}");
    let sample = if app.starts_with("v9-") {
        let row = stdout
            .lines()
            .find(|l| l.split(',').count() == 9 && l.starts_with(|x: char| x.is_ascii_digit()))
            .unwrap();
        let v: Vec<_> = row.split(',').collect();
        Sample {
            p: v[4].parse().unwrap(),
            v: v[5].parse().unwrap(),
            b: v[6].parse().unwrap(),
        }
    } else {
        let line = stderr
            .lines()
            .find_map(|l| l.strip_prefix("  End to end: prover="))
            .unwrap();
        let (p, rest) = line.split_once(" ms, verifier=").unwrap();
        let (v, b) = rest.split_once(" ms, proof=").unwrap();
        Sample {
            p: p.parse().unwrap(),
            v: v.parse().unwrap(),
            b: b.strip_suffix(" bytes").unwrap().parse().unwrap(),
        }
    };
    (sample, raw)
}
fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(f64::total_cmp);
    v[v.len() / 2]
}
fn main() {
    let paths: Vec<_> = std::env::args().skip(1).collect();
    assert_eq!(paths.len(), 7, "usage: compare BEFORE_BIN AFTER_BIN BEFORE_V9 AFTER_V9 BEFORE_MLDSA AFTER_MLDSA OUTPUT_DIR");
    let root = &paths[6];
    fs::create_dir_all(root).unwrap();
    let mut samples = BTreeMap::<(String, String), Vec<Sample>>::new();
    let mut logs = BTreeMap::<(String, String), String>::new();
    let mut csv = String::from("application,version,sample,prover_ms,verifier_ms,proof_bytes\n");
    for app in ["v9-2", "v9-4", "mldsa-44", "mldsa-65"] {
        // Untimed process warmups populate executable and circuit file pages.
        for version in ["before", "after"] {
            let _ = run(app, version, &paths);
        }
        for i in 0..7 {
            for version in if i % 2 == 0 {
                ["before", "after"]
            } else {
                ["after", "before"]
            } {
                let (s, raw) = run(app, version, &paths);
                let key = (app.to_string(), version.to_string());
                logs.entry(key.clone())
                    .or_default()
                    .push_str(&format!("comparison sample {i}\n{raw}\n"));
                samples.entry(key).or_default().push(s);
                csv.push_str(&format!(
                    "{app},{version},{i},{:.6},{:.6},{}\n",
                    s.p, s.v, s.b
                ));
            }
        }
        println!("completed {app}");
    }
    let mut table = String::from("application,version,prover_ms,verifier_ms,proof_bytes\n");
    for ((app, version), v) in &samples {
        assert!(v.iter().all(|s| s.b == v[0].b));
        table.push_str(&format!(
            "{app},{version},{:.6},{:.6},{}\n",
            median(v.iter().map(|s| s.p).collect()),
            median(v.iter().map(|s| s.v).collect()),
            v[0].b
        ));
    }
    fs::write(format!("{root}/samples.csv"), csv).unwrap();
    fs::write(format!("{root}/medians.csv"), &table).unwrap();
    for ((app, version), s) in logs {
        fs::write(format!("{root}/{version}-{app}.log"), s).unwrap();
    }
    print!("{table}");
}
