use std::{collections::BTreeMap, fs, io::Write, path::Path, process::Command};
const ROOT: &str = "/tmp/longfellow-ablation";
const CASES: [&str; 6] = ["legacy", "degree", "zero", "one", "minus", "all"];
const APPS: [&str; 4] = ["v9-2", "v9-4", "mldsa-44", "mldsa-65"];
#[derive(Clone, Copy)]
struct Sample {
    p: f64,
    v: f64,
    proof: usize,
    ph: usize,
    vh: usize,
}
fn run(case: &str, app: &str, prepare: bool, memory: bool, cpu: usize) -> (Sample, String) {
    let root = Path::new(ROOT).join(case);
    fs::create_dir_all(&root).unwrap();
    let dir = if case == "legacy" || case == "degree" {
        Path::new(ROOT).join(format!("{case}-bin"))
    } else {
        Path::new(ROOT).join("current")
    };
    let name = if app.starts_with("v9-") {
        if memory {
            "v9-memory"
        } else {
            "v9"
        }
    } else if memory {
        "mldsa-memory"
    } else {
        "mldsa"
    };
    let mut c = Command::new("taskset");
    c.args(["-c", &cpu.to_string()]).arg(dir.join(name));
    if case != "legacy" && case != "degree" {
        c.env("CIRCUIT_COEFFICIENT_CLASSES", case);
    }
    if let Some(attrs) = app.strip_prefix("v9-") {
        c.env("MDOC_V9_QUICK", "1")
            .env("MDOC_V9_ATTRIBUTES", attrs)
            .env("MDOC_V9_SAMPLES", "1")
            .env("MDOC_V9_CACHE", root.join("v9"));
    } else {
        let param = app.strip_prefix("mldsa-").unwrap();
        c.arg(param).env("MLDSA_BENCH_REPEATS", "1");
        let archives = root.join("mldsa");
        if prepare && !archives.join(format!("MlDsa{param}.lfc2")).exists() {
            c.env("MLDSA_BENCH_SAVE_DIR", archives);
        } else {
            c.env("MLDSA_BENCH_ARCHIVE_DIR", archives);
        }
    }
    let output = c.output().unwrap();
    let out = String::from_utf8(output.stdout).unwrap();
    let err = String::from_utf8(output.stderr).unwrap();
    let log = format!("{err}{out}");
    assert!(output.status.success(), "{case} {app}: {log}");
    let s = if app.starts_with("v9-") {
        let row = out
            .lines()
            .find(|l| l.starts_with(|ch: char| ch.is_ascii_digit()))
            .unwrap();
        let v: Vec<_> = row.split(',').collect();
        Sample {
            p: v[4].parse().unwrap(),
            v: v[5].parse().unwrap(),
            proof: v[6].parse().unwrap(),
            ph: v[7].parse().unwrap(),
            vh: v[8].parse().unwrap(),
        }
    } else {
        let row = err
            .lines()
            .find_map(|l| l.strip_prefix("  End to end: prover="))
            .unwrap();
        let (p, tail) = row.split_once(" ms, verifier=").unwrap();
        let (v, b) = tail.split_once(" ms, proof=").unwrap();
        let (mut ph, mut vh) = (0, 0);
        if memory {
            let row = err
                .lines()
                .find_map(|l| l.strip_prefix("  End-to-end additional peak heap: prover="))
                .unwrap();
            let (a, b) = row.split_once(", verifier=").unwrap();
            ph = a.parse().unwrap();
            vh = b.strip_suffix(" bytes").unwrap().parse().unwrap();
        }
        Sample {
            p: p.parse().unwrap(),
            v: v.parse().unwrap(),
            proof: b.strip_suffix(" bytes").unwrap().parse().unwrap(),
            ph,
            vh,
        }
    };
    (s, log)
}
fn median(mut x: Vec<f64>) -> f64 {
    x.sort_by(f64::total_cmp);
    x[x.len() / 2]
}
fn main() {
    let phase = std::env::args().nth(1).unwrap();
    if phase == "prepare" {
        std::thread::scope(|scope| {
            for (i, case) in CASES.into_iter().enumerate() {
                scope.spawn(move || {
                    for app in APPS {
                        let (_, log) = run(case, app, true, false, 4 + i);
                        fs::write(format!("{ROOT}/{case}/prepare-{app}.log"), log).unwrap();
                        println!("prepared {case} {app}");
                    }
                });
            }
        });
        return;
    }
    if phase == "memory" {
        let mut csv = String::from("case,application,prover_heap_bytes,verifier_heap_bytes\n");
        for case in CASES {
            for app in APPS {
                let (s, log) = run(case, app, false, true, 2);
                fs::write(format!("{ROOT}/{case}/memory-{app}.log"), log).unwrap();
                csv.push_str(&format!("{case},{app},{},{}\n", s.ph, s.vh));
                println!("memory {case} {app}: {} {}", s.ph, s.vh);
            }
        }
        fs::write(format!("{ROOT}/memory.csv"), csv).unwrap();
        return;
    }
    assert_eq!(phase, "time");
    let mut groups = BTreeMap::<(String, String), Vec<Sample>>::new();
    let mut csv = String::from("case,application,sample,prover_ms,verifier_ms,proof_bytes\n");
    for app in APPS {
        for case in CASES {
            let _ = run(case, app, false, false, 2);
        }
        for i in 0..7 {
            for offset in 0..CASES.len() {
                let j = if i % 2 == 0 {
                    (offset + i) % CASES.len()
                } else {
                    (CASES.len() - 1 - offset + i) % CASES.len()
                };
                let case = CASES[j];
                let (s, log) = run(case, app, false, false, 2);
                let mut file = fs::OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(format!("{ROOT}/{case}/timing-{app}.log"))
                    .unwrap();
                writeln!(file, "sample {i}\n{log}").unwrap();
                groups.entry((case.into(), app.into())).or_default().push(s);
                csv.push_str(&format!(
                    "{case},{app},{i},{:.6},{:.6},{}\n",
                    s.p, s.v, s.proof
                ));
            }
            println!("timed {app} sample {i}");
        }
    }
    let mut table = String::from("case,application,prover_ms,verifier_ms,proof_bytes\n");
    for ((case, app), samples) in groups {
        assert!(samples.iter().all(|s| s.proof == samples[0].proof));
        table.push_str(&format!(
            "{case},{app},{:.6},{:.6},{}\n",
            median(samples.iter().map(|s| s.p).collect()),
            median(samples.iter().map(|s| s.v).collect()),
            samples[0].proof
        ));
    }
    fs::write(format!("{ROOT}/samples.csv"), csv).unwrap();
    fs::write(format!("{ROOT}/medians.csv"), &table).unwrap();
    print!("{table}");
}
