use std::{
    fs,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::Command,
};
const APPS: [&str; 4] = ["next-2", "next-4", "mldsa-44", "mldsa-65"];
#[derive(Clone, Copy)]
struct Sample {
    p: f64,
    v: f64,
    proof: usize,
    ph: usize,
    vh: usize,
}
fn latest(prefix: &str) -> PathBuf {
    fs::read_dir("/home/athena/sandbox/hack/longfellow-zk/rust/target/release/deps")
        .unwrap()
        .map(|e| e.unwrap())
        .filter(|e| {
            e.file_name().to_string_lossy().starts_with(prefix)
                && e.metadata().unwrap().permissions().mode() & 0o111 != 0
        })
        .max_by_key(|e| e.metadata().unwrap().modified().unwrap())
        .unwrap()
        .path()
}
fn run(root: &Path, app: &str, prepare: bool, memory: bool) -> Sample {
    let bin = if app.starts_with("next") {
        "next"
    } else {
        "mldsa"
    };
    let dir = if memory { "memory" } else { "timing" };
    let mut cmd = Command::new("taskset");
    cmd.args(["-c", if prepare { "4" } else { "2" }])
        .arg(root.join(dir).join(bin));

    let n = app.rsplit('-').next().unwrap();
    if bin == "next" {
        cmd.env("MDOC_V9_ATTRIBUTES", n)
            .env("MDOC_V9_SAMPLES", "1")
            .env("MDOC_V9_CACHE", root.join("circuits/next"));
    } else {
        cmd.arg(n).env("MLDSA_BENCH_REPEATS", "1").env(
            if prepare {
                "MLDSA_BENCH_SAVE_DIR"
            } else {
                "MLDSA_BENCH_ARCHIVE_DIR"
            },
            root.join("circuits/mldsa"),
        );
    }
    let out = cmd.output().unwrap();
    let stdout = String::from_utf8(out.stdout).unwrap();
    let stderr = String::from_utf8(out.stderr).unwrap();
    let log = format!("{stderr}{stdout}");
    fs::create_dir_all(root.join("logs")).unwrap();
    let label = if prepare {
        "prepare"
    } else if memory {
        "memory"
    } else {
        "time"
    };
    use std::io::Write;
    let mut file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(root.join(format!("logs/{label}-{app}.log")))
        .unwrap();
    file.write_all(log.as_bytes()).unwrap();
    assert!(out.status.success(), "{app}: {log}");
    if bin == "next" {
        let row = stdout
            .lines()
            .find(|l| l.starts_with(|c: char| c.is_ascii_digit()))
            .unwrap();
        let v: Vec<_> = row.split(',').collect();
        Sample {
            p: v[2].parse().unwrap(),
            v: v[3].parse().unwrap(),
            proof: v[4].parse().unwrap(),
            ph: v[5].parse().unwrap(),
            vh: v[6].parse().unwrap(),
        }
    } else {
        let row = stderr
            .lines()
            .find_map(|l| l.strip_prefix("  End to end: prover="))
            .unwrap();
        let (p, tail) = row.split_once(" ms, verifier=").unwrap();
        let (v, b) = tail.split_once(" ms, proof=").unwrap();
        let (mut ph, mut vh) = (0, 0);
        if memory {
            let row = stderr
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
    }
}
fn main() {
    let phase = std::env::args().nth(1).unwrap();
    let root = Path::new("/tmp/native-three-benchmark");
    if let Some(label) = phase.strip_prefix("stage-") {
        let dir = root.join(if label == "time" { "timing" } else { "memory" });
        fs::create_dir_all(&dir).unwrap();
        for (prefix, name) in [
            ("mdoc_zk_bench_next-", "next"),
            ("mldsa_bench_v2-", "mldsa"),
        ] {
            let path = latest(prefix);
            fs::copy(&path, dir.join(name)).unwrap();
            println!("staged {name}: {}", path.display());
        }
        return;
    }
    if phase == "prepare" {
        for app in APPS {
            run(root, app, true, false);
            println!("prepared {app}");
        }
        return;
    }
    if phase == "memory" {
        let mut csv = String::from("application,prover_heap_bytes,verifier_heap_bytes\n");
        for app in APPS {
            let s = run(root, app, false, true);
            assert!(s.ph > 0 && s.vh > 0);
            csv.push_str(&format!("{app},{},{}\n", s.ph, s.vh));
        }
        fs::write(root.join("memory.csv"), &csv).unwrap();
        print!("{csv}");
        return;
    }
    assert_eq!(phase, "time");
    for app in APPS {
        run(root, app, false, false);
    }
    let mut groups: [Vec<Sample>; 4] = std::array::from_fn(|_| Vec::new());
    let mut csv = String::from("application,sample,prover_ms,verifier_ms,proof_bytes\n");
    for i in 0..7 {
        for offset in 0..4 {
            let index = if i % 2 == 0 {
                (i + offset) % 4
            } else {
                (i + 3 - offset) % 4
            };
            let app = APPS[index];
            let s = run(root, app, false, false);
            assert_eq!((s.ph, s.vh), (0, 0));
            csv.push_str(&format!("{app},{i},{:.6},{:.6},{}\n", s.p, s.v, s.proof));
            groups[index].push(s);
        }
        println!("sample {i} verified");
    }
    let mut med = String::from("application,prover_ms,verifier_ms,proof_bytes\n");
    for (app, g) in APPS.into_iter().zip(groups) {
        let mut p: Vec<_> = g.iter().map(|s| s.p).collect();
        let mut v: Vec<_> = g.iter().map(|s| s.v).collect();
        p.sort_by(f64::total_cmp);
        v.sort_by(f64::total_cmp);
        assert!(g.iter().all(|s| s.proof == g[0].proof));
        med.push_str(&format!("{app},{:.6},{:.6},{}\n", p[3], v[3], g[0].proof));
    }
    fs::write(root.join("samples.csv"), csv).unwrap();
    fs::write(root.join("medians.csv"), &med).unwrap();
    print!("{med}");
}
