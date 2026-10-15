#!/usr/bin/env python3
"""Reproducible ID-preserving LFR1 experiment on saved immutable circuits.

Build: cargo test --release -p circuits-experimental --test relative_segments --no-run
Run from workspace root. Size jobs overlap; their timing columns are diagnostics.
"""
import argparse
import concurrent.futures
import csv
import hashlib
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument("--binary", default="target/release/deps/relative_segments-1931a39ee0ca3ca8")
parser.add_argument("--out", default="target/relative-segments-representative")
parser.add_argument("--workers", type=int, default=3)
parser.add_argument("--proof-binary", default="target/release/deps/template_proofs-1eba8861353003c4")
parser.add_argument("--validate-only", action="store_true", help="reuse completed size logs, rerun serial load/proof checks")
args = parser.parse_args()
out = Path(args.out)
out.mkdir(parents=True, exist_ok=True)
jobs = []
for dataset in ("mldsa44", "mldsa65"):
    root = Path(f"target/plucker-grid-sf18/p4-b0-r1/{dataset}")
    jobs.append((dataset, root / f"{dataset}-wire_whole-b3-w10000000-o4-shape_classes-reuse.lfc2", 18, "0,8,32,128"))
    jobs.append((dataset + "_source", root / "source.lfc2", 18, "0"))
for dataset, field in (("mdoc_hash2", 16), ("mdoc_sig", 32)):
    jobs.append((dataset, Path(f"target/traversal-circuits/{dataset}--kind_abs_lex0213_r5.lfc2"), field, "0,8,32,128"))
for label, suffix in (("whole", "standard"), ("shape", "shape_instances-standard")):
    jobs.append(("historical44_" + label, Path(f"target/template-order-lfc2/mldsa44-b3-w10000000-o4-{suffix}.lfc2"), 24, "0,8,32,128"))
for boundary in ("boundary32", "boundary128"):
    jobs.append(("historical44_" + boundary, Path(f"target/template-order-lfc2/mldsa44-b3-w10000000-o4-{boundary}.lfc2"), 24, "0"))

def run(job):
    name, path, size, widths = job
    env = dict(os.environ, REL_DATASET=name, REL_CIRCUIT=str(path), REL_FIELD_BYTES=str(size), REL_WIDTHS=widths, REL_OUT=str(out))
    with (out / f"{name}.log").open("w") as log:
        subprocess.run([args.binary, "relative_segment_sweep", "--ignored", "--nocapture"], env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    print(f"Verified {name}", flush=True)

if not args.validate_only:
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        list(pool.map(run, jobs))
rows = []
for name, *_ in jobs:
    for line in (out / f"{name}.log").read_text().splitlines():
        if line.startswith("REL_"):
            kind, *values = line.split()
            rows.append(dict(kind=kind, **dict(v.split("=", 1) for v in values)))
keys = list(dict.fromkeys(k for row in rows for k in row))
result = HERE / "results/relative-segments.csv"
with result.open("w", newline="") as f:
    writer = csv.DictWriter(f, keys)
    writer.writeheader()
    writer.writerows(rows)
assert sum(r["kind"] == "REL_RESULT" for r in rows) == 112
print(f"Wrote {result}", flush=True)

# Serial validation and timing only after all size jobs have joined.
for name, path, *_ in jobs:
    if name not in ("mldsa44", "mldsa65", "mdoc_hash2", "mdoc_sig"):
        continue
    env = dict(os.environ, REL_DATASET=name, REL_CIRCUIT=str(path), REL_RELATIVE=str(out / f"{name}-first-pool-w0.lfr1"))
    with (out / f"{name}-load.log").open("w") as log:
        subprocess.run([args.binary, "relative_segment_load_bench", "--ignored", "--nocapture", "--test-threads=1"], env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    print(f"Serial load benchmark: {name}", flush=True)
for name in ("mldsa44", "mldsa65"):
    env = dict(os.environ, MLDSA_SLICE_PERIOD="4", MLDSA_FIRST_ROUND="1", MLDSA_PLUCKER_BITS="0", ORDER_REPEATS="1", ORDER_SUMCHECK="hand",
               ORDER_PROOF_CIRCUIT=str(out / f"{name}-decoded.lfc2"), ORDER_EXPECT_PROOF=f"target/plucker-grid-sf18/p4-b0-r1/{name}/proof.bin")
    with (out / f"{name}-proof.log").open("w") as log:
        subprocess.run([args.proof_binary, f"{name}_template_proof", "--ignored", "--nocapture", "--test-threads=1"], env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    print(f"Identical verified proof: {name}", flush=True)
hashes = {str(p): hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in [args.binary, args.proof_binary, HERE / "relative_segments.rs", HERE / "run_relative_segments.py", *[job[1] for job in jobs]]}
(out / "provenance.json").write_text(json.dumps(hashes, indent=2) + "\n")
