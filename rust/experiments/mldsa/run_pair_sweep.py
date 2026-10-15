#!/usr/bin/env python3
"""Release/native flat-LFC2 pair sweep; fixed wires, traversal, IDs and proofs.

The grammar is an offline search tool, not a hidden additional runtime format.
All reported bytes include flattened segment dictionaries and execution tokens.
Use summarize_scheduling_sweep.py for actual combined mdoc archive measurements.
"""
import argparse
import concurrent.futures
import csv
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
from run_scheduling_sweep import DATASETS, source, records

POLICIES = ["reuse", "reuse_cdc_128", "reuse_cdcstored_64"]
POLICIES += [f"pair_delta_{s}_{cap}" for s in ("left", "rank", "aligned", "gain") for cap in (32, 128, 512)]
POLICIES += [f"pair_delta_{s}_{cap}" for s in ("repair", "repairgain") for cap in (128, 512)]
POLICIES += [f"pair_stock_{s}_{cap}" for s in ("rank", "gain", "repair", "repairgain") for cap in (512, 2048)]
POLICIES += [f"pair_cdc_{s}_{cap}" for s in ("repair", "repairgain") for cap in (512, 2048)]
POLICIES += [f"pair_lz78_{cap}" for cap in (32, 128, 512)]
POLICIES += ["reuse_pair_delta_rank_128", "reuse_pair_delta_repair_512",
             "reuse_pair_stock_repair_2048", "reuse_pair_stock_repairgain_2048"]

REFINEMENT = ["reuse", "reuse_cdc_128", "reuse_cdcstored_64"]
REFINEMENT += ["pair_delta_repair_32", "pair_delta_repair_128_raw",
               "pair_delta_repair_512_prune", "pair_delta_repair_2048_prune",
               "pair_delta_rank_512_prune", "pair_delta_gain_32_raw"]
REFINEMENT += [f"pair_stock_{s}_{cap}" for s in ("repair", "rank") for cap in (8192, 65536)]
REFINEMENT += ["pair_stock_repair_2048_prune", "pair_stock_repair_65536_prune",
               "pair_cdc_repair_8192", "pair_cdc_repair_65536", "pair_cdc_repair_8192_prune"]
REFINEMENT += ["reuse_pair_stock_repair_8192", "reuse_pair_stock_repair_65536",
               "reuse_pair_stock_repair_2048_prune", "reuse_pair_delta_repair_128_raw"]
REFINEMENT += [f"dict{mode}@{base}" for mode in ("lex", "suffix", "bucketlex", "bucketsuffix", "bucketlength")
               for base in ("reuse", "reuse_cdc_128", "reuse_cdcstored_64", "reuse_pair_stock_repair_2048")]

FACTORING = ["reuse", "reuse_cdc_128", "dictsuffix@reuse_cdc_128", "dictbucketsuffix@reuse_cdc_128"]
FACTORING += [f"extract{kind}{n}@{base}" for kind in ("prefix", "suffix", "both") for n in (8, 32, 128)
              for base in ("reuse", "reuse_cdc_128")]
FACTORING += [f"dictbucketsuffix@extract{kind}{n}@reuse_cdc_128"
              for kind in ("prefix", "suffix", "both") for n in (8, 32, 128)]


def screen(args):
    binary = args.root / "scheduling_sweep"
    digest = hashlib.sha256(Path(args.binary).read_bytes()).hexdigest()
    stamp = args.root / "binary.sha256"
    if stamp.exists():
        assert stamp.read_text().strip() == digest, "binary changed; use a fresh output root"
    else:
        shutil.copyfile(args.binary, binary)
        binary.chmod(0o755)
        stamp.write_text(digest + "\n")
    policies = args.policies.split(",") if args.policies else {"main":POLICIES,"refine":REFINEMENT,"factor":FACTORING}[args.suite]
    metadata = dict(policies=policies, datasets=list(DATASETS), wire="whole", traversal="shape_classes", binary=digest)
    manifest = args.root / "manifest.json"
    if manifest.exists():
        assert json.loads(manifest.read_text()) == metadata
    else:
        manifest.write_text(json.dumps(metadata, indent=2) + "\n")

    def job(name):
        folder = args.root / name / "whole-shape_classes"
        folder.mkdir(parents=True, exist_ok=True)
        log = folder / "screen.log"
        if log.exists() and "test result: ok." in log.read_text():
            assert len(records(log, "SWEEP_SIZE")) == len(policies)
            return
        env = {k: v for k, v in os.environ.items() if not k.startswith(("SWEEP_", "ORDER_", "MLDSA_"))}
        env.update(ORDER_DATASET=name, ORDER_INPUT_CIRCUIT=str(source(name)), SWEEP_WIRE="whole",
                   SWEEP_TRAVERSAL="shape_classes", SWEEP_OUTPUT=str(folder), SWEEP_Z22="1",
                   SWEEP_SEGMENTS=",".join(policies))
        start = time.monotonic()
        with log.open("w") as out:
            subprocess.run([str(binary), "scheduling_segmentation_sweep", "--exact", "--ignored", "--nocapture"],
                           env=env, stdout=out, stderr=subprocess.STDOUT, check=True)
        assert len(records(log, "SWEEP_SIZE")) == len(policies)
        print("PAIR_SWEEP", name, round(time.monotonic() - start, 2), flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        list(pool.map(job, DATASETS))


def summarize(args):
    metadata = json.loads((args.root / "manifest.json").read_text())
    rows = []
    for log in sorted(args.root.glob("*/*/screen.log")):
        assert "test result: ok." in log.read_text(), log
        layout, = records(log, "SWEEP_LAYOUT")
        measurements = records(log, "SWEEP_SIZE")
        assert len(measurements) == len(metadata["policies"])
        for r in measurements:
            path = log.parent / (r["segmentation"] + ".lfc2")
            assert path.stat().st_size == int(r["raw"]) and r["exact"] == "true"
            rows.append(dict(layout, **r, path=str(path)))
    assert len(rows) == len(DATASETS) * len(metadata["policies"])
    with (args.root / "screen.csv").open("w") as out:
        writer = csv.DictWriter(out, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    (args.root / "z22.json").write_text(json.dumps({r["path"]: int(r["z22"]) for r in rows}, indent=2) + "\n")
    for name in DATASETS:
        best = sorted((r for r in rows if r["dataset"] == name), key=lambda r: int(r["z22"]))[:8]
        print(name, [(r["segmentation"], int(r["z22"]), int(r["raw"])) for r in best])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("screen", "summary"))
    parser.add_argument("--root", type=Path, default=Path("target/pair-segmentation-v1"))
    parser.add_argument("--binary", default="target/release/deps/scheduling_sweep-8dc8c5930001dab1")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--policies", help="explicit follow-up list; use a fresh root")
    parser.add_argument("--suite", choices=("main", "refine", "factor"), default="main")
    args = parser.parse_args()
    args.root.mkdir(parents=True, exist_ok=True)
    {"screen": screen, "summary": summarize}[args.phase](args)
