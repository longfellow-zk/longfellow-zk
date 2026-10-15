#!/usr/bin/env python3
"""Three-level experimental format; fixed old layouts and accounted full bytes."""
import argparse
import concurrent.futures
import csv
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
from run_scheduling_sweep import DATASETS, records

SEEDS = {
    "reuse": ("v1", "reuse"),
    "cdc": ("v1", "reuse_cdc_128"),
    "pruned": ("refine", "pair_delta_repair_512_prune"),
    "factored": ("factor", "dictbucketsuffix@extractboth8@reuse_cdc_128"),
}
POLICIES = ["top_8", "top_64", "top_512", "top_64_prune", "top_64_suffix",
            "factor_8", "factor_32", "factor_128", "factor_512", "factor_128_prune",
            "factor_32_suffix", "factor_128_suffix"]
TWO_PASS = [f"two_{a}_{b}_prune" for a in (32, 128) for b in (8, 128)]


def source(name, seed):
    suite, policy = SEEDS[seed]
    return Path("target/pair-segmentation-" + suite) / name / "whole-shape_classes" / (policy + ".lfc2")


def run(args):
    digest = hashlib.sha256(Path(args.binary).read_bytes()).hexdigest()
    manifest = dict(binary=digest, seeds=SEEDS, policies=POLICIES, two_pass=TWO_PASS)
    path = args.root / "manifest.json"
    if path.exists():
        assert json.loads(path.read_text()) == json.loads(json.dumps(manifest)), "changed experiment: use fresh root"
    else:
        path.write_text(json.dumps(manifest, indent=2) + "\n")
        shutil.copyfile(args.binary, args.root / "three_level_segments")
        (args.root / "three_level_segments").chmod(0o755)
    binary = str(args.root / "three_level_segments")

    def job(case):
        name, seed = case
        folder = args.root / name / seed
        folder.mkdir(parents=True, exist_ok=True)
        log = folder / "screen.log"
        if log.exists() and "test result: ok." in log.read_text():
            return
        env = {k: v for k, v in os.environ.items() if not k.startswith(("ORDER_", "THREE_"))}
        env.update(ORDER_DATASET=name, ORDER_INPUT_CIRCUIT=str(source(name, seed)), THREE_SEED=seed,
                   THREE_OUTPUT=str(folder), THREE_POLICIES=",".join(POLICIES + (TWO_PASS if seed == "reuse" else [])))
        with log.open("w") as out:
            subprocess.run([binary, "three_level_sweep", "--exact", "--ignored", "--nocapture"],
                           env=env, stdout=out, stderr=subprocess.STDOUT, check=True)
        print("DONE", name, seed, flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        list(pool.map(job, [(name, seed) for seed in SEEDS for name in DATASETS]))


def summary(args):
    rows, baselines = [], []
    for log in sorted(args.root.glob("*/*/screen.log")):
        assert "test result: ok." in log.read_text(), log
        baselines.extend(records(log, "THREE_BASE"))
        for row in records(log, "THREE_SIZE"):
            row["path"] = str(log.parent / (row["policy"] + ".l3e"))
            assert Path(row["path"]).stat().st_size == int(row["raw"])
            rows.append(row)
    def write(path, data):
        with path.open("w") as out:
            writer = csv.DictWriter(out, fieldnames=list(data[0]))
            writer.writeheader()
            writer.writerows(data)
    write(args.root / "sizes.csv", rows)
    write(args.root / "baselines.csv", baselines)
    assert len(rows) == 4 * (4 * len(POLICIES) + len(TWO_PASS))
    for name in DATASETS:
        best = sorted((r for r in rows if r["dataset"] == name), key=lambda r: int(r["z22"]))[:6]
        print(name, [(r["seed"], r["policy"], r["raw"], r["z22"], r["segment_ms"]) for r in best])


def archives(args):
    rows = list(csv.DictReader((args.root / "sizes.csv").open()))
    lookup = {(r["dataset"], r["seed"], r["policy"]): r for r in rows}
    profiles = sorted({(r["seed"], r["policy"]) for r in rows})
    binary = str(args.root / "three_level_segments")
    folder = args.root / "archives"
    folder.mkdir(exist_ok=True)
    def job(key):
        log = folder / ("--".join(key) + ".log")
        if not log.exists() or "test result: ok." not in log.read_text():
            env = dict(os.environ, ORDER_SIG=lookup["mdoc_sig", *key]["path"], ORDER_HASH=lookup["mdoc_hash2", *key]["path"])
            with log.open("w") as out:
                subprocess.run([binary, "three_level_archive", "--exact", "--ignored", "--nocapture"], env=env,
                               stdout=out, stderr=subprocess.STDOUT, check=True)
        archive, = records(log, "THREE_ARCHIVE")
        row = dict(seed=key[0], policy=key[1])
        for name in DATASETS:
            for metric in ("raw", "z16", "z22", "segment_ms"):
                row[name + "_" + metric] = lookup[name, *key][metric]
        for metric in ("raw", "z16", "z22"):
            row["mdoc_" + metric] = archive[metric]
        return row
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        data = list(pool.map(job, profiles))
    with (args.root / "shared.csv").open("w") as out:
        writer = csv.DictWriter(out, fieldnames=list(data[0]))
        writer.writeheader()
        writer.writerows(data)
    for r in sorted(data, key=lambda r: int(r["mdoc_z22"]))[:8]:
        print("SHARED", r)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("run", "summary", "archives"))
    parser.add_argument("--root", type=Path, default=Path("target/three-level-v1"))
    parser.add_argument("--binary", default="target/release/deps/three_level_segments-7c64ddffa2291f48")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    args.root.mkdir(parents=True, exist_ok=True)
    {"run":run,"summary":summary,"archives":archives}[args.phase](args)
