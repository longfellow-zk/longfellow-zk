#!/usr/bin/env python3
"""Build jointly compressed mdoc archives and compare fixed shared policies."""
import argparse
import concurrent.futures
import csv
import json
import os
from pathlib import Path
import re
import subprocess

DATASETS = ("mdoc_sig", "mdoc_hash2", "mldsa44", "mldsa65")


def records(log, marker):
    return [dict(re.findall(r"(\w+)=([^\s]+)", s)) for s in log.read_text().splitlines()
            if s.startswith(marker + " ")]


def key(row):
    return (row["wire"], row["traversal"], row["segmentation"])


def archives(args):
    rows = list(csv.DictReader((args.root / "screen.csv").open()))
    profiles = {key(r) for r in rows}
    paths = {(r["dataset"], key(r)): r["path"] for r in rows}
    def job(profile):
        if any((name, profile) not in paths for name in DATASETS[:2]):
            return
        stem = args.root / "archives" / "--".join(profile)
        stem.parent.mkdir(exist_ok=True)
        log = stem.with_suffix(".log")
        if log.exists() and "test result: ok." in log.read_text():
            return
        env = {k: v for k, v in os.environ.items() if not k.startswith("ORDER_")}
        env.update(ORDER_SIG=paths["mdoc_sig", profile], ORDER_HASH=paths["mdoc_hash2", profile],
                   ORDER_ATTRS="2", ORDER_SAVE_ARCHIVE=str(stem.with_suffix(".archive")))
        with log.open("w") as output:
            subprocess.run([args.prover, "mdoc_template_proof", "--exact", "--ignored", "--nocapture"],
                           env=env, stdout=output, stderr=subprocess.STDOUT, check=True)
        assert "test result: ok." in log.read_text(), log
        print("ARCHIVE", "--".join(profile), flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        list(pool.map(job, sorted(profiles)))


def summary(args):
    rows = list(csv.DictReader((args.root / "screen.csv").open()))
    z22 = json.loads((args.root / "z22.json").read_text())
    by_key = {}
    for row in rows:
        row["z22"] = z22[row["path"]]
        by_key[row["dataset"], key(row)] = row
    with (args.root / "complete-sizes.csv").open("w") as out:
        writer = csv.DictWriter(out, fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)
    profiles = sorted({key(r) for r in rows})
    combined = []
    for profile in profiles:
        if any((name, profile) not in by_key for name in DATASETS):
            continue
        log = args.root / "archives" / ("--".join(profile) + ".log")
        if not log.exists() or "test result: ok." not in log.read_text():
            continue
        archive, = records(log, "ORDER_MDOC_ARCHIVE")
        r = dict(zip(("wire", "traversal", "segmentation"), profile))
        for dataset in DATASETS:
            for metric in ("raw", "z16", "z22", "deltas", "segments", "entries", "tokens"):
                r[dataset + "_" + metric] = int(by_key[dataset, profile][metric])
        for metric in ("raw", "z16", "z22"):
            r["mdoc_archive_" + metric] = int(archive[metric])
        combined.append(r)
    with (args.root / "shared-policies.csv").open("w") as out:
        if combined:
            writer = csv.DictWriter(out, fieldnames=list(combined[0]))
            writer.writeheader(); writer.writerows(combined)
    base = {"mldsa44_z22": 367947, "mldsa65_z22": 377432, "mdoc_archive_z22": 156667}
    score = lambda r: (max(r[k] / v for k, v in base.items()),
                       sum(r[k] / v for k, v in base.items()))
    print("VERIFIED SIZE ROWS", len(rows), "SHARED PROFILES WITH ARCHIVES", len(combined))
    for r in sorted(combined, key=score)[:15]:
        print("COMMON", key(r), {k: r[k] for k in base}, "worst_ratio", score(r)[0])
    for dataset in DATASETS:
        r = min((r for r in rows if r["dataset"] == dataset), key=lambda r: r["z22"])
        print("INDIVIDUAL", dataset, key(r), r["raw"], r["z22"])
    for traversal in ("shape", "shape_classes", "shape_terms", "morton"):
        eligible = [r for r in combined if r["traversal"] == traversal]
        if eligible:
            r = min(eligible, key=score)
            print("TRAVERSAL", key(r), {k: r[k] for k in base})


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("archives", "summary"))
    parser.add_argument("--root", type=Path, default=Path("target/scheduling-segmentation-v1"))
    parser.add_argument("--prover", default="target/release/deps/template_proofs-1eba8861353003c4")
    parser.add_argument("--workers", type=int, default=2)
    args = parser.parse_args()
    {"archives": archives, "summary": summary}[args.phase](args)
