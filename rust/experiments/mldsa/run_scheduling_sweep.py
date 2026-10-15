#!/usr/bin/env python3
"""Fixed matrix; no application-dependent scheduler or production mutations.

Screen all layouts at zstd-16. Compress saved artifacts at zstd-22 separately
without rebuilding, and build actual paired mdoc archives for chosen profiles.
Jobs are resumable only for an unchanged binary; use a new root after edits.
"""
import argparse
import concurrent.futures
import csv
import ctypes
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

DATASETS = ("mdoc_sig", "mdoc_hash2", "mldsa44", "mldsa65")
WIRES = ("none", "whole", "layer", "role", "role4", "role16")
TRAVERSALS = ("shape", "shape_classes", "shape_terms", "morton")
SEGMENTS = ("standard", "reuse", "window_16", "window_64", "window_128",
            "fixed_32", "fixed_128", "cdc_32", "cdc_128", "allphase_32",
            "allphase_64", "cdcstored_64")


def source(dataset):
    if dataset.startswith("mldsa"):
        return Path("target/plucker-grid-sf18/p4-b0-r1") / dataset / "source.lfc2"
    return Path("target/traversal-circuits") / f"{dataset}--kind_abs_lex0213_r5.lfc2"


def records(log, marker):
    return [dict(re.findall(r"(\w+)=([^\s]+)", s)) for s in log.read_text().splitlines()
            if s.startswith(marker + " ")]


def screen(args):
    digest = hashlib.sha256(Path(args.binary).read_bytes()).hexdigest()
    stamp = args.root / "binary.sha256"
    if stamp.exists():
        assert stamp.read_text().strip() == digest, "binary changed: use a new root"
    else:
        stamp.write_text(digest + "\n")
    def job(case):
        dataset, wire, traversal = case
        dest = args.root / dataset / f"{wire}-{traversal}"
        dest.mkdir(parents=True, exist_ok=True)
        log = dest / "screen.log"
        if log.exists() and "test result: ok." in log.read_text():
            assert len(records(log, "SWEEP_SIZE")) == len(SEGMENTS)
            return
        env = {k: v for k, v in os.environ.items() if not k.startswith(("ORDER_", "SWEEP_", "MLDSA_"))}
        env.update(ORDER_DATASET=dataset, ORDER_INPUT_CIRCUIT=str(source(dataset)),
                   SWEEP_WIRE=wire, SWEEP_TRAVERSAL=traversal,
                   SWEEP_SEGMENTS=",".join(SEGMENTS), SWEEP_OUTPUT=str(dest))
        start = time.monotonic()
        with log.open("w") as out:
            subprocess.run([args.binary, "scheduling_segmentation_sweep", "--exact", "--ignored", "--nocapture"],
                           env=env, stdout=out, stderr=subprocess.STDOUT, check=True)
        assert "test result: ok." in log.read_text()
        assert len(records(log, "SWEEP_SIZE")) == len(SEGMENTS)
        print("DONE", dataset, wire, traversal, round(time.monotonic() - start, 1), flush=True)
    cases = [(d, w, t) for w in WIRES for t in TRAVERSALS for d in DATASETS]
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        list(pool.map(job, cases))


def summarize(args):
    rows = []
    complete = 0
    for log in sorted(args.root.glob("*/*/screen.log")):
        if "test result: ok." not in log.read_text():
            continue
        layout, = records(log, "SWEEP_LAYOUT")
        measurements = records(log, "SWEEP_SIZE")
        assert len(measurements) == len(SEGMENTS)
        complete += 1
        for r in measurements:
            row = dict(layout, **r)
            row["path"] = str(log.parent / (r["segmentation"] + ".lfc2"))
            assert Path(row["path"]).stat().st_size == int(row["raw"])
            assert row["exact"] == "true"
            rows.append(row)
    with (args.root / "screen.csv").open("w") as out:
        if rows:
            writer = csv.DictWriter(out, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)
    print("COMPLETE", complete, "of", len(WIRES) * len(TRAVERSALS) * len(DATASETS), "layouts", len(rows), "measurements")
    return rows


def compress(args):
    rows = summarize(args)
    lib = ctypes.CDLL("libzstd.so.1")
    lib.ZSTD_compressBound.argtypes = [ctypes.c_size_t]
    lib.ZSTD_compressBound.restype = ctypes.c_size_t
    lib.ZSTD_compress.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int]
    lib.ZSTD_compress.restype = ctypes.c_size_t
    lib.ZSTD_isError.argtypes = [ctypes.c_size_t]
    lib.ZSTD_isError.restype = ctypes.c_uint
    output = args.root / "z22.json"
    results = json.loads(output.read_text()) if output.exists() else {}
    def job(row):
        path = row["path"]
        if path in results:
            return path, results[path]
        data = Path(path).read_bytes()
        buf = ctypes.create_string_buffer(lib.ZSTD_compressBound(len(data)))
        n = lib.ZSTD_compress(buf, len(buf), data, len(data), 22)
        assert not lib.ZSTD_isError(n), path
        return path, n
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        for i, (path, n) in enumerate(pool.map(job, rows)):
            results[path] = n
            if (i + 1) % 12 == 0:
                output.write_text(json.dumps(results, indent=2) + "\n")
                print("Z22", i + 1, "/", len(rows), flush=True)
    output.write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("screen", "summary", "compress"))
    parser.add_argument("--binary", default="target/release/deps/scheduling_sweep-8dc8c5930001dab1")
    parser.add_argument("--root", type=Path, default=Path("target/scheduling-segmentation-v1"))
    parser.add_argument("--workers", type=int, default=2)
    args = parser.parse_args()
    args.root.mkdir(parents=True, exist_ok=True)
    {"screen": screen, "summary": summarize, "compress": compress}[args.phase](args)
