#!/usr/bin/env python3
"""Causal follow-up: keep shared interiors, vary only their residual segmenter."""
import concurrent.futures
import csv
import hashlib
import json
import os
from pathlib import Path
import subprocess
from run_scheduling_sweep import DATASETS, source, records

ROOT = Path("target/scheduling-segmentation-refine")
BINARY = "target/release/deps/scheduling_sweep-8dc8c5930001dab1"
POLICIES = ("reuse_window_32", "reuse_window_16", "reuse_window_64", "reuse_window_128",
            "reuse_cdc_32", "reuse_cdc_128", "reuse_cdcstored_64", "cdc_64")


def run(name):
    folder = ROOT / name / "whole-shape_classes"
    folder.mkdir(parents=True, exist_ok=True)
    env = {k: v for k, v in os.environ.items() if not k.startswith(("SWEEP_", "ORDER_", "MLDSA_"))}
    env.update(ORDER_DATASET=name, ORDER_INPUT_CIRCUIT=str(source(name)),
               SWEEP_WIRE="whole", SWEEP_TRAVERSAL="shape_classes", SWEEP_OUTPUT=str(folder),
               SWEEP_SEGMENTS=",".join(POLICIES), SWEEP_Z22="1")
    with (folder / "screen.log").open("w") as output:
        subprocess.run([BINARY, "scheduling_segmentation_sweep", "--exact", "--ignored", "--nocapture"],
                       env=env, stdout=output, stderr=subprocess.STDOUT, check=True)
    baseline = Path("target/scheduling-segmentation-v1") / name / "whole-shape_classes" / "reuse.lfc2"
    assert (folder / "reuse_window_32.lfc2").read_bytes() == baseline.read_bytes()
    print("REFINE", name, "baseline byte-identical", flush=True)


def summarize():
    rows = []
    for log in sorted(ROOT.glob("*/*/screen.log")):
        assert "test result: ok." in log.read_text()
        layout, = records(log, "SWEEP_LAYOUT")
        measurements = records(log, "SWEEP_SIZE")
        assert len(measurements) == len(POLICIES)
        for r in measurements:
            rows.append(dict(layout, **r, path=str(log.parent / (r["segmentation"] + ".lfc2"))))
    assert len(rows) == len(DATASETS) * len(POLICIES)
    with (ROOT / "screen.csv").open("w") as out:
        writer = csv.DictWriter(out, fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)
    (ROOT / "z22.json").write_text(json.dumps({r["path"]: int(r["z22"]) for r in rows}, indent=2) + "\n")


if __name__ == "__main__":
    ROOT.mkdir(exist_ok=True)
    (ROOT / "binary.sha256").write_text(hashlib.sha256(Path(BINARY).read_bytes()).hexdigest() + "\n")
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        list(pool.map(run, DATASETS))
    summarize()
