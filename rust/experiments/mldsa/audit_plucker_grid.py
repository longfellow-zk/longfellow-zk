#!/usr/bin/env python3
"""Check complete SF18 grid coverage, artifacts, duplicate schedules and provenance."""

import csv
import hashlib
import itertools
import json
from pathlib import Path
import subprocess

import run_plucker_grid as grid

HERE = Path(__file__).resolve().parent
ROOT = Path("target/plucker-grid-sf18")
RESULTS = HERE / "results/plucker-sf18"
rows = list(csv.DictReader((RESULTS / "plucker-grid-summary.csv").open()))
key = lambda r: (r["dataset"], int(r["period"]), int(r["bits"]), int(r["first"]))
expected = set(itertools.product(["mldsa44", "mldsa65"], range(1, 7), range(7), range(2)))
assert len(rows) == len(expected) == 168
assert set(map(key, rows)) == expected
assert all(r["status"] == "verified" for r in rows)


def folder(dataset, period, bits, first):
    return ROOT / f"p{period}-b{bits}-r{first}" / dataset


def circuit(dataset):
    return f"{dataset}-wire_whole-b3-w10000000-o4-shape_classes-reuse.lfc2"


for r in rows:
    dataset, p, b, first = key(r)
    d = folder(dataset, p, b, first)
    slices = (24 + p - 1) // p + int(bool(first) and p != 1)
    lane_inputs = 64 if b == 0 else (64 + b - 1) // b
    fixed = {"mldsa44": 77072, "mldsa65": 105063}[dataset]
    assert int(r["inputs"]) == fixed + 8 * slices * 25 * lane_inputs
    assert r["subfield_boundary"] == r["inputs"]
    assert (r["field_bytes"], r["subfield_bytes"]) == ("18", "3")
    assert r["sumcheck_order"] == "hand"
    assert int(r["raw"]) == (d / circuit(dataset)).stat().st_size
    assert int(r["proof"]) == (d / "proof.bin").stat().st_size
    assert int(r["peak_rss_kib"]) > 0
    config = f"period={p} first={first} bits={b}"
    for name in ["compile.log", "order.log", "timing.log", "memory.log"]:
        log = (d / name).read_text()
        assert "test result: ok." in log and "test result: FAILED" not in log
        if name != "order.log":
            assert config in log
    timed = grid.records(d / "timing.log", "ORDER_PROOF")
    fresh = grid.records(d / "memory.log", "ORDER_PROOF")
    assert len(timed) == 5 and len(fresh) == 1
    for sample in timed + fresh:
        assert sample["proof"] == r["proof"]
        assert sample["before_hwm_kib"] > 0 and sample["after_hwm_kib"] > 0

pairs = 0
for dataset, b in itertools.product(["mldsa44", "mldsa65"], range(7)):
    a, z = folder(dataset, 1, b, 0), folder(dataset, 1, b, 1)
    for name in ["source.lfc2", circuit(dataset), "proof.bin"]:
        assert (a / name).read_bytes() == (z / name).read_bytes(), (dataset, b, name)
    pairs += 1

old_path = HERE / "results/plucker-grid-summary.csv"
old = {key(r): r for r in csv.DictReader(old_path.open()) if r["status"] == "compiled"}
compared = 0
for r in rows:
    if key(r) in old:
        for field in ["inputs", "public", "wires", "terms", "layers", "deltas"]:
            assert r[field] == old[key(r)][field], (key(r), field)
        compared += 1

files = [
    "circuits/experimental/src/mldsa/algebra.rs",
    "circuits/experimental/src/mldsa/shake.rs",
    "circuits/experimental/tests/core_audit.rs",
    "circuits/experimental/tests/template_proofs.rs",
    "circuits/experimental/tests/layer_templates.rs",
    "target/release/deps/core_audit-17e41ed52dc7a8be",
    "target/release/deps/template_proofs-1eba8861353003c4",
    "target/release/deps/layer_templates-ea9ecaff61fd5f69",
    "target/release/deps/experimental_tests-1db3c8eb8c415ef4",
]
result = {
    "cells": len(rows), "timing_samples": len(rows) * 5, "fresh_memory_flows": len(rows),
    "verified_flows": len(rows) * 6, "identical_period_one_pairs": pairs,
    "unchanged_geometry_vs_previous_encoding": compared,
    "cells_exceeding_default_total_term_budget": sum(int(r["terms"]) > 20_000_000 for r in rows),
    "git_head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
    "branch": subprocess.check_output(["git", "branch", "--show-current"], text=True).strip(),
    "note": "Experimental dirty worktree; HEAD alone does not identify benchmark code.",
    "rustc": subprocess.check_output(["rustc", "--version"], text=True).strip(),
    "sha256": {p: hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in files},
}
(RESULTS / "audit.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k != "sha256"}, indent=2))
