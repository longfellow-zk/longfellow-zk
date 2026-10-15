#!/usr/bin/env python3
"""Reproducible, resumable hand-major MLDSA slicing/packed-witness experiment.

Build the four release test binaries with mldsa-slicing-experiment first, then
pass their paths. Compile/order may run concurrently; measurement is serial.
Period-one first-cut on/off are the same schedule; still run both configurations.
Successful logs and circuits are retained below target/plucker-grid-sf18. No previous
experiment artifacts are modified. Changing implementation requires a new root.
The current experiment uses boundary=ninput and 18/3-byte field serialization.
"""

import argparse
import concurrent.futures
import csv
import os
from pathlib import Path
import re
import random
import statistics
import subprocess
import time


def records(path, prefix):
    result = []
    for line in path.read_text().splitlines():
        if not line.startswith(prefix + " "):
            continue
        row = dict(re.findall(r"(\w+)=([^\s]+)", line))
        for tag, high, resident in re.findall(
                r"(before|after)=VmHWM:\s*(\d+)\s+kB\s+VmRSS:\s*(\d+)\s+kB", line):
            row.pop(tag, None)
            row[tag + "_hwm_kib"] = int(high)
            row[tag + "_rss_kib"] = int(resident)
        result.append(row)
    return result


def run(command, env, log, expected):
    if log.exists() and "test result: ok." in log.read_text() and expected in log.read_text():
        return
    with log.open("w") as output:
        subprocess.run(command, env=env, stdout=output, stderr=subprocess.STDOUT, check=True)
    text = log.read_text()
    if "test result: ok." not in text or expected not in text:
        raise RuntimeError(f"Missing successful test / result in {log}")


def cell_paths(args, cell):
    dataset, period, bits, first = cell
    folder = args.root / f"p{period}-b{bits}-r{first}" / dataset
    folder.mkdir(parents=True, exist_ok=True)
    source = folder / "source.lfc2"
    circuit = folder / f"{dataset}-wire_whole-b3-w10000000-o4-shape_classes-reuse.lfc2"
    env = {k: v for k, v in os.environ.items()
           if not k.startswith("ORDER_") and not k.startswith("MLDSA_")}
    env.update(MLDSA_SLICE_PERIOD=str(period), MLDSA_PLUCKER_BITS=str(bits),
               MLDSA_FIRST_ROUND=str(first), ORDER_SUMCHECK="hand", ORDER_DATASET=dataset,
               ORDER_EXPORT_CIRCUIT=str(source), ORDER_INPUT_CIRCUIT=str(source),
               ORDER_PROOF_CIRCUIT=str(circuit), ORDER_SAVE_DIR=str(folder),
               ORDER_SAVE_PROOF=str(folder / "proof.bin"),
               ORDER_WIRE_POLICY="whole", ORDER_COMPONENTS="3", ORDER_LOCAL_ORDERS="4",
               ORDER_WINDOWS="10000000", ORDER_TRAVERSALS="shape_classes", ORDER_SEGMENTS="reuse")
    # Only locally generated grid circuits. The production reader default and
    # every per-layer/dimension bound remain unchanged.
    env["ORDER_TOTAL_TERM_LIMIT"] = "40000000"
    return folder, source, circuit, env


def compile_cell(args, cell):
    folder, source, circuit, env = cell_paths(args, cell)
    start = time.monotonic()
    run([args.compiler, "mldsa_core_bytes", "--exact", "--ignored", "--nocapture"],
        env, folder / "compile.log", "EXPORTED_CIRCUIT")
    if not source.exists():
        raise RuntimeError(f"Missing source {source}")
    run([args.orderer, "layer_template_order_sweep", "--exact", "--ignored", "--nocapture"],
        env, folder / "order.log", "ORDER_LFC2")
    if not circuit.exists():
        raise RuntimeError(f"Missing circuit {circuit}")
    print(f"COMPILED {cell} elapsed={time.monotonic()-start:.1f}s", flush=True)


def measure_cell(args, cell):
    folder, _, circuit, env = cell_paths(args, cell)
    if not circuit.exists():
        raise RuntimeError(f"Missing circuit {circuit}; run compile phase first")
    command = [args.prover, f"{cell[0]}_template_proof", "--exact", "--ignored", "--nocapture"]
    env["ORDER_REPEATS"] = str(args.repeats)
    run(command, env, folder / "timing.log", "ORDER_PROOF")
    measurements = records(folder / "timing.log", "ORDER_PROOF")
    if len(measurements) != args.repeats:
        raise RuntimeError(f"Unexpected timing repeat count in {folder}")
    env["ORDER_REPEATS"] = "1"
    run(["/usr/bin/time", "-v", *command], env, folder / "memory.log", "Maximum resident set size")
    print(f"MEASURED {cell} proof={measurements[0]['proof']} "
          f"prover_ms={statistics.median(float(r['total_prover_ms']) for r in measurements):.3f}", flush=True)


def check_cell(args, cell):
    folder, _, _, env = cell_paths(args, cell)
    # Filter includes native and compiled-witness acceptance/corruption checks.
    run([args.tests, "mldsa_shake::", "--nocapture", "--test-threads=1"],
        env, folder / "shake-tests.log", "3 passed")
    print(f"CHECKED {cell}", flush=True)


def summarize(args, cells):
    rows = []
    timings = []
    for cell in cells:
        folder, _, circuit, _ = cell_paths(args, cell)
        row = dict(zip(["dataset", "period", "bits", "first"], cell))
        row["packing"] = "balanced_lane"
        row["sumcheck_order"] = "hand"
        row["wire_policy"] = "whole"
        row["traversal"] = "shape_classes"
        row["segmentation"] = "reuse"
        row["status"] = "incomplete"
        try:
            compiled, = records(folder / "compile.log", "EXPORTED_CIRCUIT")
            sizes, = records(folder / "order.log", "ORDER_LFC2")
            lfc1, = records(folder / "order.log", "ORDER_LFC1")
            for key in ["inputs", "public", "terms", "wires", "layers", "subfield_boundary"]:
                row[key] = int(compiled[key])
            assert row["subfield_boundary"] == row["inputs"]
            row["field_bytes"] = 18
            row["subfield_bytes"] = 3
            row["default_total_term_budget"] = int(row["terms"] <= 20_000_000)
            for key in ["raw", "z16", "z22", "deltas", "segments", "tokens"]:
                row[key] = int(sizes[key])
            assert row["raw"] == circuit.stat().st_size
            row["lfc1_raw"] = int(lfc1["raw"])
            row["lfc1_z22"] = int(lfc1["z22"])
            row["decode_ms"] = float(sizes["decode_ms"])
            row["status"] = "compiled"
            measurements = records(folder / "timing.log", "ORDER_PROOF")
            if len(measurements) != args.repeats:
                raise ValueError("Timing cell is not complete yet")
            fresh, = records(folder / "memory.log", "ORDER_PROOF")
            for key in ["proof", "witnesses", "constraints", "block_enc"]:
                values = {int(r[key]) for r in measurements + [fresh]}
                assert len(values) == 1
                row[key] = values.pop()
            assert row["proof"] == (folder / "proof.bin").stat().st_size
            for key in ["total_prover_ms", "verify_ms", "commit_ms", "prove_ms", "load_ms"]:
                row[key] = statistics.median(float(r[key]) for r in measurements)
            memory = (folder / "memory.log").read_text()
            row["peak_rss_kib"] = int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", memory)[1])
            row["repeats"] = args.repeats
            row["status"] = "verified"
            for r in measurements:
                timings.append({**dict(zip(["dataset", "period", "bits", "first"], cell)), **r})
        except (OSError, ValueError):
            pass
        rows.append(row)
    args.results.mkdir(parents=True, exist_ok=True)
    for name, data in [("plucker-grid-summary.csv", rows), ("plucker-grid-timings.csv", timings)]:
        if data:
            keys = list(dict.fromkeys(k for row in data for k in row))
            with (args.results / name).open("w") as output:
                writer = csv.DictWriter(output, keys)
                writer.writeheader()
                writer.writerows(data)
    print(f"SUMMARY rows={len(rows)} verified={sum(r['status']=='verified' for r in rows)}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["compile", "measure", "check", "summary"])
    parser.add_argument("--root", type=Path, default=Path("target/plucker-grid-sf18"))
    parser.add_argument("--results", type=Path, default=Path("experiments/mldsa/results/plucker-sf18"))
    parser.add_argument("--compiler", default="target/release/deps/core_audit-17e41ed52dc7a8be")
    parser.add_argument("--orderer", default="target/release/deps/layer_templates-ea9ecaff61fd5f69")
    parser.add_argument("--prover", default="target/release/deps/template_proofs-1eba8861353003c4")
    parser.add_argument("--tests", default="target/release/deps/experimental_tests-1db3c8eb8c415ef4")
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--seed", type=int, default=20260912)
    parser.add_argument("--periods", default="1,2,3,4,5,6")
    parser.add_argument("--bits", default="0,1,2,3,4,5,6")
    parser.add_argument("--first", default="0,1")
    parser.add_argument("--datasets", default="mldsa44,mldsa65")
    args = parser.parse_args()
    cells = [(dataset, int(period), int(bits), int(first))
             for bits in args.bits.split(",") for period in args.periods.split(",")
             for first in args.first.split(",") for dataset in args.datasets.split(",")]
    if args.phase == "summary":
        summarize(args, cells)
    elif args.phase == "measure":
        execution_order = cells.copy()
        random.Random(args.seed).shuffle(execution_order)
        for i, cell in enumerate(execution_order, 1):
            measure_cell(args, cell)
            if i % 12 == 0:
                summarize(args, cells)
        summarize(args, cells)
    else:
        work = compile_cell if args.phase == "compile" else check_cell
        if args.phase == "check":
            cells = [c for c in cells if c[0] == args.datasets.split(",")[0]]
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            list(pool.map(lambda cell: work(args, cell), cells))


if __name__ == "__main__":
    main()
