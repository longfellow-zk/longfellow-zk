#!/usr/bin/env python3
"""Release controls: saved wire numbering, offline global Morton, stock LFC2.

Run from the Rust workspace. Build layer_templates, template_proofs and
morton_folds with --release --features mldsa-slicing-experiment first.
Size jobs may overlap; proof and fold checks are serial correctness checks,
not controlled timing or peak-memory benchmarks. Successful jobs are resumable.
"""
import argparse
import concurrent.futures
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path("target/template-morton-control")
DATASETS = ("mdoc_sig", "mdoc_hash2", "mldsa44", "mldsa65")


def source(name, layout):
    if name.startswith("mldsa"):
        folder = Path("target/plucker-grid-sf18/p4-b0-r1") / name
        return folder / ("source.lfc2" if layout == "original" else
                         f"{name}-wire_whole-b3-w10000000-o4-shape_classes-reuse.lfc2")
    if layout == "original":
        return Path("target/traversal-circuits") / f"{name}--kind_abs_lex0213_r5.lfc2"
    return Path("target/template-core-lfc2") / f"{name}-wire_whole-b3-w10000000-o4-shape_classes-reuse.lfc2"


def folder(name, layout):
    return ROOT / f"{name}-{layout}"


def morton(name, layout):
    return folder(name, layout) / f"{name}-b6-w10000000-o4-morton-standard.lfc2"


def run(binary, test, env, log, marker):
    if log.exists() and marker in log.read_text() and "test result: ok." in log.read_text():
        return
    log.parent.mkdir(parents=True, exist_ok=True)
    clean = {k: v for k, v in os.environ.items() if not k.startswith(("ORDER_", "MLDSA_"))}
    clean.update(env)
    with log.open("w") as output:
        subprocess.run([binary, test, "--exact", "--ignored", "--nocapture"],
                       env=clean, stdout=output, stderr=subprocess.STDOUT, check=True)
    assert marker in log.read_text() and "test result: ok." in log.read_text(), log
    print("PASS", log, flush=True)


def sizes(args):
    def cell(case):
        name, layout = case
        run(args.orderer, "layer_template_order_sweep", dict(
            ORDER_DATASET=name, ORDER_INPUT_CIRCUIT=str(source(name, layout)),
            ORDER_WIRE_POLICY="none", ORDER_COMPONENTS="6", ORDER_LOCAL_ORDERS="4",
            ORDER_WINDOWS="10000000", ORDER_TRAVERSALS="morton", ORDER_SEGMENTS="standard",
            ORDER_SAVE_DIR=str(folder(name, layout))), folder(name, layout) / "order.log", "ORDER_LFC2")
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        list(pool.map(cell, [(n, l) for n in DATASETS for l in ("original", "template")]))


def validate(args):
    for name in DATASETS:
        for layout in ("original", "template"):
            env = dict(ORDER_DATASET=name, ORDER_PROOF_CIRCUIT=str(morton(name, layout)))
            run(args.folds, "stored_morton_folds", env,
                folder(name, layout) / "folds.log", "MORTON_FOLDS")
            if name.startswith("mldsa"):
                env.update(MLDSA_SLICE_PERIOD="4", MLDSA_FIRST_ROUND="1", MLDSA_PLUCKER_BITS="0",
                           ORDER_SUMCHECK="round", ORDER_REPEATS="1",
                           ORDER_SAVE_PROOF=str(folder(name, layout) / "round.proof"))
                run(args.prover, name + "_template_proof", env,
                    folder(name, layout) / "proof.log", "ORDER_PROOF")
    for layout in ("original", "template"):
        for traversal in ("hand", "morton"):
            path = ROOT / f"mdoc-{layout}-{traversal}"
            get = source if traversal == "hand" else morton
            archive = path.with_suffix(".archive")
            run(args.prover, "mdoc_template_proof", dict(
                ORDER_SIG=str(get("mdoc_sig", layout)), ORDER_HASH=str(get("mdoc_hash2", layout)),
                ORDER_ATTRS="2", ORDER_SAVE_ARCHIVE=str(archive)),
                path.with_suffix(".archive.log"), "ORDER_MDOC_ARCHIVE")
            # v8's app protocol remains hand-major. Round-major compatibility is
            # checked independently on every stored layer above; do not relabel
            # this v8 circuit as v7, which would also change its witness layout.
            run(args.prover, "mdoc_template_proof", dict(
                ORDER_MDOC_ARCHIVE=str(archive), ORDER_ATTRS="2", ORDER_REPEATS="1"),
                path.with_suffix(".proof.log"), "ORDER_MDOC_PROOF")


def records(path, marker):
    return [dict(re.findall(r"(\w+)=([^\s]+)", line)) for line in path.read_text().splitlines()
            if line.startswith(marker + " ")]


def summary(args):
    rows = []
    for name in DATASETS:
        for layout in ("original", "template"):
            log = folder(name, layout) / "order.log"
            base, = records(log, "ORDER_BASE")
            result, = records(log, "ORDER_LFC2")
            lfc1, = records(log, "ORDER_LFC1")
            for traversal, data in (("hand", base), ("morton", result)):
                row = dict(dataset=name, numbering=layout, traversal=traversal,
                           segmentation="reuse" if layout == "template" and traversal == "hand" else "standard")
                for key in ("raw", "z16", "z22", "deltas", "terms", "wires", "layers"):
                    row[key] = data.get(key, base.get(key))
                if traversal == "morton":
                    row.update(lfc1_raw=lfc1["raw"], lfc1_z22=lfc1["z22"])
                rows.append(row)
    with (ROOT / "sizes.csv").open("w") as output:
        writer = csv.DictWriter(output, fieldnames=list(dict.fromkeys(k for r in rows for k in r)))
        writer.writeheader()
        writer.writerows(rows)
    archives = []
    for log in sorted(ROOT.glob("*.archive.log")):
        row, = records(log, "ORDER_MDOC_ARCHIVE")
        archives.append(dict(profile=log.name, **row))
    (ROOT / "archives.json").write_text(json.dumps(archives, indent=2) + "\n")
    paths = [source(n, l) for n in DATASETS for l in ("original", "template")]
    paths += [morton(n, l) for n in DATASETS for l in ("original", "template")]
    paths += [Path(args.orderer), Path(args.prover), Path(args.folds)]
    (ROOT / "sha256.json").write_text(json.dumps(
        {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}, indent=2) + "\n")
    for r in rows:
        print(r)
    print("ARCHIVES", archives)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("sizes", "validate", "summary"))
    parser.add_argument("--orderer", required=True)
    parser.add_argument("--prover", required=True)
    parser.add_argument("--folds", required=True)
    args = parser.parse_args()
    ROOT.mkdir(parents=True, exist_ok=True)
    {"sizes": sizes, "validate": validate, "summary": summary}[args.phase](args)
