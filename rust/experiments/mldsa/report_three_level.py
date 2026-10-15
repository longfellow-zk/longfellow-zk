#!/usr/bin/env python3
"""Publish size tables and check the dictionary-order control independently."""
import csv
import json
from pathlib import Path
import shutil

ROOT = Path("target/three-level-v1")
OUT = Path("experiments/mldsa/results")
WIDTH = dict(mldsa44=18, mldsa65=18, mdoc_sig=32, mdoc_hash2=16)


def parse(path, width, three):
    data = path.read_bytes()
    assert data[:4] == (b"L3E1" if three else b"LFC2")
    pos = 4
    def n():
        nonlocal pos
        value = 0
        for shift in range(0, 28, 7):
            b = data[pos]
            pos += 1
            value |= (b & 127) << shift
            if b < 128:
                return value
        raise ValueError("ULEB overflow")
    def seq():
        return [n() for _ in range(n())]
    def dictionary():
        return [seq() for _ in range(n())]
    for _ in range(6):
        n()
    nl, nc = n(), n()
    pos += nc * width
    layers = []
    for _ in range(nl):
        start = pos
        n(); n()
        nd = n()
        for _ in range(4 * nd):
            n()
        metadata = data[start:pos]
        lower = dictionary()
        upper = dictionary() if three else None
        roots = seq()
        layers.append((metadata, lower, upper, roots))
    assert pos + 32 == len(data)
    return layers


if __name__ == "__main__":
    OUT.mkdir(exist_ok=True)
    for src, dst in [("sizes.csv", "three-level-circuits.csv"), ("shared.csv", "three-level-shared.csv"),
                     ("baselines.csv", "three-level-baselines.csv")]:
        shutil.copyfile(ROOT / src, OUT / dst)
    rows = list(csv.DictReader((ROOT / "shared.csv").open()))
    previous = list(csv.DictReader((OUT / "pair-segmentation-shared.csv").open()))
    controls = {}
    for name, width in WIDTH.items():
        old = Path("target/pair-segmentation-refine") / name / "whole-shape_classes" / "dictbucketsuffix@reuse_cdc_128.lfc2"
        new = ROOT / name / "cdc/top_64_suffix.l3e"
        a, b = parse(old, width, False), parse(new, width, True)
        assert len(a) == len(b)
        for x, y in zip(a, b):
            assert x[0] == y[0] and x[1] == y[1], name
            # Same lower dictionary and same complete lower-reference execution.
            assert x[3] == [s for t in y[3] for s in y[2][t]], name
        controls[name] = dict(delta_table_identical=True, lower_dictionary_identical=True, expanded_references_identical=True)
    (OUT / "three-level-controls.json").write_text(json.dumps(controls, indent=2) + "\n")
    lines = ["# Three-level segmentation: exact bytes", "", "Each cell is raw / zstd-22 bytes. mdoc is a complete joint LFA2 archive.", "",
             "| Policy | MLDSA44 | MLDSA65 | mdoc |", "|---|---:|---:|---:|"]
    for policy in ["reuse_cdc_128", "dictbucketsuffix@reuse_cdc_128", "pair_delta_repair_512_prune"]:
        r, = [r for r in previous if r["segmentation"] == policy]
        cells = [f"{int(r[n + '_raw']):,} / {int(r[n + '_z22']):,}" for n in ("mldsa44", "mldsa65", "mdoc_archive")]
        lines.append("| Flat: `" + policy + "` | " + " | ".join(cells) + " |")
    for seed, policy in [("cdc", "top_64_prune"), ("cdc", "top_64_suffix"), ("cdc", "factor_128_prune"),
                         ("reuse", "two_32_128_prune"), ("factored", "top_64_prune")]:
        r, = [r for r in rows if r["seed"] == seed and r["policy"] == policy]
        cells = [f"{int(r[n + '_raw']):,} / {int(r[n + '_z22']):,}" for n in ("mldsa44", "mldsa65", "mdoc")]
        lines.append(f"| Three-level: `{seed}/{policy}` | " + " | ".join(cells) + " |")
    (OUT / "three-level-tables.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    print("CONTROL: all four lower dictionaries and expanded reference streams are identical")
