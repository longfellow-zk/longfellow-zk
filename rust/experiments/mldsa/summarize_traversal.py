#!/usr/bin/env python3
"""Summarize measured complete LFC2 sizes, retaining aliases and provenance."""
import csv
from pathlib import Path
import sys

RESULTS = Path(__file__).resolve().parent / "results"
DATASETS = ("mldsa44", "mldsa65", "mdoc_hash2", "mdoc_sig")
BASELINE = "kind_abs_lex0213_r5"


def read_results():
    rows = {}
    for path in sorted(RESULTS.glob("traversal-*.log")):
        dataset = path.name.split("-")[1]
        for line in path.read_text().splitlines():
            parts = line.split()
            if not parts:
                continue
            if parts[0] == "SWEEP":
                row = dict(dataset=dataset, policy=parts[1], source=path.name)
                row.update((k, float(v) if k == "ms" else int(v))
                           for k, v in (p.split("=", 1) for p in parts[2:]))
                rows[dataset, parts[1]] = row
            if parts[0] == "SWEEP_DUP":
                alias = parts[2].split("=", 1)[1]
                if (dataset, alias) in rows:
                    rows[dataset, parts[1]] = dict(rows[dataset, alias], policy=parts[1])
    return rows


def main():
    rows = read_results()
    if "--csv" in sys.argv:
        writer = csv.DictWriter(sys.stdout, fieldnames=list(next(iter(rows.values()))))
        writer.writeheader()
        writer.writerows(rows.values())
        return
    for dataset in DATASETS:
        subset = sorted((r for (d, _), r in rows.items() if d == dataset),
                        key=lambda r: r["zstd16"])
        print(f"\n{dataset}: {len(subset)} policies")
        for r in subset[:12]:
            print(r["policy"], "z16", r["zstd16"], "raw", r["raw"],
                  "deltas", r["layer_deltas"], "segments", r["segments"])
    policies = {p for d, p in rows if d == DATASETS[0]}
    common = [p for p in policies if all((d, p) in rows for d in DATASETS)]
    if all((d, BASELINE) in rows for d in DATASETS):
        def score(p):
            return max(rows[d, p]["zstd16"] / rows[d, BASELINE]["zstd16"]
                       for d in DATASETS)
        print("\nShared policy ranking by worst size ratio to current (research diagnostic only):")
        for p in sorted(common, key=score)[:20]:
            print(p, *(rows[d, p]["zstd16"] for d in DATASETS), f"worst={score(p):.4f}")


if __name__ == "__main__":
    main()
