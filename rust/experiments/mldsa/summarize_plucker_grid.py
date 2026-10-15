#!/usr/bin/env python3
"""Generate the balanced-plucker report from the complete measured CSV grid."""

import csv
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROWS = list(csv.DictReader((HERE / "results/plucker-sf18/plucker-grid-summary.csv").open()))
assert len(ROWS) == 168 and all(r["status"] == "verified" for r in ROWS)
for row in ROWS:
    for key in ["period", "bits", "first", "raw", "z22", "proof", "peak_rss_kib",
                "wires", "terms", "layers", "inputs", "deltas"]:
        row[key] = int(row[key])
    for key in ["total_prover_ms", "verify_ms"]:
        row[key] = float(row[key])
INDEX = {(r["dataset"], r["period"], r["bits"], r["first"]): r for r in ROWS}


def pair(p, b, first):
    return [INDEX[d, p, b, first] for d in ["mldsa44", "mldsa65"]]


def table(rows):
    text = ["| Circuit | Period | Max bits | Round 0 special | LFC2 bytes | zstd-22 bytes | Proof bytes | Prover ms | Verifier ms | Peak MiB |",
            "|---|---:|---:|:---:|---:|---:|---:|---:|---:|---:|"]
    for r in rows:
        text.append(f"| {r['dataset']} | {r['period']} | {r['bits']} | {'yes' if r['first'] else 'no'} | "
                    f"{r['raw']:,} | {r['z22']:,} | {r['proof']:,} | {r['total_prover_ms']:,.1f} | "
                    f"{r['verify_ms']:,.1f} | {r['peak_rss_kib']/1024:.1f} |")
    return "\n".join(text)


settings = [(p, b, first) for p in range(1, 7) for b in range(7)
            for first in range(2) if not (p == 1 and first == 1)]
feasible = [s for s in settings if all(r["z22"] <= 500_000 for r in pair(*s))]
smallest_proof = min(feasible, key=lambda s: sum(r["proof"] for r in pair(*s)))
fastest = min(feasible, key=lambda s: sum(r["total_prover_ms"] for r in pair(*s)))
smallest_circuit = min(settings, key=lambda s: sum(r["z22"] for r in pair(*s)))
selected = list(dict.fromkeys([(4, 0, 1), (6, 0, 0), (6, 0, 1), smallest_proof, fastest, smallest_circuit]))
text = ["# Balanced plucker / unroll grid (hand-major, full subfield inputs, 18/3-byte fields)", "",
        "## Scope and measurement", "",
        "168 configurations: MLDSA-44 and MLDSA-65 × periods 1–6 × maximum packed widths 0–6 × round-0 special off/on. "
        "Width 0 is the original direct XOR-basis witness. All circuits use the same whole / shape_classes / reuse LFC2 ordering; "
        "all proving and verification is hand-major. No Morton control or per-circuit choice of ordering is used.", "",
        "All circuits set `subfield_boundary = ninput`. Every native input is checked to lie in fp24 before proving. "
        "This boundary stops at the original inputs: sumcheck pad witnesses appended by the prover remain extension-field witnesses. "
        "fp24 serializes as three little-endian bytes; fp24_6 serializes as six such coefficients (18 bytes). "
        "Noncanonical coefficients and lengths are rejected. The in-memory arithmetic representation is unchanged. "
        "The proof-geometry optimizer uses these same 18/3-byte sizes. These circuits, IDs and proofs are regenerated; "
        "old 24/4-byte artifacts are not reused or silently reinterpreted.", "",
        "Each 64-bit lane uses ceil(64 / width) pluckers, balanced to widths differing by at most one, larger first. "
        "Widths 1…6 give 64×1; 32×2; 20×3+2×2; 16×4; 12×5+1×4; 9×6+2×5. "
        "No padding bits are introduced. Decoder range assertions are retained, and decoded Boolean bits are converted to the existing XOR basis (1−2b).", "",
        "Round-0 special adds a cut after round 0 without moving regular cuts: period 6 has [0,5,11,17,23], not [0,6,12,18,23]. "
        "Period 1 already slices after round 0; both flag values were compiled and measured anyway.", "",
        "Release Rust, target-cpu=native, on the existing Ryzen 9950X host. Compilation/compression ran in parallel; "
        "proof timings ran serially after that work finished, in a fixed shuffled order (seed 20260912). Times are medians of five complete verified flows; prover includes commitment plus proving, "
        "but excludes circuit load/ID validation, native input construction and proof serialization. Verifier excludes proof parsing. "
        "Peak memory is actual process high-water RSS from a separate fresh one-flow /usr/bin/time -v run, including loading, witnesses, proving and verification. "
        "It is not an allocation estimate and does not include offline compilation. MiB = 1,048,576 bytes; the circuit target is 500,000 compressed bytes.", "",
        "Proof geometry is optimized independently by the existing Ligero geometry selector with rateinv=4 and nreq=128. "
        "The security parameters and runtime algorithms are unchanged. Every measured proof is serialized, parsed and verified. "
        "Circuit/proof sizes are measured byte counts, not geometry estimates. LFC2 is directly consumed by the hand-major prover.", "",
        "The largest packed circuits exceed the default reader's 20-million-total-term budget. The local experiment harness explicitly sets "
        "a 40-million-total-term budget via `ORDER_TOTAL_TERM_LIMIT`; the production default and all per-layer/dimension bounds are unchanged. "
        "Using these oversized cells outside the harness requires the same explicit reader configuration for trusted circuits.", "",
        "## Common-policy candidates", "",
        f"Under 500,000 bytes for both circuits: **{len(feasible)} distinct settings** (excluding duplicate period-1 flag values). "
        f"The lowest combined proof size uses `(period, bits, special) = {smallest_proof}`; "
        f"the lowest combined prover time uses `{fastest}`. These are explicit tradeoff objectives, not an adaptive encoding policy.", "",
        "For the 500 KB target, retain period 6 with a special round-0 cut and direct XOR witnesses when speed is the priority. "
        "For a modest speed/size tradeoff, period 4 with the same round-0 cut and no pluckers gives 367,947 / 377,432 compressed bytes, "
        "slightly smaller proofs, and about 5% more combined prover time than period 6. "
        "Four-bit packing with period 1 minimizes proof bytes under the shared cap, but takes about 74% more combined prover time "
        "than the period-6 unpacked configuration. Following this sweep, period 4 / special round 0 / no pluckers was selected "
        "as the default for both MLDSA circuits. Other configurations remain opt-in experiments.", "",
        table([r for s in selected for r in pair(*s)]), "",
        "### Every shared setting below the circuit-size cap", "",
        "Each setting below is fixed for both MLDSA circuits. No runtime format selection or per-circuit heuristic switching is involved.", "",
        table([r for s in feasible for r in pair(*s)]), "",
        "## Circuit-size grid", "",
        "Entries are exact zstd-22 compressed LFC2 bytes. Column = regular slice period; row = maximum plucker width. "
        "The full CSV also contains raw LFC1/LFC2, zstd-16/22, wires, terms, layers, input count, delta/segment/token counts, "
        "proof witnesses/constraints/block geometry, all timing medians and actual peak RSS.", ""]
for dataset in ["mldsa44", "mldsa65"]:
    for first in range(2):
        text += [f"### {dataset}, round 0 {'special' if first else 'ordinary'}", "",
                 "| Max bits | 1 | 2 | 3 | 4 | 5 | 6 |", "|---:|---:|---:|---:|---:|---:|---:|"]
        for b in range(7):
            text.append("| " + " | ".join([str(b)] + [f"{INDEX[dataset,p,b,first]['z22']:,}" for p in range(1,7)]) + " |")
        text.append("")
text += ["## Geometry of selected settings", "",
         "| Circuit | Period | Max bits | Special | Input wires | Total wires | Terms | Layers | Delta-table entries (sum) |",
         "|---|---:|---:|:---:|---:|---:|---:|---:|---:|"]
for s in selected:
    for r in pair(*s):
        text.append(f"| {r['dataset']} | {r['period']} | {r['bits']} | {r['first']} | {r['inputs']:,} | "
                    f"{r['wires']:,} | {r['terms']:,} | {r['layers']} | {r['deltas']:,} |")
text += ["", "## Interpretation", "",
         "Packing reduces SHAKE state inputs from 1,600 per cut/permutation to 25×ceil(64/width). "
         "There are eight SHAKE permutations in each fixture. Its cost is the plucker's interpolation and range polynomials: "
         "the latter has degree 2^width, so larger widths can increase terms and depth substantially. "
         "Balancing avoids one anomalously small final decoder without changing the number of witnesses. "
         "All state computation remains in the XOR basis; this is an input encoding experiment, not a change of SHAKE basis.", "",
         "Proof byte counts need not vary monotonically with width or period: they depend on both witness count and circuit depth, "
         "with discrete block-size choices by the existing geometry optimizer. "
         "Round-0 slicing trades another witness boundary for more uniform later SHAKE chunks. "
         "Overrides of the selected period-4 / special-round-0 / no-plucker default remain opt-in in the experimental MLDSA module. The requested full-subfield boundary and compact field serialization "
         "also apply to default MLDSA builds; mdoc and the production reader's default resource limits are unchanged.", "",
         "## Effect of the corrected assumptions", "",
         "For period 6 / unpacked XOR witnesses / special round 0, the previous measured proof sizes (boundary 0, 24/4-byte encoding) "
         "were 694,424 bytes for MLDSA-44 and 759,256 bytes for MLDSA-65. The new measured sizes are "
         f"{INDEX['mldsa44',6,0,1]['proof']:,} and {INDEX['mldsa65',6,0,1]['proof']:,} bytes respectively. "
         "This is the combined effect of the correct subfield metadata, compact field encoding and geometry selected with those byte sizes; "
         "it is not a wire/term reduction. See the [previous experiment](FIRST_ROUND_SLICE_REPORT.md) for the historical measurements.", "",
         "## Validation and artifacts", "",
         "- All 84 schedule/packing combinations passed the three SHAKE tests (252 tests), including compiled witness acceptance and valid-point corruption rejection. Packed cases also reject the excluded lookup point.",
         "- All 54 non-ignored MLDSA tests passed at balanced width 6 / period 6 / special round 0; all 42 ordering tests passed. Compact serialization tests cover exact bytes, all coefficients, malformed lengths and nonzero word padding.",
         "- At grid measurement time, four default-build schedule/packing tests passed with deliberately conflicting experiment environment variables using the then-default unpacked period 6. The selected default was changed afterward to period 4 with a special round-0 cut and no pluckers.",
         "- After selecting the new default, all 54 non-ignored MLDSA tests, four schedule/packing tests (with conflicting environment variables), and both full C++-vector circuit evaluations passed. Fresh default builds of both circuits are byte-identical to the saved p4-b0-r1 source.lfc2 grid artifacts. The no-default-features library check also passed.",
         "- Workspace all-target/all-feature cargo check passed.",
         "- All 14 core-proto tests passed, including default-reader budget and exact/lowered budget checks for both LFC1 and LFC2.",
         "- LFC2 reorder preserves each circuit's term multiset under internal-wire renaming; inputs and outputs are fixed. Every saved LFC2 is decoded, byte-round-tripped and circuit-ID checked.",
         "- 168 × (five timing flows + one fresh-memory flow) = 1,008 successful proof/verifier flows.", "",
         "The [artifact audit](results/plucker-sf18/audit.json) verifies complete coverage, the input-count formula, all configured boundaries, "
         "proof byte counts, and exact source/circuit/proof equality for all 14 period-1 flag pairs. "
         "All 101 available old/new comparisons retain the same inputs, wires, terms, layers and delta-table counts. "
         "Eleven oversized cells need the explicit higher reader budget; none is a shared under-500-KB candidate.", "",
         "[Full grid](results/plucker-sf18/plucker-grid-summary.csv) · [Every timing sample](results/plucker-sf18/plucker-grid-timings.csv) · "
         "[Runner](run_plucker_grid.py) · [Report generator](summarize_plucker_grid.py) · [Auditor](audit_plucker_grid.py)", "",
         "Raw per-cell logs, proofs and LFC2 artifacts: `target/plucker-grid-sf18/p{period}-b{bits}-r{first}/{dataset}/`. "
         "Run `run_plucker_grid.py compile`, then `measure`, then this report generator. "
         "The runner accepts explicit release test binary paths; build with `--features mldsa-slicing-experiment` first. "
         "Use a new artifact root after changing the implementation; successful cells are otherwise reused.", ""]
(HERE / "PLUCKER_GRID_REPORT.md").write_text("\n".join(text))
print(f"Wrote report: smallest_proof={smallest_proof} fastest={fastest} smallest_circuit={smallest_circuit}")
