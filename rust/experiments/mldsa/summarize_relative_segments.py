#!/usr/bin/env python3
"""Summarize the complete representative-based LFR1 measurements."""
import csv
from pathlib import Path

here = Path(__file__).resolve().parent
rows = list(csv.DictReader((here / "results/relative-segments.csv").open()))
base = {r["dataset"]: r for r in rows if r["kind"] == "REL_BASE"}
rank = {r["dataset"]: r for r in rows if r["kind"] == "REL_RANK_CONTROL"}
variants = {(r["dataset"], r["variant"]): r for r in rows if r["kind"] == "REL_RESULT"}
assert len(variants) == 112
def num(row, key): return f"{int(row[key]):,}"
datasets = ["mldsa44", "mldsa65", "mdoc_hash2", "mdoc_sig"]
text = ["# Relative segment references: ID-preserving LFR1 experiment", "",
"## Decision", "",
"Keep the selected MLDSA policy: period 4, special round 0, no pluckers, hand-major. Do not promote LFR1 to a production format on this evidence. "
"It can coalesce boundary entries, but does not remove their coordinate information. The small current-MLDSA byte savings do not carry over to mdoc. "
"All changes in this experiment are isolated to experimental code; production LFC2, readers, prover/verifier, symbolic verifier, circuit-ID computation, and slicing defaults are untouched.", "",
"## What the proposed offset means", "",
"For absolute coordinates x[j], a translated run is x'[j] = x[j] + t. Therefore its interior differences are unchanged: "
"d'[j] = d[j] for j > 0. Only the entry difference from the previous run can change. Adding t to every delta instead adds (j+1)*t to absolute coordinates, "
"starting from the same incoming accumulator. This is a different (affine-ramp) relation. Both relations were tested as explicit separate codec modes, never confused or silently substituted.", "",
"The existing LFC2 delta and segment dictionaries are per layer, not per chunk. A segment reference is reusable only if its entire corrected delta sequence, "
"including coefficient indices and duplicate multiplicity, agrees exactly. No graph inference, term reordering, wire renumbering, input changes, or approximate matching is used.", "",
"The historical 466,401 / 178,492 numbers compare different traversals, not a measured partition into interior and boundary deltas. "
"The saved shape-first control has 179,844 deltas. Instance-boundary-aware segmentation does expose many of the whole-instance deltas as entry deltas, "
"but most of the resulting coalescing is singleton segments: their coordinates move into the three offset integers.", "",
"## Format and implementation", "",
"LFR1 is a tagged experimental container with the exact original LFC2 geometry/constant header and original 32-byte circuit ID. For each layer it stores:", "",
"1. Layer dimensions, a delta dictionary, and a dictionary of core segments (delta-index sequences).",
"2. References encoded as `(core_id << 1) | has_offset`; nonzero offsets add three signed ZigZag/ULEB integers. Coefficients are not offset.",
"3. Either references inline in execution order, or a deduplicated reference table plus ordinary integer execution tokens.", "",
"The encoder groups segments by exact equality after removing their entry coordinates (or the common delta shift in the affine control). "
"It then uses an actual first representative, rather than an artificial zero-origin core. Unshared segments and uses identical to the representative have no offset payload. "
"Dictionary IDs are frequency-ranked for the indices actually written; an ordinary-LFC2 delta-ranking control is reported separately. "
"All framing, constants, dictionary indices, reference tags, offsets, execution tokens, and the ID are counted in raw and compressed sizes.", "",
"The compatibility decoder expands references into ordinary LFC2 dictionaries, not a flat array of all executed terms. The current prover still consumes its existing compact Layer representation. "
"This prototype saves serialized bytes only, not the expanded delta dictionary's in-memory space. It uses offline/load-time hash tables; none is added to proving or verification. "
"A future direct LFR1 layer iterator would require integration and hardening and has not been implemented or performance-claimed here.", "",
"## Current circuits", "",
"Exact bytes, standalone zstd level 22. MLDSA uses the measured whole / shape_classes / reuse LFC2 layout at the selected slicing configuration. "
"mdoc uses the saved two-attribute hash and signature controls. These are individual circuit sizes, not a sum intended to predict an archive's compressed size.", "",
"| Circuit | LFC2 raw | LFC2 z22 | Relative inline raw | Relative inline z22 | Relative pooled raw | Relative pooled z22 |",
"|---|---:|---:|---:|---:|---:|---:|"]
for d in datasets:
    b, i, p = base[d], variants[d,"first-inline-w0"], variants[d,"first-pool-w0"]
    text.append(f"| {d} | {num(b,'raw')} | {num(b,'z22')} | {num(i,'raw')} | {num(i,'z22')} | {num(p,'raw')} | {num(p,'z22')} |")
text += ["", "### What actually coalesces", "",
"`Boundary-only` counts distinct deltas appearing at existing segment starts and nowhere in interiors. "
"`Merged multi-term segments` excludes the trivial sharing of single-term segments with equal coefficients.", "",
"| Circuit | Original deltas | Boundary-only | Relative core deltas | Merged multi-term segments | Pooled offset bytes | Inline offset bytes |",
"|---|---:|---:|---:|---:|---:|---:|"]
for d in datasets:
    b, i, p = base[d], variants[d,"first-inline-w0"], variants[d,"first-pool-w0"]
    text.append(f"| {d} | {num(b,'deltas')} | {num(b,'boundary_only')} | {num(p,'deltas')} | {num(p,'shared_nontrivial')} | {num(p,'offset_bytes')} | {num(i,'offset_bytes')} |")
text += ["", "### No-format-change control", "",
"Reindex the original delta dictionary by serialized-reference frequency, with no new reference encoding and no ID change:", "",
"| Circuit | Original z22 | Reindexed LFC2 raw | Reindexed LFC2 z22 |", "|---|---:|---:|---:|"]
for d in datasets:
    text.append(f"| {d} | {num(base[d],'z22')} | {num(rank[d],'raw')} | {num(rank[d],'z22')} |")
text += ["", "## Historical whole-instance hypothesis", "",
"These controls retain period 6, the historical 24/4-byte field encoding and original IDs. "
"A read-only historical serialization adapter recomputes and checks the original IDs; no old file is reinterpreted as an 18-byte field circuit.", "",
"| Traversal / segmentation | Original deltas | Boundary-only | Relative core deltas | Original raw / z22 | Inline relative raw / z22 | Pooled relative raw / z22 |",
"|---|---:|---:|---:|---:|---:|---:|"]
for label in ["whole", "shape", "boundary32", "boundary128"]:
    d="historical44_"+label; b=base[d]; p=variants[d,"first-pool-w0"]; i=variants[d,"first-inline-w0"]
    text.append(f"| {label} | {num(b,'deltas')} | {num(b,'boundary_only')} | {num(p,'deltas')} | {num(b,'raw')} / {num(b,'z22')} | {num(i,'raw')} / {num(i,'z22')} | {num(p,'raw')} / {num(p,'z22')} |")
text += ["", "The boundary-aware files have the exact same term order and ID as the whole-instance file; only their segmentation differs. "
"They establish that boundary/jump entries are a real contributor. With boundary32 and inline references, the historical whole traversal improves from 1,932,323 "
"to 1,518,288 compressed bytes (or from 2,105,889 for its boundary32 LFC2 representation). This is a real win, but still worse than the historical shape-first "
"control at 1,023,325 bytes. The reference overhead is proportional to the number of distinct segment references, "
"not eight SHAKE permutations or a small number of complete template instances:", "",
"| Boundary segmentation | Original segments | Core segments | Pooled references | Merged multi-term segments | Offset + reference-tag bytes | Token bytes |",
"|---|---:|---:|---:|---:|---:|---:|"]
for label in ["boundary32", "boundary128"]:
    p=variants["historical44_"+label,"first-pool-w0"]
    text.append(f"| {label} | {num(p,'original_segments')} | {num(p,'cores')} | {num(p,'references')} | {num(p,'shared_nontrivial')} | {num(p,'reference_bytes')} | {num(p,'token_bytes')} |")
text += ["", "A 3-integer reference is sufficient for a genuinely translated segment, but it is not an encoding of an arbitrary input/output map. "
"Fixed inputs, constant wires, and non-translation instance mappings can alter interior differences and force additional segments. "
"Thus the proposed ~200 bytes per complete instance cannot be assumed from delta-table cardinalities.", "",
"## Sweep coverage and verification", "",
"112 variants: first-delta and all-delta corrections; inline and pooled references; existing segmentation and fixed stream chunks of 8/32/128 where applicable. "
"The exact same terms, coordinates, input hands, coefficients, multiplicities, layer dimensions, constants, and ID are checked after every decode. "
"Four unit tests cover translation versus affine behavior, shared-port/coefficient mismatches, negatives, duplicates, empty segments, truncation, invalid indices and mode tags. "
"Current source-circuit controls (before the offline whole/shape_classes/reuse ordering) are also included in the CSV.", "",
"### Best compressed candidate observed per fixture (diagnostic, not an adaptive policy)", "",
"| Fixture | Variant | Raw | z22 |", "|---|---|---:|---:|"]
for d in base:
    best=min((r for (name,_),r in variants.items() if name==d),key=lambda r:int(r["z22"]))
    text.append(f"| {d} | {best['variant']} | {num(best,'raw')} | {num(best,'z22')} |")
text += ["", "## Decoder and proof checks", "",
"Size-sweep jobs overlap; encode/decode timing columns in the sweep CSV are diagnostics only. "
"Separate serial loader measurements below use seven repetitions, median, excluding circuit-ID hashing for both paths. "
"The relative measurement includes reference expansion, LFC2 serialization, and the normal reader; it measures the compatibility adapter, not an optimized direct LFR1 decoder.", "",
"| Circuit | LFC2 decode ms | Relative adapter + decode ms |", "|---|---:|---:|"]
root = Path("target/relative-segments-representative")
for d in datasets:
    lines=(root/f"{d}-load.log").read_text().splitlines()
    row=next(dict(v.split("=",1) for v in line.split("REL_LOAD ",1)[1].split()) for line in lines if "REL_LOAD " in line)
    text.append(f"| {d} | {row['baseline_ms']} | {row['relative_adapter_ms']} |")
for d in ["mldsa44", "mldsa65"]:
    log=(root/f"{d}-proof.log").read_text()
    assert "test result: ok." in log and "ORDER_PROOF " in log
text += ["", "Both selected MLDSA circuits were proved again after decoding pooled first-delta references. "
"The harness asserted byte-for-byte equality against the saved p4-b0-r1 proof, then parsed and verified it. "
"Proof sizes remain 218,708 / 227,852 bytes. These one-flow correctness checks are not a replacement for the earlier five-run runtime benchmarks. "
"No mdoc end-to-end proof was rerun in this experiment; its exact streams and computed circuit IDs were verified.", "",
"## Reproduction", "", "```sh",
"cargo test --release -p circuits-experimental --test relative_segments -- --nocapture",
"python3 experiments/mldsa/run_relative_segments.py",
"python3 experiments/mldsa/summarize_relative_segments.py", "```", "",
"[All size results](results/relative-segments.csv) · [Codec](relative_segments.rs) · [Runner](run_relative_segments.py)", "",
"Complete LFR1/zstd artifacts, decoded controls, and logs are in `target/relative-segments-representative`. "
"The earlier zero-base engineering controls are retained separately in `target/relative-segments-final` and `target/relative-segments-ranked`; they are not the results reported above.", ""]
(here / "RELATIVE_SEGMENTS_REPORT.md").write_text("\n".join(text))
print("Wrote relative segment report")
