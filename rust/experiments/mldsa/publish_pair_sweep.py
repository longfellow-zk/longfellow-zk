#!/usr/bin/env python3
"""Publish exact raw/zstd results and diagnostic LFC2 section measurements."""
import argparse
import csv
import ctypes
from pathlib import Path

ROOTS = [Path("target/pair-segmentation-" + s) for s in ("v1", "refine", "factor")]
OUT = Path("experiments/mldsa/results")
SELECTED = ["reuse", "reuse_cdcstored_64", "reuse_cdc_128", "pair_delta_repair_128",
            "pair_delta_repair_512_prune", "pair_delta_gain_32", "pair_delta_aligned_128", "pair_lz78_128",
            "pair_cdc_repair_8192_prune",
            "pair_stock_repair_8192", "reuse_pair_stock_repair_8192",
            "reuse_pair_stock_repair_65536", "dictsuffix@reuse_cdc_128",
            "dictbucketsuffix@reuse_cdc_128", "extractboth8@reuse_cdc_128",
            "dictbucketsuffix@extractprefix8@reuse_cdc_128",
            "dictbucketsuffix@extractprefix32@reuse_cdc_128",
            "dictbucketsuffix@extractprefix128@reuse_cdc_128",
            "dictbucketsuffix@extractboth8@reuse_cdc_128"]


def write_csv(path, rows):
    with path.open("w") as out:
        writer = csv.DictWriter(out, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def load():
    rows, profiles = {}, {}
    cases = 0
    for root in ROOTS:
        for row in csv.DictReader((root / "complete-sizes.csv").open()):
            cases += 1
            key = row["dataset"], row["segmentation"]
            if key in rows:
                previous = rows[key]
                for k in ("raw", "z16", "z22", "deltas", "segments", "entries", "tokens"):
                    assert row[k] == previous[k], (key, k)
                assert Path(row["path"]).read_bytes() == Path(previous["path"]).read_bytes(), key
            rows[key] = row
        for row in csv.DictReader((root / "shared-policies.csv").open()):
            key = row["segmentation"]
            if key in profiles:
                assert row == profiles[key]
            profiles[key] = row
    print("EXECUTED", cases, "UNIQUE_CIRCUITS", len(rows), "UNIQUE_POLICIES", len(profiles))
    return rows, profiles


def tables():
    rows, profiles = load()
    write_csv(OUT / "pair-segmentation-circuits.csv", list(rows.values()))
    write_csv(OUT / "pair-segmentation-shared.csv", list(profiles.values()))
    lines = ["# Pair segmentation: exact byte measurements", "",
             "All sizes are bytes, not KiB. Each cell is **raw / zstd-22**. mdoc is the actual joint LFA2 archive.", "",
             "| Policy | MLDSA44 | MLDSA65 | mdoc archive |", "|---|---:|---:|---:|"]
    for p in SELECTED:
        r = profiles[p]
        cells = [f"{int(r[d + '_raw']):,} / {int(r[d + '_z22']):,}" for d in ("mldsa44", "mldsa65", "mdoc_archive")]
        lines.append("| `" + p + "` | " + " | ".join(cells) + " |")
    lines += ["", "## Per-dataset compressed minima (not one common policy)", "",
              "| Dataset | Policy | Raw bytes | zstd-16 | zstd-22 |", "|---|---|---:|---:|---:|"]
    for name in ("mldsa44", "mldsa65", "mdoc_sig", "mdoc_hash2"):
        r = min((r for (d, p), r in rows.items() if d == name), key=lambda r: int(r["z22"]))
        lines.append(f"| {name} | `{r['segmentation']}` | {int(r['raw']):,} | {int(r['z16']):,} | {int(r['z22']):,} |")
    r = min(profiles.values(), key=lambda r: int(r["mdoc_archive_z22"]))
    lines.append(f"| mdoc archive | `{r['segmentation']}` | {int(r['mdoc_archive_raw']):,} | {int(r['mdoc_archive_z16']):,} | {int(r['mdoc_archive_z22']):,} |")
    lines += ["", "## Smallest raw circuits (not compressed winners)", "",
              "| Dataset | Policy | Raw bytes | zstd-22 |", "|---|---|---:|---:|"]
    for name in ("mldsa44", "mldsa65", "mdoc_sig", "mdoc_hash2"):
        r = min((r for (d, p), r in rows.items() if d == name), key=lambda r: int(r["raw"]))
        lines.append(f"| {name} | `{r['segmentation']}` | {int(r['raw']):,} | {int(r['z22']):,} |")
    (OUT / "pair-segmentation-tables.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


def sections():
    rows, _ = load()
    z = ctypes.CDLL("libzstd.so.1")
    z.ZSTD_compressBound.argtypes = [ctypes.c_size_t]
    z.ZSTD_compressBound.restype = ctypes.c_size_t
    z.ZSTD_compress.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int]
    z.ZSTD_compress.restype = ctypes.c_size_t
    z.ZSTD_isError.argtypes = [ctypes.c_size_t]
    z.ZSTD_isError.restype = ctypes.c_uint

    def compressed(data):
        out = ctypes.create_string_buffer(z.ZSTD_compressBound(len(data)))
        n = z.ZSTD_compress(out, len(out), data, len(data), 22)
        assert not z.ZSTD_isError(n)
        return n

    output = []
    for name in ("mldsa44", "mldsa65", "mdoc_sig", "mdoc_hash2"):
        for policy in SELECTED:
            data = Path(rows[name, policy]["path"]).read_bytes()
            assert data[:4] == b"LFC2"
            pos = 4

            def read():
                nonlocal pos
                n = shift = 0
                while True:
                    b = data[pos]
                    pos += 1
                    n |= (b & 127) << shift
                    if b < 128:
                        return n
                    shift += 7

            field, nv, nc, npub, subfield, ninput, nlayers, nconstants = (read() for _ in range(8))
            pos += nconstants * {"mldsa44": 18, "mldsa65": 18, "mdoc_sig": 32, "mdoc_hash2": 16}[name]
            for layer in range(nlayers):
                begin = pos
                logw, nw = read(), read()
                delta_start = pos
                nd = read()
                for _ in range(4 * nd):
                    read()
                segment_start = pos
                ns = read()
                entries = 0
                lengths = []
                for _ in range(ns):
                    length = read()
                    lengths.append(length)
                    entries += length
                    for _ in range(length):
                        read()
                token_start = pos
                nt = read()
                terms = sum(lengths[read()] for _ in range(nt))
                r = dict(dataset=name, segmentation=policy, layer=layer, nw=nw, terms=terms,
                         deltas=nd, segments=ns, entries=entries, tokens=nt, raw=pos-begin,
                         delta_bytes=segment_start-delta_start, segment_bytes=token_start-segment_start,
                         token_bytes=pos-token_start, layer_z22=compressed(data[begin:pos]),
                         delta_z22=compressed(data[delta_start:segment_start]),
                         segment_z22=compressed(data[segment_start:token_start]), token_z22=compressed(data[token_start:pos]))
                output.append(r)
            assert pos + 32 == len(data), (name, policy, pos, len(data))
    write_csv(OUT / "pair-segmentation-sections.csv", output)
    print("SECTION_DIAGNOSTICS", len(output), "independent zstd frames, NOT additive circuit sizes")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("tables", "sections"))
    args = parser.parse_args()
    OUT.mkdir(exist_ok=True)
    {"tables": tables, "sections": sections}[args.phase]()
