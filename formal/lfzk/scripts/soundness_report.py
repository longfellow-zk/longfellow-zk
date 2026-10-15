#!/usr/bin/env python3
"""Recompute the ZK-verifier error breakdown with exact fractions (stdlib only).

Reads the committed RBR rows, circuit profiles and Hahn coefficients. Checks the new
127-bit certificate, the hash bottleneck, and the WI factor of two. Lean remains the
authority; this report independently checks the arithmetic and README approximations.

Run from formal/: python3 lfzk/scripts/soundness_report.py
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import math
import re
import sys

import rbr_v1_rows as rbr

FORMAL = Path(__file__).resolve().parents[2]
LFZK = FORMAL / "lfzk"
sys.path.insert(0, str(FORMAL / "ligero/examples/Ligero/scripts"))
import hahn_mask_certificates as hahn  # noqa: E402


def bits(x):
    return -math.log2(x) if x else math.inf


def hahn_signature():
    source = (LFZK / "Lfzk/LigeroV1RowsHahn.lean").read_text()
    body = source.split("def v7SigHahn : Row :=", 1)[1].split("theorem", 1)[0]
    f = {key: int(value) for key, value in re.findall(r"\b(\w+) := (\d+)\b", body)}
    assert "fieldOrder := p256Order" in body
    assert "hahnMask := Ligero.Examples.Grid.LongfellowProfiledExtraction.HahnMask.v7Sig" in body
    source = (FORMAL / "ligero/examples/Ligero/Longfellow/HahnMaskCertificates.lean").read_text()
    coeffs = [int(x) for x in re.search(r"def v7Sig : List Nat :=\s*\[([^]]+)\]", source)[1].split(",")]
    bound = hahn.check(f["n"], f["maskThreshold"], 2 * f["k"] - 1, coeffs)
    assert bound is not None, "invalid Hahn certificate"
    row = rbr.Row(f["n"], f["k"], f["d"], f["e"], f["g"], f["m"], f["fieldBits"],
                  f["targetBits"], f["openings"], f["failureThreshold"],
                  f["arithmeticThreshold"], rbr.P256)
    assert f["maskThreshold"] == row.at + 1 < row.johnson_threshold
    arith = Q(row.list_bound * bound, row.field_size)
    eps = row.list_bound * (row.cover() + row.fail() + arith)
    assert rbr.certified_bits(eps) == row.target_bits == 126
    return row, arith


def breakdown(row, profile, arith=None):
    arith = row.arith() if arith is None else arith
    nl, rounds, logv = profile["nlayers"], profile["total_sumcheck_rounds"], profile["logv"]
    field = Q(row.list_bound * (nl * (logv + 2) + 2 * rounds + 1), row.field_size)
    core = field + row.fail() + arith + row.cover()
    coeff = max(Q(row.list_bound * (logv + 2), row.field_size), row.fail() + arith, row.cover())
    return field, core, coeff


def main():
    profiles = json.loads((LFZK / "scripts/v7-circuit-profiles.json").read_text())
    rows = rbr.parse_rows(LFZK / "Lfzk/LigeroV1RowsV7.lean")
    assert len(rows) == len(profiles) == 5
    data = []
    print("row          field bits   Ligero bits   core bits   coefficient bits")
    for row, profile in zip(rows, profiles):
        assert (row.n, row.k, row.openings) == (profile["ligero_n"], profile["ligero_k"], profile["nreq"])
        name = "v7Sig" if profile["component"] == "sig" else f'v7Hash{profile["attributes"]}'
        field, core, coeff = breakdown(row, profile)
        data.append((row, profile, core, coeff))
        print(f"{name:12} {bits(field):10.5f} {bits(row.fail()+row.arith()+row.cover()):13.5f}"
              f" {bits(core):11.5f} {bits(coeff):18.5f}")
        if profile["component"] == "hash":
            assert core > Q(1, 2**116)
            assert Q(row.list_bound * 2 * profile["total_sumcheck_rounds"], row.field_size) > Q(1, 2**117)

    row, arith = hahn_signature()
    profile = profiles[0]
    assert profile["component"] == "sig"
    field, core, coeff = breakdown(row, profile, arith)
    print(f"{'v7SigHahn':12} {bits(field):10.5f} {bits(row.fail()+arith+row.cover()):13.5f}"
          f" {bits(core):11.5f} {bits(coeff):18.5f}")
    fc, length, cutoff = 2 * row.n, profile["nlayers"] + profile["total_sumcheck_rounds"] + 3, 2**127
    eps = Q(1, 2**127)
    assert core + Q(fc * (1 + length), 2**256) <= eps
    assert coeff + Q(fc + cutoff, 2**256) <= eps
    assert Q(3 * cutoff + 2 * fc + 1 + length, 2**256) <= eps
    assert core > Q(1, 2**128)
    assert core < data[0][2]
    print("127-bit T-security: all three exact slack inequalities pass")
    print("\ntwo-field core bits (old signature -> Hahn signature):")
    for _, profile, hash_core, hash_coeff in data[1:]:
        shared_old = hash_core + data[0][2] + Q(1, 2**128)
        shared_new = hash_core + core + Q(1, 2**128)
        separate_old = hash_core + data[0][2] + Q(4, 2**128)
        separate_new = hash_core + core + Q(4, 2**128)
        assert shared_new < shared_old and separate_new < separate_old
        assert max(hash_coeff, data[0][3], Q(4, 2**128)) == max(hash_coeff, coeff, Q(4, 2**128))
        assert separate_new <= Q(651, 1000 * 2**115)
        print(f'  {profile["attributes"]} attributes: shared MAC {bits(shared_old):.5f} -> '
              f'{bits(shared_new):.5f}; separate MAC {bits(separate_old):.5f} -> '
              f'{bits(separate_new):.5f}; integer target remains 115')

    errors = [Q(4*r.n**2 + (2*r.n-1)*(2*r.n-2) + 2*(r.n-r.openings)*2**115, 2**256) for r in rows]
    assert all(e <= Q(1, 2**128) for e in errors)
    assert all(2 * (errors[0] + e) <= Q(1, 2**126) for e in errors[1:])
    print("\nAt 2^115 Merkle queries: WI <= 2^-127 per side, <= 2^-126 for two fields")


if __name__ == "__main__":
    main()
