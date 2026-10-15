#!/usr/bin/env python3
"""The deployed **v7** rows: Ligero V1 round-by-round rows (`Lfzk.LigeroV1RowsV7`), composed
`CertifiedV1.Row`s (`Lfzk.CertifiedV7`) and two-field rows (`Lfzk.TwoFieldV7Rows`), with every
numeral their headline lemmas quote.

The v7 registry (`rust/applications/mdoc_zk/runtime/src/zk_spec.rs`, `ZK_SPECS`, version 7) uses
`ligero_config(rateinv 7, nreq 132, block_enc)` with hash `block_enc` 4151/4265/4307/4415 for 1-4
attributes and sig `block_enc` 4096.  The Ligero parameter code (`rust/runtime/ligero/src/param.rs`,
`lib/ligero/ligero_param.h`) sets `block = (block_enc + 1) / (2 + rateinv)`,
`dblock = 2 block - 1`, `block_ext = block_enc - dblock`; the Lean geometry is `k = block`,
`n = block_ext`, `w = block - nreq`.  `v7-circuit-profiles.json` (written by
`inspect_v7_circuit_profile.py` from the stored, ID-checked v7 artifacts, with the deployed
verifier's `ZkVerifier::geometry`) records both, and this script asserts that the presets of
`rbr_v1_rows.py` are exactly that geometry.

Per component the Ligero row is `rbr_v1_rows.Scanner.best` at 132 openings over the default box —
the same search that produced the v8 rows — and the composed row is `Params` (below, a
transcription of `Lfzk.CostV1.Params`) at the component's circuit profile (`nl`, `logw`, `ninp = nw[-1]`, as for v8), with `cardCand = listBound`,
`commitFuel = 2^60`, `tape = 2^62`, `sizeBound = proofBytes`, `colBytes` 2 (hash) / 32 (sig).

    v7_rows.py                 # the table: geometry, Ligero bits, composed lam, coefficients, two-field
    v7_rows.py --emit-lean     # the Lean row literals
    v7_rows.py --check         # re-derive every v7 numeral in the three Lean files

The Lean files `LigeroV1RowsV7.lean`, `CertifiedV7.lean` and `TwoFieldV7Rows.lean` carry these
rows; `--check` re-derives them.

Untrusted: every number is re-checked by `native_decide` in Lean.  `--check` catches drift.
"""

from __future__ import annotations

import argparse
import json
import math
import re
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import rbr_v1_rows as rbr  # noqa: E402

LFZK = HERE.parent / "Lfzk"
LIGERO_FILE = LFZK / "LigeroV1RowsV7.lean"
CERTIFIED_FILE = LFZK / "CertifiedV7.lean"
TWOFIELD_FILE = LFZK / "TwoFieldV7Rows.lean"
PROFILES = HERE / "v7-circuit-profiles.json"

OPENINGS = 132
DIGEST_BITS = 256
COMMIT_FUEL = 2 ** 60
TAPE = 2 ** 62
MAC_FIELD = 2 ** 128
NFULL_WIT = 1

# ---- `Lfzk.CostV1.Params`, definition for definition ----

# `Lfzk.CostV1`'s constants.
BYTES_F = 16
BYTES_H = 32


def column_field_count(nw: int, nq: int) -> int:
    """`Lfzk.CostV1.columnFieldCount`."""
    return nw + 3 * nq + 5


def paths(h: int, q: int) -> int:
    """`Lfzk.CostV1.paths h q = ∑ l ∈ Icc 1 (h-1), min q (2^l - q)`."""
    return sum(min(q, rbr.nat_sub(2 ** l, q)) for l in range(1, rbr.nat_sub(h, 1) + 1))


def merkle_numerator(commit_fuel: int, t: int) -> int:
    """`Bcs.merkleNumerator commitFuel T = commitFuel(commitFuel-1)/2 + T(2 commitFuel + 1)`."""
    return commit_fuel * rbr.nat_sub(commit_fuel, 1) // 2 + t * (2 * commit_fuel + 1)


class Params:
    """`Lfzk.CostV1.Params`."""

    def __init__(self, row: rbr.Row, q: int, nl: int, logw: list[int], logc: int,
                 digest_bits: int, ninp: int, col_bytes: int, nfull_wit: int):
        assert len(logw) == nl
        self.row, self.q, self.nl, self.logw, self.logc = row, q, nl, logw, logc
        self.digest_bits, self.ninp, self.col_bytes, self.nfull_wit = (
            digest_bits, ninp, col_bytes, nfull_wit)

    def rounds(self, ly: int) -> int:
        return 2 * self.logw[ly]

    @property
    def pad_size(self) -> int:
        return sum(4 * self.logw[ly] + 3 for ly in range(self.nl))

    @property
    def total_rounds(self) -> int:
        return sum(self.rounds(ly) for ly in range(self.nl))

    @property
    def sumcheck_elems(self) -> int:
        return sum(2 * self.rounds(ly) + 2 for ly in range(self.nl))

    @property
    def nw(self) -> int:
        return rbr.nat_div(self.ninp + self.pad_size + self.q - 1, self.q)

    @property
    def nq(self) -> int:
        return rbr.nat_div(self.nl + self.q - 1, self.q)

    def merkle_term(self, commit_fuel: int, t: int) -> Fraction:
        return Fraction(merkle_numerator(commit_fuel, t), 2 ** self.digest_bits)

    @property
    def field_density(self) -> Fraction:
        return Fraction(self.nl * 2 + self.total_rounds * 2 + 1, self.row.field_size)

    @property
    def ligero_density(self) -> Fraction:
        return (self.row.fail() + self.row.arith()) + self.row.cover()

    def nizk_bound(self, card_cand: int, commit_fuel: int, t: int) -> Fraction:
        return card_cand * (self.field_density + self.ligero_density) + self.merkle_term(commit_fuel, t)

    # size model
    @property
    def cleartext_elems(self) -> int:
        return rbr.nat_sub(4 * self.row.k + self.row.openings, 2)

    @property
    def col_rows(self) -> int:
        return column_field_count(self.nw, self.nq)

    @property
    def nfull(self) -> int:
        return 3 * self.nq + 5 + self.nfull_wit

    @property
    def column_bytes(self) -> int:
        return self.row.openings * (rbr.nat_sub(self.col_rows, self.nfull) * self.col_bytes
                                    + self.nfull * BYTES_F)

    @property
    def path_digests(self) -> int:
        return paths(self.row.n.bit_length() - 1, self.row.openings)   # `Nat.log2 n`

    @property
    def nonce_bytes(self) -> int:
        return self.row.openings * BYTES_H

    @property
    def proof_elems(self) -> int:
        return self.sumcheck_elems + self.cleartext_elems

    @property
    def proof_bytes(self) -> int:
        return (self.proof_elems * BYTES_F + self.column_bytes
                + self.path_digests * BYTES_H + self.nonce_bytes)


# (Lean name, `rbr_v1_rows` preset, profile component, attributes, colBytes)
COMPONENTS = [
    ("v7Sig", "v7sig", "sig", 0, 32),
    ("v7Hash1", "v7hash1", "hash", 1, 2),
    ("v7Hash2", "v7hash2", "hash", 2, 2),
    ("v7Hash3", "v7hash3", "hash", 3, 2),
    ("v7Hash4", "v7hash4", "hash", 4, 2),
]
# the v7 registry's Ligero configurations, `(rateinv, nreq, block_enc)`
REGISTRY = {"v7Sig": (7, 132, 4096), "v7Hash1": (7, 132, 4151), "v7Hash2": (7, 132, 4265),
            "v7Hash3": (7, 132, 4307), "v7Hash4": (7, 132, 4415)}
PAIRS = [(f"v7P256Sha{a}", "v7Sig", f"v7Hash{a}") for a in range(1, 5)]


def bits(x: Fraction) -> int:
    """Largest `t` with `x <= 2^-t`."""
    return rbr.certified_bits(x)


def lg(x: Fraction) -> float:
    return -math.log2(x) if x > 0 else math.inf


# --------------------------------------------------------------------------- #
# Derivation
# --------------------------------------------------------------------------- #

def geometry(block_enc: int, rateinv: int, nreq: int) -> tuple[int, int, int]:
    """`(n, k, w)` from a Ligero configuration, as `param.rs` computes it."""
    block = (block_enc + 1) // (2 + rateinv)
    dblock = 2 * block - 1
    return block_enc - dblock, block, block - nreq


def load_profiles() -> dict:
    out = {}
    for rec in json.loads(PROFILES.read_text()):
        out[(rec["component"], rec["attributes"])] = rec
    return out


class Component:
    def __init__(self, name, preset, comp, attrs, col_bytes, profiles):
        self.name, self.preset, self.col_bytes = name, preset, col_bytes
        p = rbr.PRESETS[preset]
        rateinv, nreq, block_enc = REGISTRY[name]
        n, k, w = geometry(block_enc, rateinv, nreq)
        assert (p["n"], p["k"]) == (n, k), (name, p, n, k)
        assert nreq == OPENINGS
        prof = profiles[(comp, attrs)]
        assert (prof["ligero_n"], prof["ligero_k"], prof["ligero_w"]) == (n, k, w), name
        assert prof["block_enc"] == block_enc and prof["nreq"] == nreq
        self.profile = prof
        scanner = rbr.Scanner(n, k, p["field_bits"], p["field_order"])
        self.row = scanner.best(OPENINGS, scanner.cells(600, 200))
        assert not self.row.valid() and self.row.sharp(), name
        self.params = Params(self.row, w, prof["nlayers"], prof["logw"], 0, DIGEST_BITS,
                                prof["nw"][-1], col_bytes, NFULL_WIT)
        self.card_cand = self.row.list_bound
        self.bound = self.params.nizk_bound(self.card_cand, COMMIT_FUEL, TAPE)
        self.lam = bits(self.bound)
        assert Fraction(1, 2 ** (self.lam + 1)) < self.bound
        self.size = self.params.proof_bytes
        # `Lfzk.CertifiedV1.Row.Valid`'s remaining conjuncts
        assert OPENINGS + w == k
        assert self.params.nw >= 1 and self.params.nq >= 1          # `CoreRowsNonempty`
        assert 2 * n + COMMIT_FUEL < TAPE
        # `NizkGrinding`'s coefficient and `NizkAdaptive`'s slack
        q = self.row.field_size
        self.densities = {"field": Fraction(2, q), "challenge": self.row.fail() + self.row.arith(),
                          "query": self.row.cover()}
        self.max_slot = max(self.densities, key=self.densities.get)
        self.max_density = self.densities[self.max_slot]
        self.fs_coeff = self.card_cand * self.max_density
        self.fs_bits = bits(self.fs_coeff)
        self.length = self.params.nl + self.params.total_rounds + 3
        self.slack_bound = self.bound + Fraction(TAPE * self.length, 2 ** DIGEST_BITS)
        self.slack_coeff = self.fs_coeff + Fraction(TAPE, 2 ** DIGEST_BITS)
        self.slack_bound_bits = bits(self.slack_bound)
        self.slack_coeff_bits = bits(self.slack_coeff)
        # the bound's three parts, for bounds of other shapes
        self.field_density_bits = bits(self.params.field_density)
        self.ligero_density_bits = bits(self.params.ligero_density)
        self.merkle_bits = bits(self.params.merkle_term(COMMIT_FUEL, TAPE))
        assert self.slack_bound_bits == self.lam, name
        assert self.slack_coeff_bits == self.fs_bits, name

    def lean_row(self) -> str:
        logw = ", ".join(map(str, self.params.logw))
        return (f"{{ params :=\n"
                f"      {{ row := Lfzk.LigeroV1Rows.{self.name}\n"
                f"        q := {self.params.q}, nl := {self.params.nl},\n"
                f"        logw := fun ly => [{logw}].getD ly 0,\n"
                f"        logc := 0, digestBits := {DIGEST_BITS}, ninp := {self.params.ninp},\n"
                f"        colBytes := {self.col_bytes}, nfullWit := {NFULL_WIT} }}\n"
                f"    lam := {self.lam}, cardCand := {self.card_cand},\n"
                f"    commitFuel := 2 ^ {COMMIT_FUEL.bit_length() - 1}, "
                f"tape := 2 ^ {TAPE.bit_length() - 1},\n"
                f"    sizeBound := {self.size} }}")


class Pair:
    def __init__(self, name, sig: Component, sha: Component):
        self.name, self.sig, self.sha = name, sig, sha
        self.bound = sig.bound + sha.bound + Fraction(1, MAC_FIELD)
        self.lam = bits(self.bound)
        assert Fraction(1, 2 ** (self.lam + 1)) < self.bound
        self.size = sig.size + sha.size
        # `TwoFieldRowV1.Valid`'s other conjuncts
        assert (2 * sig.row.n + COMMIT_FUEL) + (2 * sha.row.n + COMMIT_FUEL) < TAPE
        assert OPENINGS + sig.params.q + sig.row.n <= sig.row.field_size
        assert OPENINGS + sha.params.q + sha.row.n <= sha.row.field_size
        self.len2 = 1 + sig.length + sha.length
        self.slack_bound = self.bound + 2 * Fraction(TAPE * self.len2, 2 ** DIGEST_BITS)
        self.coeff = max(max(sig.fs_coeff, sha.fs_coeff), Fraction(1, MAC_FIELD))
        self.slack_coeff = self.coeff + 2 * Fraction(TAPE, 2 ** DIGEST_BITS)
        self.slack_bound_bits = bits(self.slack_bound)
        self.slack_coeff_bits = bits(self.slack_coeff)
        assert self.slack_bound_bits == self.lam and self.slack_coeff_bits == bits(self.coeff)


def derive():
    profiles = load_profiles()
    comps = {c[0]: Component(*c, profiles) for c in COMPONENTS}
    pairs = [Pair(name, comps[s], comps[h]) for name, s, h in PAIRS]
    return comps, pairs


# --------------------------------------------------------------------------- #
# Report
# --------------------------------------------------------------------------- #

def report(comps, pairs):
    print("component  field    n     k    w   r   e     g    m       ft    at    L  "
          "Ligero(bits, -lg eps)   nl rounds  lam (-lg bound)  coeff  size")
    for c in comps.values():
        r = c.row
        field = "P-256" if r.field_order else "2^128"
        print(f"{c.name:<10} {field:<6} {r.n:>5} {r.k:>4} {c.params.q:>4} {r.openings:>3} "
              f"{r.e:>5} {r.g:>4} {r.m:>7} {r.ft:>5} {r.at:>5} {r.list_bound:>2}  "
              f"{r.target_bits:>3} ({lg(r.eps()):7.3f})        "
              f"{c.params.nl:>3} {c.params.total_rounds:>5}  {c.lam:>4} ({lg(c.bound):7.3f})  "
              f"{c.fs_bits:>4}  {c.size}")
        print(f"{'':<11}-lg cover {lg(r.cover()):.2f}  -lg fail {lg(r.fail()):.2f}  "
              f"-lg arith {lg(r.arith()):.2f}  -lg fieldDensity {lg(c.params.field_density):.2f}  "
              f"max slot = {c.max_slot}  L = {c.length}")
    print()
    print("pair         lam (-lg bound)   coeff (-lg)        len2  size")
    for p in pairs:
        print(f"{p.name:<12} {p.lam:>4} ({lg(p.bound):7.3f})   {bits(p.coeff):>4} "
              f"({lg(p.coeff):7.3f})   {p.len2:>5}  {p.size}")


def emit(comps, pairs):
    print("-- LigeroV1RowsV7")
    for c in comps.values():
        print(f"def {c.name} : Row :=\n  " + c.row.lean().replace("\n", "\n  "))
    print("\n-- CertifiedV7")
    for c in comps.values():
        print(f"def {c.name} : Row :=\n  " + c.lean_row())
    print("\n-- TwoFieldV7Rows")
    for p in pairs:
        print(f"def {p.name} : TwoFieldRowV1 :=\n  {{ ecdsa := CertifiedV1.{p.sig.name}, "
              f"sha := CertifiedV1.{p.sha.name},\n    macFieldSize := 2 ^ 128, lam := {p.lam}, "
              f"sizeBound := {p.size} }}")


# --------------------------------------------------------------------------- #
# Check
# --------------------------------------------------------------------------- #

_DEF_RE = re.compile(r"^def (v7\w+) : (?:Lfzk\.LigeroV1Rows\.)?Row :=\s*\n(.*?)(?=\n\n|\n/--|\ntheorem)",
                     re.S | re.M)
_CROW_RE = re.compile(
    r"\{ params :=\s*\{ row := Lfzk\.LigeroV1Rows\.(\w+)\s*q := (\d+), nl := (\d+),\s*"
    r"logw := fun ly => \[([\d, ]+)\]\.getD ly 0,\s*logc := (\d+), digestBits := (\d+), "
    r"ninp := (\d+),\s*colBytes := (\d+), nfullWit := (\d+) \}\s*lam := (\d+), cardCand := (\d+),"
    r"\s*commitFuel := 2 \^ (\d+), tape := 2 \^ (\d+),\s*sizeBound := (\d+) \}")
_PAIR_RE = re.compile(
    r"def (v7P256Sha\d) : TwoFieldRowV1 :=\s*\{ ecdsa := CertifiedV1\.(\w+), "
    r"sha := CertifiedV1\.(\w+),\s*macFieldSize := 2 \^ (\d+), lam := (\d+), "
    r"sizeBound := (\d+) \}")
# one theorem's statement: never runs into the next declaration
_STMT = r"((?:(?!\ntheorem |\ndef |\n/--).)*?)"
_LE_RE = re.compile(r"theorem (v7\w+?)\s+(?:[({\[][^)}\]]*[)}\]]\s*)*:\s*" + _STMT +
                    r"\s*≤ \(1 : ℚ\) / 2 \^ (\d+)"
                    r"(?: \+ N \* \(\(1 : ℚ\) / 2 \^ (\d+)\))? :=", re.S)
_NLE_RE = re.compile(r"theorem (v7\w+_sharp) :\s*¬ " + _STMT + r" ≤ \(1 : ℚ\) / 2 \^ (\d+) :=",
                     re.S)


def check(comps, pairs) -> int:
    failures = []

    def expect(label, got, want):
        ok = got == want
        print(f"  {'ok ' if ok else 'BAD'} {label}: {got}" + ("" if ok else f" (expected {want})"))
        if not ok:
            failures.append(label)

    # Ligero rows
    print(LIGERO_FILE.name)
    text = LIGERO_FILE.read_text()
    found = {}
    for mt in _DEF_RE.finditer(text):
        rows = []
        for m in rbr._ROW_RE.finditer(mt.group(2)):   # `rbr_v1_rows.py`'s own literal parser
            n, k, d, e, g, m_, fb, tb, r, order, ft, at = m.groups()
            q = 0 if order is None else (rbr.P256 if order == "p256Order" else int(order))
            rows.append(rbr.Row(int(n), int(k), int(d), int(e), int(g), int(m_), int(fb),
                                int(tb), int(r), int(ft), int(at), q))
        if len(rows) == 1:
            found[mt.group(1)] = rows[0]
    for c in comps.values():
        got = found.get(c.name)
        expect(f"{c.name} Ligero row", got, c.row)
        if got is not None:
            bad = got.valid() + ([] if got.sharp() else ["not sharp"])
            expect(f"{c.name} Ligero row Valid ∧ Sharp", bad, [])
    for c in comps.values():
        m = re.search(rf"theorem {c.name}_listBound : {c.name}\.listBound = (\d+)", text)
        expect(f"{c.name}_listBound", m and int(m.group(1)), c.row.list_bound)
        m = re.search(rf"theorem {c.name}_targetBits : {c.name}\.targetBits = (\d+)", text)
        expect(f"{c.name}_targetBits", m and int(m.group(1)), c.row.target_bits)

    # composed rows and their numerals
    print(CERTIFIED_FILE.name)
    text = CERTIFIED_FILE.read_text()
    crows = {}
    for mt in re.finditer(r"^def (v7\w+) : Row :=\s*\n(.*?)\n\n", text, re.S | re.M):
        m = _CROW_RE.search(mt.group(2))
        if m:
            crows[mt.group(1)] = m.groups()
    for c in comps.values():
        want = (c.name, str(c.params.q), str(c.params.nl), ", ".join(map(str, c.params.logw)),
                "0", str(DIGEST_BITS), str(c.params.ninp), str(c.col_bytes), str(NFULL_WIT),
                str(c.lam), str(c.card_cand), str(COMMIT_FUEL.bit_length() - 1),
                str(TAPE.bit_length() - 1), str(c.size))
        expect(f"{c.name} composed row", crows.get(c.name), want)
    les = {m.group(1): (int(m.group(3)), m.group(4) and int(m.group(4)))
           for m in _LE_RE.finditer(text)}
    nles = {m.group(1): int(m.group(3)) for m in _NLE_RE.finditer(text)}
    for c in comps.values():
        expect(f"{c.name}_fsCoefficient", les.get(f"{c.name}_fsCoefficient"), (c.fs_bits, None))
        expect(f"{c.name}_fsCoefficient_sharp", nles.get(f"{c.name}_fsCoefficient_sharp"),
               c.fs_bits + 1)
        expect(f"{c.name}_adaptive_slack_bound", les.get(f"{c.name}_adaptive_slack_bound"),
               (c.lam, None))
        expect(f"{c.name}_adaptive_slack_coeff", les.get(f"{c.name}_adaptive_slack_coeff"),
               (c.fs_bits, None))
        expect(f"{c.name}_adaptive_rhs_le", les.get(f"{c.name}_adaptive_rhs_le"),
               (c.lam, c.fs_bits))
        expect(f"{c.name}_fs_rhs_le", les.get(f"{c.name}_fs_rhs_le"), (c.lam, c.fs_bits))
        expect(f"{c.name}_fieldDensity_le", les.get(f"{c.name}_fieldDensity_le"),
               (c.field_density_bits, None))
        expect(f"{c.name}_ligeroDensity_le", les.get(f"{c.name}_ligeroDensity_le"),
               (c.ligero_density_bits, None))
        expect(f"{c.name}_merkleTerm_le", les.get(f"{c.name}_merkleTerm_le"), (c.merkle_bits, None))
        m = re.search(rf"theorem {c.name}_length :\s*Rounds\.Role\.length {c.name}\.params\.nl "
                      rf"{c.name}\.params\.rounds = (\d+)", text)
        expect(f"{c.name}_length", m and int(m.group(1)), c.length)
        slot = {"field": None, "challenge": "fail + arith", "query": "cover"}[c.max_slot]
        m = re.search(rf"theorem {c.name}_maxDensity_eq :\s*{c.name}\.maxDensity = (.*?) :=",
                      text, re.S)
        got = None
        if m:
            got = "fail + arith" if "fail" in m.group(1) else "cover" if "cover" in m.group(1) \
                else m.group(1)
        expect(f"{c.name}_maxDensity_eq", got, slot)

    # two-field rows
    print(TWOFIELD_FILE.name)
    text = TWOFIELD_FILE.read_text()
    prow = {m.group(1): m.groups()[1:] for m in _PAIR_RE.finditer(text)}
    les = {m.group(1): (int(m.group(3)), m.group(4) and int(m.group(4)))
           for m in _LE_RE.finditer(text)}
    for p in pairs:
        expect(f"{p.name} row", prow.get(p.name),
               (p.sig.name, p.sha.name, "128", str(p.lam), str(p.size)))
        expect(f"{p.name}_adaptive_slack_bound", les.get(f"{p.name}_adaptive_slack_bound"),
               (p.lam, None))
        expect(f"{p.name}_adaptive_slack_coeff", les.get(f"{p.name}_adaptive_slack_coeff"),
               (p.slack_coeff_bits, None))
        expect(f"{p.name}_adaptive_rhs_le", les.get(f"{p.name}_adaptive_rhs_le"),
               (p.lam, p.slack_coeff_bits))
        m = re.search(rf"theorem {p.name}_len2 : len2 {p.name}\.ecdsa {p.name}\.sha = (\d+)", text)
        expect(f"{p.name}_len2", m and int(m.group(1)), p.len2)
    print(f"{len(failures)} failing")
    return 1 if failures else 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--emit-lean", action="store_true")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args(argv)
    comps, pairs = derive()
    if args.check:
        return check(comps, pairs)
    report(comps, pairs)
    if args.emit_lean:
        print()
        emit(comps, pairs)
    return 0


if __name__ == "__main__":
    sys.exit(main())
