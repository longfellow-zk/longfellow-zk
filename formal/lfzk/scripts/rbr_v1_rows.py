#!/usr/bin/env python3
"""Round-by-round rows for Ligero **V1** at the deployed geometries, in the shape
`Lfzk.LigeroV1Rows.Row` checks.

This is an untrusted optimizer.  Every function below transcribes one Lean definition from
`formal/ligero` (the name is in its docstring) so that `Row.Valid`'s `native_decide` is the
authority and this script can only drift, never decide.  `--check` re-derives the committed
rows exactly, which is how drift is caught.

The bound a row quotes, read off `Lfzk.LigeroV1Rows.Row`:

    cover  = hypergeometricRatio (max ft (max (n-e-1) (min n (g+at)))) n r
    fail   = (selectedMCAOptimizedIntegratedFailureProfile q n e g d (m-1) localLineBound)
                 .labelsAtLeast (ft+1) / (q * (q - (g+1)))
    arith  = (uncheckedAgreementProfile q n (2k-1) L T).labelsAtLeast (at+1) / q
    eps    = L * (cover + fail + arith),      L = Certificate.listSize (Johnson, packing-capped)

with `T = isqrt(n(2k-1)) + 1` the V1 Johnson threshold and `localLineBound a` the
agreement-local clique threshold `Certificate.integratedLocalM a - 1`.

## The search

Once `g + at` exceeds `n - e - 1` the radius `e` only costs (it raises the clique threshold
and the list bound without moving the cover), so the optimum has `e = n - 1 - g - at` and
`ft = g + at`.  The search is then over `(g, at)`: `g` trades one covered column per unit against
the clique threshold `m`, which falls roughly like `1/(g+1)`; `at` trades the cover against the
unchecked list bound just above the Johnson threshold.  Candidates are scored in floating point
over the declared box and the best few are re-scored exactly.

    rbr_v1_rows.py --preset v8hash                 # n=4088 k=584 r=132 over GF(2^128)
    rbr_v1_rows.py --preset v8sig                  # n=3458 k=494 r=132 over P-256's base field
    rbr_v1_rows.py --preset v8hash --openings 120:140
    rbr_v1_rows.py --preset v8hash --emit-lean     # the Lean `Row` literal(s)
    rbr_v1_rows.py --check                         # re-derive every row literal in LigeroV1Rows.lean
"""

from __future__ import annotations

import argparse
import math
import re
import sys
from dataclasses import dataclass
from fractions import Fraction
from math import comb, isqrt
from pathlib import Path

LEAN_FILE = Path(__file__).resolve().parents[1] / "Lfzk" / "LigeroV1Rows.lean"

# `P-256`'s base field, `2^256 - 2^224 + 2^192 + 2^96 - 1` (`Lfzk.LigeroV1Rows.p256Order`).
P256 = 2 ** 256 - 2 ** 224 + 2 ** 192 + 2 ** 96 - 1
assert P256 == 115792089210356248762697446949407573530086143415290314195533631308867097853951
FIELD_ORDER_NAMES = {P256: "p256Order"}

# The deployed Ligero geometries (`formal/ligero/examples/Ligero/Longfellow/
# v8-extracted-parameters.json`, `OptimizedIOPCertificates.lean`): `k = (block_enc+1)/(rateinv+2)`,
# `n = block_enc - (2k-1)`, 132 openings.
PRESETS = {
    "v8hash": dict(n=4088, k=584, field_bits=128, field_order=0),
    "v8sig": dict(n=3458, k=494, field_bits=256, field_order=P256),
    "v7hash1": dict(n=3230, k=461, field_bits=128, field_order=0),
    "v7hash2": dict(n=3318, k=474, field_bits=128, field_order=0),
    "v7hash3": dict(n=3352, k=478, field_bits=128, field_order=0),
    "v7hash4": dict(n=3436, k=490, field_bits=128, field_order=0),
    "v7sig": dict(n=3187, k=455, field_bits=256, field_order=P256),
}


# --------------------------------------------------------------------------- #
# Lean's arithmetic
# --------------------------------------------------------------------------- #

def nat_sub(a: int, b: int) -> int:
    """Truncated subtraction on `Nat`."""
    return a - b if a > b else 0


def nat_div(a: int, b: int) -> int:
    """`Nat` division, with Lean's `x / 0 = 0`."""
    return a // b if b else 0


def choose(a: int, b: int) -> int:
    """`Nat.choose`, which is `0` when `b > a`."""
    return comb(a, b) if 0 <= b <= a else 0


# --------------------------------------------------------------------------- #
# Exact mirrors of the Lean definitions
# --------------------------------------------------------------------------- #

def hypergeometric_ratio(a: int, b: int, c: int) -> Fraction:
    """`LigeroFamily.hypergeometricRatio a b c = C(a, c) / C(b, c)`."""
    return Fraction(choose(a, c), choose(b, c))


def jl_denominator(n: int, d: int, errors: int) -> int:
    """`CodingTheory.InterleavedJohnson.denominator` (an `Int`)."""
    return n * d - 2 * n * errors + errors * errors


def jl_list_bound(n: int, d: int, errors: int) -> int:
    """`CodingTheory.InterleavedJohnson.listBound = n * (d - E) / denominator.toNat`."""
    return nat_div(n * nat_sub(d, errors), max(jl_denominator(n, d, errors), 0))


def balanced_choose_three(n: int, total: int) -> int:
    """`AffineAgreement.balanced_choose_three`."""
    low, high_count = divmod(total, n)
    return (n - high_count) * choose(low, 3) + high_count * choose(low + 1, 3)


def clique_upper(m: int, occupancy: int) -> int:
    """`SelectedMCA.simpleCliqueUpperNat m R = (R - 2) * C(m, 2) / 3`."""
    return nat_div(nat_sub(occupancy, 2) * choose(m, 2), 3)


def direct_clique(n: int, e: int, g: int, d: int, m: int) -> bool:
    """`SelectedMCA.DirectCliqueCondition n e g d m`."""
    if m < 3 or not nat_sub(n, d) < nat_sub(n, e):
        return False
    occupancy = nat_div(n, g + 1)          # `directLineOccupancyBound n g`
    return (
        clique_upper(m, occupancy) * nat_sub(nat_sub(n, e), nat_sub(n, d))
        + choose(m, 3) * nat_sub(n, d)
        < balanced_choose_three(n, m * nat_sub(n, e))
    )


def least_clique_threshold(n: int, e: int, g: int, d: int, ceiling: int = 1 << 52) -> int | None:
    """Least `m` satisfying `DirectCliqueCondition`, or `None` if unreachable."""
    low, high = 2, 3
    while not direct_clique(n, e, g, d, high):
        low, high = high, high * 2
        if high > ceiling:
            return None
    while high - low > 1:
        middle = (low + high) // 2
        if direct_clique(n, e, g, d, middle):
            high = middle
        else:
            low = middle
    assert direct_clique(n, e, g, d, high)
    assert high == 3 or not direct_clique(n, e, g, d, high - 1)
    return high


def binary_clique_search(n: int, radius: int, g: int, d: int, fuel: int, lo: int, hi: int) -> int:
    """`Ligero.Examples.Grid.binaryCliqueSearch n radius g d fuel lo hi`."""
    while fuel > 0:
        if lo < hi:
            mid = (lo + hi) // 2
            if direct_clique(n, radius, g, d, mid):
                hi = mid
            else:
                lo = mid + 1
            fuel -= 1
        else:
            return hi
    return hi


def failure_labels(n: int, g: int, d: int, line_bound: int):
    """`SchemeSelectedMCA.selectedMCAFailureProfile n g d lineBound`."""
    def labels(a: int) -> int:
        if n < a:
            return 0
        if 3 * nat_sub(n, a) < d:
            return 1 + nat_div(nat_sub(n, a), g + 1)
        return line_bound
    return labels


def unchecked_list_bound(n: int, lam: int, a: int) -> int:
    """`LigeroFamily.uncheckedAgreementListBound n lambda a`."""
    return jl_list_bound(n, nat_sub(n, lam), nat_sub(n, a))


def unchecked_labels(q: int, n: int, lam: int, list_size: int, threshold: int):
    """`LigeroFamily.uncheckedAgreementProfile q n lambda L johnsonThreshold`."""
    def labels(a: int) -> int:
        if n < a:
            return 0
        if a < threshold:
            return q
        return list_size * unchecked_list_bound(n, lam, a)
    return labels


# --------------------------------------------------------------------------- #
# Exact mirror of `Lfzk.LigeroV1Rows.Row` over a `Certificate`
# --------------------------------------------------------------------------- #

@dataclass(frozen=True)
class Row:
    n: int
    k: int
    d: int
    e: int
    g: int
    m: int
    field_bits: int
    target_bits: int
    openings: int
    ft: int
    at: int
    field_order: int = 0   # `Certificate.fieldOrder`; zero means `2^fieldBits`
    cutoff: int = 0        # `Certificate.cutoff`, unused on the V1 triples route
    local_m: int = 0       # `Certificate.localM`

    # ---- `Certificate` ----
    @property
    def field_size(self) -> int:
        """`Certificate.fieldSize`."""
        return 2 ** self.field_bits if self.field_order == 0 else self.field_order

    @property
    def line_bound(self) -> int:
        """`Certificate.lineBound = directLineFailureBound m = m - 1`."""
        return nat_sub(self.m, 1)

    @property
    def refined_local_m(self) -> int:
        """`Certificate.refinedLocalM`."""
        return self.m if self.local_m == 0 else self.local_m

    def integrated_local_m(self, a: int) -> int:
        """`Certificate.integratedLocalM c a`."""
        if 3 * nat_sub(self.n, a) < self.d:
            return self.m
        return binary_clique_search(self.n, nat_sub(self.n, a), self.g, self.d, 64, 3,
                                    max(self.m, self.refined_local_m))

    def integrated_local_line_bound(self, a: int) -> int:
        """`Certificate.integratedLocalLineBound c a`."""
        return nat_sub(self.integrated_local_m(a), 1)

    def integrated_local_point_valid(self, a: int) -> bool:
        """`Certificate.IntegratedLocalPointValid c a`."""
        lm = self.integrated_local_m(a)
        radius = nat_sub(self.n, a)
        if not direct_clique(self.n, radius, self.g, self.d, lm):
            return False
        if not 3 * radius < self.d:
            return not direct_clique(self.n, radius, self.g, self.d, nat_sub(lm, 1))
        return True

    def integrated_local_valid(self) -> bool:
        """`Certificate.integratedLocalValidBool`."""
        return all(self.integrated_local_point_valid(a)
                   for a in range(self.n + 1) if nat_sub(self.n, self.e) <= a)

    @property
    def list_bound(self) -> int:
        """`Certificate.listSize`: the Johnson bound `InterleavedJohnson.listBound n d (e + g)`,
        capped at 1 inside unique decoding and at 2 under the three-codeword packing bound."""
        j = jl_list_bound(self.n, self.d, self.e + self.g)
        if 2 * (self.e + self.g) < self.d:
            return min(j, 1)
        if self.n + 3 * (self.n - self.d) < 3 * (self.n - (self.e + self.g)):
            return min(j, 2)
        return j

    @property
    def lam(self) -> int:
        return nat_sub(2 * self.k, 1)

    @property
    def johnson_threshold(self) -> int:
        """`Certificate.v1Threshold = Nat.sqrt (n * (2k - 1)) + 1`."""
        return isqrt(self.n * self.lam) + 1

    @property
    def optimized_failure_denominator(self) -> int:
        """`Certificate.optimizedFailureDenominator = q * (q - (g + 1))`."""
        q = self.field_size
        return q * nat_sub(q, self.g + 1)

    # ---- the profiles ----
    def integrated_failure_labels(self, a: int) -> int:
        """`SchemeSelectedMCA.selectedMCAIntegratedFailureProfile n e g d (m-1) local`."""
        outer = failure_labels(self.n, self.g, self.d, self.line_bound)
        if nat_sub(self.n, self.e) <= a <= self.n:
            local = failure_labels(self.n, self.g, self.d, self.integrated_local_line_bound(a))
            return min(outer(a), local(a))
        return outer(a)

    def failure_profile_labels(self, a: int) -> int:
        """`selectedMCAOptimizedIntegratedFailureProfile q n e g d (m-1) local` =
        `endpointOptimizedProfile q g (integrated profile)`."""
        q = self.field_size
        base = self.integrated_failure_labels(a)
        if a == self.n:
            return min(q * base, (self.g + 1) * nat_sub(q, self.g + 1))
        return q * base

    # ---- `Row` ----
    @property
    def query_cover(self) -> int:
        return max(self.ft, max(nat_sub(nat_sub(self.n, self.e), 1),
                                min(self.n, self.g + self.at)))

    def cover(self) -> Fraction:
        return hypergeometric_ratio(self.query_cover, self.n, self.openings)

    def fail(self) -> Fraction:
        return Fraction(self.failure_profile_labels(self.ft + 1),
                        self.optimized_failure_denominator)

    def arith(self) -> Fraction:
        labels = unchecked_labels(self.field_size, self.n, self.lam,
                                  self.list_bound, self.johnson_threshold)
        return Fraction(labels(self.at + 1), self.field_size)

    def eps(self) -> Fraction:
        return self.list_bound * (self.cover() + self.fail() + self.arith())

    def valid(self) -> list[str]:
        """`Row.Valid`, conjunct by conjunct; returns the failing ones."""
        bad = []
        if not 0 < self.k:
            bad.append("0 < k")
        if not self.k <= self.n:
            bad.append("k <= n")
        if self.d != nat_sub(self.n, self.k) + 1:
            bad.append("d = n - k + 1")
        if not 2 * self.k <= self.n:
            bad.append("2k <= n")
        if not direct_clique(self.n, self.e, self.g, self.d, self.m):
            bad.append("DirectCliqueCondition m")
        if not 3 * self.g < nat_sub(self.d, self.e):
            bad.append("3g < d - e")
        if not self.g + 1 < self.field_size:
            bad.append("g + 1 < |F|")
        if not jl_denominator(self.n, self.d, self.e + self.g) > 0:
            bad.append("Johnson denominator")
        if not self.integrated_local_valid():
            bad.append("integratedLocalValidBool")
        if not (self.ft + 1 <= self.n and self.at + 1 <= self.n):
            bad.append("thresholds in range")
        if not self.openings <= self.n:
            bad.append("openings <= n")
        if not self.eps() <= Fraction(1, 2 ** self.target_bits):
            bad.append("eps <= 2^-target")
        return bad

    def sharp(self) -> bool:
        """`Row.Sharp`."""
        return Fraction(1, 2 ** (self.target_bits + 1)) < self.eps()

    def lean(self) -> str:
        order = ("" if self.field_order == 0 else
                 f", fieldOrder := {FIELD_ORDER_NAMES.get(self.field_order, self.field_order)}")
        return (f"{{ certificate :=\n"
                f"      {{ n := {self.n}, k := {self.k}, d := {self.d}, e := {self.e}, "
                f"g := {self.g}, m := {self.m},\n"
                f"        fieldBits := {self.field_bits}, targetBits := {self.target_bits}, "
                f"openings := {self.openings}{order} }},\n"
                f"    failureThreshold := {self.ft}, arithmeticThreshold := {self.at} }}")


def certified_bits(eps: Fraction) -> int:
    """Largest `t` with `eps <= 2^-t`, exactly."""
    t = max(0, math.floor(-math.log2(eps)) - 2) if eps > 0 else 0
    while eps <= Fraction(1, 2 ** (t + 1)):
        t += 1
    while t > 0 and eps > Fraction(1, 2 ** t):
        t -= 1
    return t


# --------------------------------------------------------------------------- #
# Search
# --------------------------------------------------------------------------- #

def log_row(n: int, queries: int) -> list[float]:
    """`log C(x, queries)` for every `x <= n`."""
    return [
        math.lgamma(x + 1) - math.lgamma(queries + 1) - math.lgamma(x - queries + 1)
        if x >= queries else -math.inf
        for x in range(n + 1)
    ]


class Scanner:
    """`(g, at) -> bits` at one `(n, k, |F|)`, with the clique threshold cached: `m` depends on
    `(e, g) = (n-1-g-at, g)` and not on `r`."""

    def __init__(self, n: int, k: int, field_bits: int, field_order: int = 0):
        self.n, self.k, self.d = n, k, n - k + 1
        self.field_bits, self.field_order = field_bits, field_order
        self.q = 2 ** field_bits if field_order == 0 else field_order
        self.lam = 2 * k - 1
        self.at_min = isqrt(n * self.lam)            # at + 1 >= johnsonThreshold
        self._m: dict[tuple[int, int], int | None] = {}
        self._logrow: dict[int, list[float]] = {}

    def e_of(self, g: int, at: int) -> int:
        return self.n - 1 - g - at

    def m_of(self, g: int, at: int) -> int | None:
        e = self.e_of(g, at)
        key = (e, g)
        if key not in self._m:
            ok = e >= 0 and 3 * g < self.d - e
            self._m[key] = least_clique_threshold(self.n, e, g, self.d) if ok else None
        return self._m[key]

    def log_cover(self, base: int, r: int) -> float:
        row = self._logrow.get(r)
        if row is None:
            row = self._logrow[r] = log_row(self.n, r)
        return (row[base] - row[self.n]) / math.log(2)

    def row(self, g: int, at: int, r: int) -> Row:
        e = self.e_of(g, at)
        m = self.m_of(g, at)
        assert m is not None
        probe = Row(self.n, self.k, self.d, e, g, m, self.field_bits, 0, r, g + at, at,
                    self.field_order)
        return Row(self.n, self.k, self.d, e, g, m, self.field_bits, certified_bits(probe.eps()),
                   r, g + at, at, self.field_order)

    def cells(self, g_max: int, at_span: int) -> list[tuple[int, int, int, float]]:
        """Every admissible `(g, at)` in the box with the `r`-independent part of the bound,
        `(g, at, L, fail + arith)` (floating point; `fail` at the outer line bound, which is what
        the exact profile reduces to at `ft + 1 = n - e` when `m` is the least threshold)."""
        out = []
        for g in range(0, g_max + 1):
            for at in range(self.at_min, self.at_min + at_span + 1):
                m = self.m_of(g, at)
                if m is None:
                    continue
                L = Row(self.n, self.k, self.d, self.e_of(g, at), g, 0, self.field_bits, 0, 0, 0, 0,
                        self.field_order).list_bound
                if L == 0:
                    continue
                rest = ((m - 1) / (self.q - g - 1)
                        + L * unchecked_list_bound(self.n, self.lam, at + 1) / self.q)
                out.append((g, at, L, rest))
        return out

    def best(self, r: int, cells, keep: int = 24) -> Row:
        """Exhaustive over `cells` in floating point, then the `keep` best re-scored exactly.
        Best-found over the box, nothing more."""
        cover = [2.0 ** self.log_cover(base, r) if base >= r else 0.0
                 for base in range(self.n + 1)]
        scored = sorted(((L * (cover[g + at] + rest), g, at)
                         for g, at, L, rest in cells))[:keep]
        top = None
        for _eps, g, at in scored:
            row = self.row(g, at, r)
            key = (row.target_bits, -row.eps())
            if top is None or key > top[0]:
                top = (key, row)
        return top[1]


# --------------------------------------------------------------------------- #
# Checking the committed rows
# --------------------------------------------------------------------------- #

_ROW_RE = re.compile(
    r"\{ certificate :=\s*\{ n := (\d+), k := (\d+), d := (\d+), e := (\d+), g := (\d+), "
    r"m := (\d+),\s*fieldBits := (\d+), targetBits := (\d+), openings := (\d+)"
    r"(?:, fieldOrder := (\w+))? \},\s*failureThreshold := (\d+), arithmeticThreshold := (\d+) \}")


def parse_rows(path: Path = LEAN_FILE) -> list[Row]:
    """Every `Row` literal in `LigeroV1Rows.lean`, in file order."""
    by_name = {name: order for order, name in FIELD_ORDER_NAMES.items()}
    rows = []
    for mt in _ROW_RE.finditer(path.read_text()):
        n, k, d, e, g, m, fb, tb, r, order, ft, at = mt.groups()
        q = 0 if order is None else (int(order) if order.isdigit() else by_name[order])
        rows.append(Row(int(n), int(k), int(d), int(e), int(g), int(m), int(fb), int(tb),
                        int(r), int(ft), int(at), q))
    return rows


def command_check(path: Path = LEAN_FILE) -> int:
    rows = parse_rows(path)
    failures = 0
    for row in rows:
        bad = row.valid() + ([] if row.sharp() else ["not sharp"])
        if bad:
            failures += 1
        label = "ok" if not bad else ", ".join(bad)
        print(f"n = {row.n}, k = {row.k}, r = {row.openings}, bits = {row.target_bits}: {label}")
    print(f"checked {len(rows)} rows, {failures} failing")
    return 1 if failures or not rows else 0


# --------------------------------------------------------------------------- #
# Main
# --------------------------------------------------------------------------- #

def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--preset", choices=sorted(PRESETS), default=None)
    parser.add_argument("--n", type=int, default=None)
    parser.add_argument("--k", type=int, default=None)
    parser.add_argument("--field", type=int, default=128, help="field bits (binary field)")
    parser.add_argument("--p256", action="store_true", help="P-256's base field")
    parser.add_argument("--openings", default="132", help="`lo:hi` or a single count")
    parser.add_argument("--g-max", type=int, default=600, help="search box: 0 <= g <= g-max")
    parser.add_argument("--at-span", type=int, default=200,
                        help="search box: T-1 <= at <= T-1 + at-span")
    parser.add_argument("--emit-lean", action="store_true")
    parser.add_argument("--check", action="store_true",
                        help="re-derive every row literal in LigeroV1Rows.lean")
    args = parser.parse_args(argv)
    if args.check:
        return command_check()

    if args.preset:
        p = PRESETS[args.preset]
        n, k, field_bits, field_order = p["n"], p["k"], p["field_bits"], p["field_order"]
    else:
        if args.n is None or args.k is None:
            parser.error("--preset or both --n and --k are required")
        n, k = args.n, args.k
        field_order = P256 if args.p256 else 0
        field_bits = field_order.bit_length() if field_order else args.field

    lo, hi = ((int(x) for x in args.openings.split(":")) if ":" in args.openings
              else (int(args.openings), int(args.openings)))
    scanner = Scanner(n, k, field_bits, field_order)
    cells = scanner.cells(args.g_max, args.at_span)
    label = (f"{FIELD_ORDER_NAMES.get(field_order, field_order)} ({field_bits} bits)"
             if field_order else f"2^{field_bits}")
    print(f"V1 rbr   n = {n}   k = {k}   d = {n - k + 1}   |F| = {label}   "
          f"johnsonThreshold = {scanner.at_min + 1}")
    print(f"box: g <= {args.g_max}, {scanner.at_min} <= at <= {scanner.at_min + args.at_span}, "
          f"e = n-1-g-at, ft = g+at  ({len(cells)} admissible cells)\n")
    print(f"{'r':>4} {'bits':>5} {'e':>5} {'g':>5} {'at':>5} {'m':>7} {'L':>3} "
          f"{'-lg cover':>9} {'-lg fail':>9} {'-lg arith':>9}")
    rows = []
    for r in range(lo, hi + 1):
        row = scanner.best(r, cells)
        bad = row.valid()
        assert not bad, (r, bad)
        assert row.sharp(), r
        rows.append(row)
        print(f"{r:>4} {row.target_bits:>5} {row.e:>5} {row.g:>5} {row.at:>5} "
              f"{row.m:>7} {row.list_bound:>3} {-math.log2(row.cover()):>9.2f} "
              f"{-math.log2(row.fail()):>9.2f} {-math.log2(row.arith()):>9.2f}")
    if args.emit_lean:
        print()
        for row in rows:
            print(row.lean())
    return 0


if __name__ == "__main__":
    sys.exit(main())
