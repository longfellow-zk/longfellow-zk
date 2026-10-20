#!/usr/bin/env python3
"""Exact-rational FS budget report; decimal logarithms are display only.

Run from any directory. The existing Hahn table is read, not duplicated.
This evaluates a hypothetical two-level schedule with the stated geometry
at both levels; it does not construct a circuit, Child, or byte transcript.
The two selected schedules are independently checked by FSTwoLevel.lean.
"""

from fractions import Fraction
from math import comb, isqrt, log2
from pathlib import Path
import re

N, K, S, FIELD = 8192, 512, 64, 2**128
OVERLAP = K + 2 * S - 1
MU = Fraction(comb(N, K + 2 * S + 1), FIELD ** (S + 1))
UNIT = Fraction(1, FIELD)
FLOOR = 2 * UNIT - UNIT**2


def theta(cutoff, queries):
    return Fraction(comb(cutoff - 1, queries), comb(N, queries))


def error(threshold):
    return threshold + (1 - threshold) * (MU + UNIT)


def two_error(e0, e1):
    return e0 + (1 - e0) * e1


def budget(parent, child):
    a0, t0, l0 = parent
    a1, t1, l1 = child
    return 2 * MU + (l0 + l1) * UNIT + l1 * theta(a0, t0) + theta(a1, t1)


def role_prices(parent, child):
    a0, t0, l0 = parent
    a1, t1, l1 = child
    return (MU + l0 * UNIT, l1 * theta(a0, t0),
            MU + l1 * UNIT, theta(a1, t1))


def bits(value):
    # No floating-point value is used to select or certify a schedule.
    return log2(value.denominator) - log2(value.numerator)


def johnson(cutoff):
    denominator = cutoff**2 - N * OVERLAP
    assert denominator > 0
    return N * (cutoff - OVERLAP) // denominator


def excess_ok(cutoff, queries, bound):
    # The incidence-index-one HahnExcessCondition, with bound < FIELD.
    return bound * comb(OVERLAP, queries) <= 2 * comb(cutoff - 1, queries)


def johnson_breakpoints():
    """Smallest cutoff for every attainable Johnson list bound."""
    cutoffs = {}
    for a in range(max(2 * K + S, isqrt(N * OVERLAP) + 1), N + 1):
        cutoffs.setdefault(johnson(a), a)
    return [(a, bound) for bound, a in cutoffs.items()]


def best_johnson(queries, replace_parent=False, replace_child=False):
    """Exhaustive exact search over both cutoffs, equal query counts.

    Rank error is common. Multiplication by FIELD*choose(N,t) converts
    the remaining objective into an integer, avoiding rounding in selection.
    For a fixed list bound the smallest cutoff minimizes the threshold.
    Replacement flags are UNPROVED sensitivity experiments: a flagged
    exception list is priced at one field unit instead of its cardinality.
    """
    denominator = comb(N, queries)
    candidates = [(a, bound, comb(a - 1, queries))
                  for a, bound in johnson_breakpoints()]
    _, a0, l0, a1, l1 = min(
        (((1 if replace_parent else l0) + (1 if replace_child else l1)) * denominator
         + FIELD * (l1 * c0 + c1), a0, l0, a1, l1)
        for a0, l0, c0 in candidates for a1, l1, c1 in candidates)
    assert excess_ok(a0, queries, l0) and excess_ok(a1, queries, l1)
    return (a0, queries, l0), (a1, queries, l1)


def main():
    source = (Path(__file__).resolve().parent.parent / "Instances" / "HahnRateSixteenth.lean").read_text()
    certificates = {int(a): (int(cutoff), int(bound)) for a, cutoff, bound in
                    re.findall(r"\| \.c(\d+) => ⟨(\d+), (\d+), coeffs", source)}
    rows = [(int(t), int(cert)) for t, cert in
            re.findall(r"⟨(\d+), \.c(\d+), \d+, \d+, \d+⟩", source)]
    assert len(rows) == 21
    print("Field 2^128; both levels n=8192, k=512, s=64.")
    print("Same verified local row used at both levels (numerical reference):")
    print("| t | log2 L | two-level IOP bits | full-list FS B bits | loss |")
    print("|---:|---:|---:|---:|---:|")
    for t, cert in rows:
        if t not in (50, 60, 64, 65, 70):
            continue
        a, bound = certificates[cert]
        e = error(theta(a, t))
        rho = two_error(e, e)
        b = budget((a, t, bound), (a, t, bound))
        print(f"| {t} | {log2(bound):.4f} | {bits(rho):.4f} | {bits(b):.4f} | {bits(rho)-bits(b):.4f} |")
    a, _ = certificates[dict(rows)[70]]
    reference = two_error(error(theta(a, 70)), error(theta(a, 70)))
    assert FLOOR <= reference
    print("\nOptimized Johnson cutoffs, equal query counts (exhaustive integer search):")
    print("| t | a0 | L0 | a1 | L1 | B bits | loss vs 70-opening reference |")
    print("|---:|---:|---:|---:|---:|---:|---:|")
    for t in (64, 70, 74, 75, 80, 81):
        parent, child = best_johnson(t)
        b = budget(parent, child)
        print(f"| {t} | {parent[0]} | {parent[2]} | {child[0]} | {child[2]} | {bits(b):.4f} | {bits(reference)-bits(b):.4f} |")
    print("\nSchedules independently kernel-checked in FSTwoLevel.lean:")
    for parent, child, loss, floor_bits in [
        ((2487, 75, 15), (2559, 75, 11), 4, 123),
        ((2660, 81, 8), (2713, 80, 7), 3, 124),
    ]:
        for a, t, bound in (parent, child):
            assert johnson(a) == bound < FIELD and excess_ok(a, t, bound)
        b = budget(parent, child)
        assert b <= 2**loss * FLOOR and b <= Fraction(1, 2**floor_bits)
        prices = role_prices(parent, child)
        assert sum(prices) == b and max(prices) <= b
        print(f"parent {parent}, child {child}: B bits={bits(b):.6f}, "
              f"query-slope bits={bits(max(prices)):.6f}, "
              f"loss={bits(reference)-bits(b):.6f} < {loss} bits")
    parent, child = best_johnson(70)
    print("\n70-opening optimized budget components, in units of 2^-128:")
    print(f"parent exceptions={parent[2]}, child exceptions={child[2]}, "
          f"parent query={float(child[2]*theta(parent[0],70)/UNIT):.6f}, "
          f"terminal query={float(theta(child[0],70)/UNIT):.6f}")
    print("Rank error is included in all exact bounds; search optimality is not a Lean theorem.")
    print("\nUNPROVED sensitivity experiments at 70 openings; not security bounds:")
    for name, replace0, replace1 in [("parent", True, False), ("child", False, True),
                                     ("both", True, True)]:
        parent, child = best_johnson(70, replace0, replace1)
        hypothetical = budget(parent, child)
        if replace0:
            hypothetical -= (parent[2] - 1) * UNIT
        if replace1:
            hypothetical -= (child[2] - 1) * UNIT
        print(f"replace {name} exception price(s) by one field unit: "
              f"{bits(hypothetical):.6f} bits; parent={parent}, child={child}")


if __name__ == "__main__":
    main()
