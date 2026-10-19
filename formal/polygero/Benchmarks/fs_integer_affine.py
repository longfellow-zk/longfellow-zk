#!/usr/bin/env python3
"""Reproduce the integer-occupancy FS schedules (exact rational budgets).

Lean independently proves the combinatorial inequality, instantiates the
actual protocol certificates and checks every bound. This script is a
readable report/search aid; it is not part of the trust base.
"""
from fractions import Fraction
from math import comb, log2

N, OVERLAP, FIELD = 8192, 639, 2**128
RANK = Fraction(comb(N, 641), FIELD**65)
ROWS = (
    ("fixed", 81, 80, 2714, 6, 2, 125, 2),
    ("126 bits", 86, 86, 2917, 4, 1, 126, 3),
    ("near 126.415", 89, 88, 3007, 3, 1, 126, 2),
    ("127 bits", 100, 100, 3370, 2, 1, 127, 3),
)


def threshold(cutoff, queries):
    return Fraction(comb(cutoff - 1, queries), comb(N, queries))


def gap(cutoff, size, occupancy):
    count = size + 1
    return (2 * occupancy * count * cutoff
            - count * size * OVERLAP - N * occupancy * (occupancy + 1))


def main():
    for name, parent, child, cutoff, size, occupancy, bits, overhead in ROWS:
        assert gap(cutoff, size, occupancy) > 0
        t0, t1 = threshold(cutoff, parent), threshold(cutoff, child)
        budget = 2 * RANK + Fraction(2 * size, FIELD) + size * t0 + t1
        slope = max(RANK + Fraction(size, FIELD), size * t0, t1)
        price = Fraction(size, FIELD) + RANK
        clean = Fraction(1, 2**bits)
        assert slope <= price and budget <= 3 * price
        assert budget <= (overhead - Fraction(1, 64)) * clean
        assert RANK <= clean**2 / 64 and slope <= clean + RANK
        print(f"{name}: openings {parent}/{child}, cutoff {cutoff}, list {size}")
        print(f"  occupancy gap {gap(cutoff, size, occupancy)}; "
              f"B*q={float(budget * FIELD):.12f}; "
              f"slope bits={-log2(float(slope)):.9f}")
        print(f"  exact clean theorem: (queries+{overhead}) * 2^-{bits}")


if __name__ == "__main__":
    main()
