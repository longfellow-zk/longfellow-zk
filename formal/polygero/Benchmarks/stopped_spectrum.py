#!/usr/bin/env python3
"""Exact exposed-parent spectrum moments; not arbitrary-order FS bounds.

The Lean file FSStoppedSpectrum.lean independently checks the safe rates.
Integer-occupancy certificates must establish the cumulative tail lists;
StoppedSpectrum.spectrum_layers_le then converts them into these moments.
The final nonuniform refinement is an exact Python experiment, and has
not been formalized in Lean or connected to arbitrary-order ROM queries.
"""
from fractions import Fraction
from math import comb, log2

N, FIELD = 8192, 2**128


def price(rate, capacity):
    if capacity <= 2 * rate:
        return capacity / (4 * rate)
    return 1 - rate / capacity


def moment(queries, cuts, units):
    rate = units / FIELD
    fractions = [Fraction(comb(a - 1, queries), comb(N, queries)) for a in cuts]
    return sum((price(rate, c) for c in fractions), Fraction(0)) + price(rate, Fraction(1))


def nonuniform_exploration():
    """Check affine majorants using whole-family integer occupancies.

    For m associated sets of cardinalities a_i and pair intersections at
    most 639, integer occupancies imply
      2*h*sum(a_i) <= m*(m-1)*639 + 8192*h*(h+1).
    The stable Lean theorem currently treats equal-cardinality families;
    this nonuniform extension and the affine assembly remain unformalized.
    """
    denominator = comb(N, 81)
    units = Fraction(47, 10)

    def f(a):
        capacity = Fraction(FIELD * comb(a, 81), denominator)
        return price(units, capacity)

    # Support-size bounds for exactly m systems. Individual capacities
    # additionally have a_i <= N. All high systems have a_i >= 2714.
    totals = {
        m: min((m * (m - 1) * 639 + N * h * (h + 1)) // (2 * h)
               for h in range(1, 9))
        for m in range(1, 7)
    }
    assert totals == {1: 8192, 2: 8831, 3: 10109, 4: 12026, 5: 14582, 6: 17080}

    f2714, f2880, f2916, f2917 = (f(a) for a in (2714, 2880, 2916, 2917))
    slope5 = f2917 - f2916
    slope6 = (f2880 - f2714) / 166
    assert slope5 >= 0 and slope6 >= 0
    for a in range(2714, N + 1):
        value = f(a)
        assert value <= f2916 + slope5 * (a - 2916)
        assert value <= f2714 + slope6 * (a - 2714)
    bound5 = 5 * f2916 + slope5 * (totals[5] - 5 * 2916)
    bound6 = 6 * f2714 + slope6 * (totals[6] - 6 * 2714)
    assert bound5 <= units and bound6 <= units and 4 <= units
    baseline = Fraction(FIELD * comb(2713, 81), denominator)
    full_units = units + baseline
    print("UNFORMALIZED nonuniform refinement, exact Python checks only:")
    print(f"all 5479 support sizes checked; m5 bound={float(bound5):.12f}, "
          f"m6 bound={float(bound6):.12f}, safe exception rate={units}/q")
    print(f"candidate baseline/rank local rate={float(full_units):.12f}/q "
          f"({128-log2(float(full_units)):.6f} bits); not a formal or full FS bound.")


def main():
    rows = [
        (75, 2487, 14, [2502, 2534, 2537, 2555, 2597, 2644, 2655, 2714,
                        2847, 2917, 3007, 3370, 4416], Fraction(861, 100)),
        (81, 2660, 7, [2714, 2847, 2917, 3007, 3370, 4416], Fraction(541, 100)),
        (81, 2714, 6, [2847, 2917, 3007, 3370, 4416], Fraction(541, 100)),
        (80, 2713, 7, [2714, 2847, 2917, 3007, 3370, 4416], Fraction(581, 100)),
    ]
    print("Local exposed-parent exception model only; remaining ROM bridge and roles excluded.")
    for queries, cutoff, bound, cuts, units in rows:
        assert len(cuts) + 1 == bound
        value = moment(queries, cuts, units)
        assert value <= units
        print(f"t={queries}, base cutoff={cutoff}, L={bound}: "
              f"exact moment <= {units} = {float(units):.2f}; "
              f"moment={float(value):.9f}, "
              f"safe local rate bits={128-log2(float(units)):.6f}")
    baseline = Fraction(comb(2713, 81), comb(N, 81)) * FIELD
    full_units = Fraction(541, 100) + baseline
    print("Actual fixed81 parent, with baseline and rank (rank <= baseline): "
          f"rate={float(full_units):.9f}/q, "
          f"local bits={128-log2(float(full_units)):.6f}; full ROM bridge excluded.")
    nonuniform_exploration()


if __name__ == "__main__":
    main()
