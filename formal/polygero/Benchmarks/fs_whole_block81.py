#!/usr/bin/env python3
"""Display the exact rational complete 81/80 ABS bounds.

The independent Lean certificates are FSWholeBlock81.checked,
FSWholeBlock81.certifiedAffineFS, FSWholeBlock81.certifiedSoundness,
and FSDefect81.certifiedSoundness for the clean126 row.
FSCompletion81.certifiedSoundness_iop certifies the improved uniform row.
Decimal displays and bit conversions are not used by the Lean proofs.
"""
from fractions import Fraction
from math import comb, log2

Q = 2**128
N = 8192
MU = Fraction(comb(N, 641), Q**65)


def theta(t, a):
    return Fraction(comb(a - 1, t), comb(N, t))


def main():
    theta1 = theta(80, 2714)
    child_price = (1 - theta1) * MU + Fraction(2, Q) + theta1
    original_local = theta(70, 2109) + (1 - theta(70, 2109)) * (MU + Fraction(1, Q))
    original_iop = original_local + (1 - original_local) * original_local
    original_bits = -log2(float(original_iop))
    same0 = theta(81, 2714) + (1 - theta(81, 2714)) * (MU + Fraction(1, Q))
    same1 = theta1 + (1 - theta1) * (MU + Fraction(1, Q))
    same_iop = same0 + (1 - same0) * same1
    same_bits = -log2(float(same_iop))
    print(f"81/80 IOP field units at cutoff 2714/2714: {float(Q*same_iop):.12f}; {same_bits:.9f} bits")
    print(f"child whole-block field units: {float(Q * child_price):.12f}")
    print(f"original 70/70 IOP reference: {original_bits:.9f} bits")
    for name, units in [("fixed cutoff", Fraction(553, 100)),
                        ("lower parent cutoff", Fraction(543, 100)),
                        ("nonuniform support packing", Fraction(24, 5)),
                        ("defect-sensitive packing", Fraction(4))]:
        rho = units / Q
        assert child_price <= rho
        intercept = 2 * rho + child_price
        bits = -log2(float(rho))
        print(f"{name}: rho*q={float(units):.9f}; "
              f"intercept*q={float(Q*intercept):.12f}; "
              f"coefficient bits={bits:.9f}; "
              f"gap to original IOP={original_bits-bits:.9f}; "
              f"gap to cutoff-2714 IOP={same_bits-bits:.9f}")
        assert intercept <= 3 * rho
    defect_price = Fraction(4, Q)
    defect_intercept = 2 * defect_price + child_price
    assert defect_intercept <= 4 * same_iop and defect_price <= 4 * same_iop
    worst_uniform_factor = defect_intercept / same_iop
    print(f"defect row uniform affine/IOP factor <= {float(worst_uniform_factor):.9f} "
          f"({log2(float(worst_uniform_factor)):.9f} bits); Lean certifies factor 4 for every budget.")
    completed_intercept = defect_price + child_price
    fresh_pair_bound = MU + 6*theta(81, 2714) + (1+5*theta(81, 2714))/Q
    assert fresh_pair_bound <= defect_price
    assert completed_intercept <= Fraction(2345, 1000)*same_iop
    completed_positive_factor = (2*defect_price + child_price)/(2*same_iop)
    assert completed_positive_factor <= Fraction(1881, 1000)
    assert defect_price <= Fraction(1881, 1000)*same_iop
    print(f"joint completion: intercept*q={float(Q*completed_intercept):.12f}; "
          f"fresh-pair bound*q={float(Q*fresh_pair_bound):.12f}; "
          f"exact worst positive-budget factor={float(completed_positive_factor):.9f}")
    print(f"With the separately proved zero-query IOP bound, Lean certifies factor 1.881 "
          f"for every budget ({log2(1.881):.9f} bits).")
    print("All schedules keep 81/80 openings; decoding cutoffs affect only the analysis.")


if __name__ == "__main__":
    main()
