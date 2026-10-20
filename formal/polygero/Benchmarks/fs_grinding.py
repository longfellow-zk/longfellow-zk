#!/usr/bin/env python3
"""Exact numerical separation for the concrete three-region search.

The Lean algebra, fresh search tree, ROM probability and protocol completion
are in Local/GrindingAlgebra and Recursion/FSGrinding*. This report evaluates
the same finite lower bound as Instances/FSGrinding. All certification
comparisons use fractions; decimal display does not affect the conclusion.
"""
from fractions import Fraction
from math import comb, log2

FIELD = 2**128
N = 8192
K = 512
S = 64
COMMON = K - 1
BLOCK = 2560
AGREEMENT = COMMON + BLOCK
assert COMMON + 3 * BLOCK + 1 == N
RANK = Fraction(comb(N, K + 2 * S + 1), FIELD ** (S + 1))
ROOT_HIT = Fraction(3, FIELD) - Fraction(2, FIELD**2)


def local_error(cutoff, queries):
    threshold = Fraction(comb(cutoff - 1, queries), comb(N, queries))
    return threshold + (1 - threshold) * (RANK + Fraction(1, FIELD))


def report(name, parent_queries, child_queries, cutoff0, cutoff1, budget_bits):
    query_hit = Fraction(comb(AGREEMENT, parent_queries), comb(N, parent_queries))
    total = 2**budget_bits
    child_attempts = (4 * query_hit.denominator + query_hit.numerator - 1) // query_hit.numerator
    parent_attempts = total - child_attempts - 2
    assert child_attempts >= 8 and parent_attempts > 0
    assert parent_attempts < FIELD and child_attempts < FIELD
    assert parent_attempts + child_attempts + 2 == total
    root_lower = parent_attempts * ROOT_HIT - comb(parent_attempts, 2) * ROOT_HIT**2
    prefix = sum(Fraction(comb(child_attempts, j)) * query_hit**j for j in range(9))
    child_lower = 1 - 1 / prefix
    terminal = Fraction(N - child_queries, N)
    success_lower = root_lower * child_lower * terminal
    e0 = local_error(cutoff0, parent_queries)
    e1 = local_error(cutoff1, child_queries)
    reference = e0 + (1 - e0) * e1
    no_loss_upper = (total + 1) * reference
    assert success_lower > no_loss_upper
    ratio = success_lower / no_loss_upper
    print(f"{name}: parent/child openings {parent_queries}/{child_queries}, N_RO=2^{budget_bits}")
    print(f"  root hit = 3/2^128 - 2/2^256; query-hit bits = {-log2(float(query_hit)):.8f}")
    print(f"  child search reserve / total = {float(Fraction(child_attempts, total)):.8f}")
    print(f"  actual-search success lower bound = {float(success_lower):.12g}")
    print(f"  proposed (N_RO+1)*IOP upper bound = {float(no_loss_upper):.12g}")
    print(f"  separation factor >= {float(ratio):.8f}; log2 factor = {log2(float(ratio)):.8f} bits")
    if parent_queries == 70:
        assert Fraction(17, 100000) < success_lower
        assert no_loss_upper < Fraction(123, 1000000)
        assert Fraction(7, 5) * no_loss_upper < success_lower
    else:
        assert Fraction(423, 10000) < success_lower
        assert no_loss_upper < Fraction(413, 10000)


def main():
    report("Original verified 70-opening row", 70, 70, 2109, 2109, 114)
    report("Retuned verified three-bit schedule", 81, 80, 2660, 2713, 122)
    print("The query budget counts the typed challenge oracle; Merkle construction costs are outside this model.")


if __name__ == "__main__":
    main()
