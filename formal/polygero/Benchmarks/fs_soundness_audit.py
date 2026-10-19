#!/usr/bin/env python3
"""Exact arithmetic and an explicit support-only relaxation.

The four sets below are NOT claimed to be Polygero affine closures.
They identify what pairwise support/defect bounds alone fail to exclude.
Lean independently checks the protocol-facing upper bound and references.
"""
from fractions import Fraction as F
from itertools import combinations
from math import comb, log2

Q = 2**128
MU = F(comb(8192, 641), Q**65)


def capacity(a, t=81):
    return F(comb(a, t), comb(8192, t))


def profile(theta):
    return theta + (1 - theta) * (MU + F(1, Q))


def two_error(a, b):
    return a + (1 - a) * b


def main():
    theta0, theta1 = capacity(2713), capacity(2713, 80)
    working = two_error(profile(theta0), profile(theta1))
    strong = []
    for t in (81, 80):
        eta = capacity(639, t)
        assert Q * (Q - 1) * eta <= 2
        strong.append(profile(max(capacity(1087, t), Q * eta / 2)))
    strong = two_error(*strong)
    tau = (1 - theta1) * MU + F(2, Q) + theta1
    print(f"working IOP error*q = {float(Q*working):.15f}")
    print(f"stronger same-verifier IOP error*q = {float(Q*strong):.15f}")
    print(f"reference difference = {log2(float(working/strong)):.9f} bits")
    for units in (F(4), F(397, 100)):
        rho = units / Q
        print(f"FS query price*q = {float(units):.9f}; intercept*q = {float(Q*(rho+tau)):.12f}")
        for label, reference in (("working", working), ("stronger", strong)):
            query_gap = log2(float(rho/reference))
            positive_factor = (2*rho + tau)/(2*reference)
            print(f"  vs {label}: query gap={query_gap:.9f} bits; "
                  f"worst positive-budget affine factor={float(positive_factor):.9f} "
                  f"({log2(float(positive_factor)):.9f} bits)")

    # Six disjoint pair blocks and four disjoint private blocks fill 8192.
    cores = [set() for _ in range(4)]
    cursor = 0
    for i, j in combinations(range(4), 2):
        block = set(range(cursor, cursor + 576))
        cores[i].update(block)
        cores[j].update(block)
        cursor += 576
    for core in cores:
        core.update(range(cursor, cursor + 1184))
        cursor += 1184
    assert cursor == 8192
    assert all(len(core) == 2912 for core in cores)
    assert all(len(cores[i] & cores[j]) == 576 for i, j in combinations(range(4), 2))
    assert len(set.union(*cores)) == 8192
    raw_capacity, defect = 2975, 1
    assert all(raw_capacity + defect <= len(core) + 64 for core in cores)
    assert raw_capacity >= 2714
    conditional = 6*theta0 + capacity(raw_capacity)
    barrier = 4*conditional/(Q*conditional + 4)
    assert F(395, 100)/Q < barrier
    assert working < barrier
    print(f"support-only four-state Bellman barrier*q = {float(Q*barrier):.12f}")
    print("This is a barrier to the present capacity relaxation, not a Polygero attack.")


if __name__ == "__main__":
    main()
