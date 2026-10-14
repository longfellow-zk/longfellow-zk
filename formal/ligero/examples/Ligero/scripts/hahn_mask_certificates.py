#!/usr/bin/env python3
"""Exact Delsarte certificates for the V1 unchecked-mask list (stdlib only).

The default generates one targeted higher-degree certificate per v7/v8
geometry. Its cutoff is selected against the complete extraction budget,
not by minimizing the list bound alone. The optional --frontier mode retains
the degree-five exact rational simplex search.

Candidate generation uses normalized Hahn polynomials to construct
(t - lam) * h(t)^2. Coefficients are converted to the actual four-cell Gram
kernels of CodingTheory.HahnDelsarte. The normalized-polynomial identity is
only a search aid: certificateValid checks every realizable overlap against
the proved Gram kernel, independently of the generator and its normalization.
No optimizer or analytical endpoint inequality is trusted by Lean.

Only the certificate at maskThreshold enters Lean. UniformFamilyBound.of_le_size
extends it to larger agreement sets; Johnson is retained above its threshold.
All coefficients, overlap checks, and floors use exact integer/rational arithmetic.

Usage (from formal/):
    hahn_mask_certificates.py --lean-module PATH   # reproduce targeted data
    hahn_mask_certificates.py --check PATH         # independently recheck data
    hahn_mask_certificates.py --frontier --json OUT # degree-five LP exploration
"""

import argparse
import json
import re
from fractions import Fraction
from math import comb, floor, gcd, isqrt, lcm, prod
from functools import lru_cache
from pathlib import Path

# (name, n, k) of every distinct v7/v8 V1 geometry.
GEOMETRIES = (
    ("v7Sig", 3187, 455),
    ("v7Hash1", 3230, 461),
    ("v7Hash2", 3318, 474),
    ("v7Hash3", 3352, 478),
    ("v7Hash4", 3436, 490),
    ("v8Sig", 3458, 494),
    ("v8Hash1", 4088, 584),
    ("v8Hash2", 4081, 583),
)

# Cutoffs certified against the concrete extraction theorems. These minimize
# degree among the tested cutoffs reaching 127 signature / 125 hash bits.
TARGET_CUTOFFS = {
    "v7Sig": 1665, "v7Hash1": 1681, "v7Hash2": 1728,
    "v7Hash3": 1744, "v7Hash4": 1788, "v8Sig": 1808,
    "v8Hash1": 2122, "v8Hash2": 2113,
}

DEGREE = 5        # Maximum Hahn degree searched; no global optimality claim.
DIGITS = 19       # significant digits of the integer certificates


def choose(a, b):
    return comb(a, b) if 0 <= b <= a else 0


def nsub(a, b):
    return a - b if a >= b else 0


# --------------------------------------------------------------- Hahn kernels
def hahn_weight(n, w, k, x):
    """Lean `hahnWeight`: (-1)^x * ((n + x) - (w + k)).choose x / w.choose x."""
    den = choose(w, x)
    if den == 0:
        return Fraction(0)
    num = choose(nsub(n + x, w + k), x)
    return Fraction(-num if x % 2 else num, den)


def hahn_kernel(n, w, k, t):
    """Lean `hahnKernel` (four-cell count)."""
    weights = [hahn_weight(n, w, k, x) for x in range(2 * k + 1)]
    wt, rest = nsub(w, t), nsub(n + t, 2 * w)
    total = Fraction(0)
    for i in range(k + 1):
        inner = Fraction(0)
        for a in range(i + 1):
            outer = choose(t, a) * choose(wt, nsub(i, a))
            if outer:
                tail = Fraction(0)
                for c in range(nsub(k, i) + 1):
                    cells = choose(wt, c) * choose(rest, nsub(nsub(k, i), c))
                    if cells:
                        tail += cells * weights[a + c]
                inner += outer * tail
        total += weights[i] * inner
    return total


def hahn_omega(n, w, k, i):
    """Classical normalized Hahn polynomial Q_k(i)/Q_k(0) of J(n, w)."""
    return sum(Fraction((-1) ** j * comb(k, j) * comb(n + 1 - k, j) * comb(i, j),
                        comb(w, j) * comb(n - w, j)) for j in range(k + 1))


# --------------------------------------------------------------- exact simplex
def simplex_max(columns, b):
    """max sum_j x_j  s.t.  sum_j x_j * columns[j] <= b,  x >= 0  (b >= 0).
    Returns ("optimal", value, duals) or ("unbounded", None, None)."""
    rows, m = len(b), len(columns)
    tableau = [[columns[j][r] for j in range(m)] +
               [Fraction(int(s == r)) for s in range(rows)] + [Fraction(b[r])]
               for r in range(rows)]
    objective = [Fraction(-1)] * m + [Fraction(0)] * (rows + 1)
    basis = [m + r for r in range(rows)]
    while True:
        enter = next((j for j in range(m + rows) if objective[j] < 0), None)
        if enter is None:
            break
        leave, best = None, None
        for r in range(rows):
            if tableau[r][enter] > 0:
                ratio = tableau[r][-1] / tableau[r][enter]
                if best is None or ratio < best or (ratio == best and basis[r] < basis[leave]):
                    leave, best = r, ratio
        if leave is None:
            return "unbounded", None, None
        pivot = tableau[leave][enter]
        prow = [v / pivot for v in tableau[leave]]
        tableau[leave] = prow
        for r in range(rows):
            factor = tableau[r][enter]
            if r != leave and factor:
                tableau[r] = [u - factor * v for u, v in zip(tableau[r], prow)]
        factor = objective[enter]
        objective = [u - factor * v for u, v in zip(objective, prow)]
        basis[leave] = enter
    return "optimal", objective[-1], [objective[m + r] for r in range(rows)]


def delsarte_dual(kernels, top, ts):
    """Exact Delsarte dual: min sum_k top_k y_k s.t. sum_k y_k H_k(t) <= -1, y >= 0.
    Column generation over the intersection sizes `ts`."""
    K = len(top)
    step = max(1, len(ts) // 32)
    active = sorted(set(range(0, len(ts), step)) | {0, len(ts) - 1})
    while True:
        columns = [[-kernels[k][j] for k in range(K)] for j in active]
        status, value, duals = simplex_max(columns, top)
        if status != "optimal":
            return status, None, None
        slack = [sum(duals[k] * kernels[k][j] for k in range(K)) + 1 for j in range(len(ts))]
        violated = sorted((j for j in range(len(ts)) if slack[j] > 0 and j not in active),
                          key=lambda j: -slack[j])[:8]
        if not violated:
            return "optimal", 1 + value, duals
        active = sorted(set(active) | set(violated))


def certificate(n, w, lam, degree=DEGREE):
    """Integer certificate [f0, ..., fK] and its certified bound, or None."""
    ts = [t for t in range(lam + 1) if 2 * w <= n + t]
    kernels = [[hahn_kernel(n, w, k, t) for t in ts] for k in range(1, degree + 1)]
    top = [hahn_kernel(n, w, k, w) for k in range(1, degree + 1)]
    status, lp_value, duals = delsarte_dual(kernels, top, ts)
    if status != "optimal":
        return None
    scale = Fraction(10 ** DIGITS) / max(duals)
    coeffs = [floor(y * scale) for y in duals]
    while coeffs and coeffs[-1] == 0:
        coeffs.pop()
    worst = max(sum(c * kernels[k][j] for k, c in enumerate(coeffs)) for j in range(len(ts)))
    if worst >= 0:
        return None
    f0 = floor(-worst)
    coeffs = [f0] + coeffs
    bound = check(n, w, lam, coeffs)
    assert bound is not None and bound >= floor(lp_value)
    return {"a": w, "coeffs": coeffs, "bound": bound, "lp": float(lp_value)}


def check(n, w, lam, coeffs):
    """Mirror of `certificateValid`/`certifiedBound`; None when invalid."""
    if not coeffs:
        return None
    f0, rest = coeffs[0], coeffs[1:]
    if f0 <= 0 or any(c < 0 for c in rest):
        return None

    def poly(t):
        return f0 + sum(c * hahn_kernel(n, w, k + 1, t) for k, c in enumerate(rest))

    if any(poly(t) > 0 for t in range(lam + 1) if 2 * w <= n + t):
        return None
    return max(0, floor(poly(w) / f0))


def frontier(name, n, k):
    """Certificates for every level strictly below the Johnson threshold, down
    to the first level at which this search produces no verified certificate."""
    lam = 2 * k - 1
    threshold = isqrt(n * lam) + 1
    levels = []
    a = threshold - 1
    while a > lam:
        cert = certificate(n, a, lam)
        if cert is None:
            break
        levels.append(cert)
        a -= 1
    levels.reverse()
    return {"name": name, "n": n, "k": k, "lambda": lam, "johnson_threshold": threshold,
            "mask_threshold": levels[0]["a"] if levels else threshold, "levels": levels}


def verify_hahn_identity(n, w, degree=DEGREE, samples=(0, 1, 7)):
    """H_k(t) = H_k(w) * Q_k(w - t)/Q_k(0) at a few admissible t (documentation check)."""
    tmin = nsub(2 * w, n)
    for k in range(1, degree + 1):
        hw = hahn_kernel(n, w, k, w)
        for d in samples:
            t = max(tmin, w - d - 400)
            assert hahn_kernel(n, w, k, t) == hw * hahn_omega(n, w, k, w - t), (n, w, k, t)


# -------------------------------------------- targeted polynomial candidates
Q = Fraction


def require(condition, message):
    if not condition:
        raise ValueError(message)


def falling(x, degree):
    return prod(range(x - degree + 1, x + 1))


def multiply(left, right):
    result = [0] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            result[i + j] += x * y
    return result


def evaluate(poly, x):
    value = 0
    for coefficient in reversed(poly):
        value = value * x + coefficient
    return value


@lru_cache(None)
def multiplicity(n, degree):
    return comb(n, degree) - (comb(n, degree - 1) if degree else 0)


@lru_cache(16384)
def recurrence(n, w, degree):
    a = Q((w - degree) * (n - w - degree) * (n - degree + 1),
          (n - 2 * degree) * (n - 2 * degree + 1))
    c = (recurrence(n, w, degree - 1)[0] *
         Q(multiplicity(n, degree - 1), multiplicity(n, degree))) if degree else Q(0)
    return a, Q(w) - a - c, c


def values_at(n, w, x, degree):
    values = [Q(1)]
    for j in range(degree):
        a, b, c = recurrence(n, w, j)
        require(a > 0, "Degenerate Hahn recurrence")
        values.append(((x - b) * values[j] - (c * values[j - 1] if j else 0)) / a)
    return values


@lru_cache(512)
def integer_basis(n, w, degree):
    """Return integer P_j and integer R_j with Q_j=P_j/R_j.

    Construct directly from the terminating hypergeometric formula, rather
    than the recurrence used to generate the endpoint certificates.
    """
    require(0 <= degree <= min(w, n - w), "Invalid Hahn degree or weight")
    result = []
    for j in range(degree + 1):
        polynomial, term = [0] * (j + 1), [1]
        for i in range(j + 1):
            coefficient = ((-1) ** i * comb(j, i) * falling(n + 1 - j, i) *
                           falling(w - i, j - i) * falling(n - w - i, j - i))
            for z, value in enumerate(term):
                polynomial[z] += coefficient * value
            term = multiply(term, [w - i, -1])
        normalizer = falling(w, j) * falling(n - w, j)
        divisor = gcd(normalizer, gcd(*polynomial))
        result.append((tuple(v // divisor for v in polynomial), normalizer // divisor))
    return result


def expand_hahn(n, w, polynomial):
    degree = len(polynomial) - 1
    basis = integer_basis(n, w, degree)
    residual, denominator = list(polynomial), 1
    coefficients = [Q(0)] * (degree + 1)
    for j in range(degree, -1, -1):
        p, normalizer = basis[j]
        leading, pivot = residual[j], p[j]
        require(pivot > 0, "Invalid Hahn leading coefficient")
        coefficients[j] = Q(leading * normalizer, denominator * pivot)
        residual = [pivot * residual[i] - leading * p[i] for i in range(j)]
        denominator *= pivot
        if residual:
            divisor = gcd(denominator, gcd(*residual))
            residual = [v // divisor for v in residual]
            denominator //= divisor
    return coefficients


def endpoint_factors(n, w, s, degree):
    values = values_at(n, w, s, degree + 1)
    total = sum(multiplicity(n, j) * values[j] for j in range(degree + 1))
    require(total != 0, "Zero endpoint denominator")
    c = values[-1] / total
    require(c < 0, "Endpoint constant must be negative")
    h = [Q(0)] * (degree + 1)
    h[degree] = 1 / recurrence(n, w, degree)[0]
    for j in range(degree, 0, -1):
        _, b, _ = recurrence(n, w, j)
        upper = recurrence(n, w, j + 1)[2] * h[j + 1] if j < degree else 0
        h[j - 1] = (-c * multiplicity(n, j) - (b - s) * h[j] - upper) / recurrence(n, w, j - 1)[0]
    require(all(v >= 0 for v in h), "Endpoint factor has a negative Hahn coefficient")
    require((recurrence(n, w, 0)[1] - s) * h[0] +
            (recurrence(n, w, 1)[2] * h[1] if degree else 0) == -c,
            "Endpoint polynomial is not divisible by x-s")
    bound = Q(comb(n, degree)) - total / values[-1]
    require(bound == (w - s) * sum(h) / (-c) and bound > 0, "Invalid endpoint ratio")
    return h, c, bound


def targeted_certificate(n, w, lam):
    """Construct a candidate, then check it against every actual Gram overlap."""
    values = values_at(n, w, lam, min(64, w, n - w))
    j = next(j for j in range(1, len(values)) if values[j] < 0)
    h, _, ratio = endpoint_factors(n, w, lam, j - 1)
    polynomial = [Q(0)] * j
    for weight, (basis, normalizer) in zip(h, integer_basis(n, w, j - 1)):
        for i, value in enumerate(basis):
            polynomial[i] += weight * Q(value, normalizer)
    scale = lcm(*(value.denominator for value in polynomial))
    polynomial = [int(value * scale) for value in polynomial]
    polynomial = multiply([-lam, 1], multiply(polynomial, polynomial))
    normalized = expand_hahn(n, w, polynomial)
    require(normalized[0] > 0 and all(value >= 0 for value in normalized),
            "Candidate has negative normalized coefficients")
    coefficients = [normalized[0]]
    for degree, value in enumerate(normalized[1:], 1):
        # The diagonal four-cell count simplifies to this sum of squares.
        diagonal = sum(hahn_weight(n, w, degree, i) ** 2 *
                       choose(w, i) * choose(n - w, degree - i)
                       for i in range(degree + 1))
        require(diagonal > 0, "Zero Gram diagonal")
        coefficients.append(value / diagonal)
    scale = lcm(*(value.denominator for value in coefficients))
    coefficients = [int(value * scale) for value in coefficients]
    divisor = gcd(*coefficients)
    coefficients = [value // divisor for value in coefficients]
    require(Q(evaluate(polynomial, w), normalized[0]) == ratio,
            "Inconsistent candidate diagonal")
    bound = check(n, w, lam, coefficients)
    require(bound is not None and bound == floor(ratio),
            "Candidate fails the independent Gram-kernel check")
    return {"a": w, "coeffs": coefficients, "bound": bound}

MODULE_HEADER = """/-! Integer Hahn/Delsarte certificates for the V1 unchecked-mask list.

Generated by `ligero/examples/Ligero/scripts/hahn_mask_certificates.py
--lean-module` (stdlib only: exact polynomial generation, exact Gram verification).
For a
V1 geometry `(n, k)` the certificate `[f₀, f₁, …, f_K]` is taken at the Delsarte
cutoff `a = maskThreshold`, selected against the complete extraction budget.
It certifies that `a`-subsets of `Fin n` meeting
pairwise in at most `2k - 1` points number at most
`HahnDelsarte.certifiedBound n a coeffs`, and by `UniformFamilyBound.of_le_size`
the same bound holds at every larger agreement.  Validity is checked by
`Certificate.maskValid` inside each record's `_parameters` theorem. -/

namespace Ligero.Examples.Grid.LongfellowProfiledExtraction.HahnMask
"""


def lean_module(results):
    lines = [MODULE_HEADER]
    for result in results:
        require(result["levels"], f"No certificate found for {result['name']}")
        top = result["levels"][0]
        lines.append(f"/-- `n = {result['n']}`, `k = {result['k']}`: cutoff "
                     f"{result['mask_threshold']} (Johnson threshold "
                     f"{result['johnson_threshold']}), bound {top['bound']}. -/")
        lines.append(f"def {result['name']} : List Nat :=\n  "
                     f"[{', '.join(map(str, top['coeffs']))}]\n")
    lines.append("end Ligero.Examples.Grid.LongfellowProfiledExtraction.HahnMask")
    return "\n".join(lines) + "\n"


def check_module(path):
    """Verify stored geometry, coefficients, and bounds without rerunning the LP."""
    text = Path(path).read_text()
    table = {name: (n, k) for name, n, k in GEOMETRIES}
    found = re.findall(
        r"/-- `n = (\d+)`, `k = (\d+)`: cutoff (\d+) "
        r"\(Johnson threshold (\d+)\), bound (\d+)\. -/\s*"
        r"def (\w+) : List Nat :=\s*\[([0-9,\s]+)\]", text)
    require(len(found) == len(table) and {row[5] for row in found} == set(table),
            "Missing or duplicate geometries")
    for stored_n, stored_k, weight, threshold, stored_bound, name, body in found:
        n, k = table[name]
        lam = 2 * k - 1
        require((int(stored_n), int(stored_k)) == (n, k), f"Wrong geometry for {name}")
        require(int(threshold) == isqrt(n * lam) + 1, f"Wrong Johnson threshold for {name}")
        coeffs = [int(x) for x in body.replace("\n", " ").split(",")]
        a = int(weight)
        require(lam < a < int(threshold), f"Invalid mask cutoff for {name}")
        bound = check(n, a, lam, coeffs)
        require(bound is not None, f"Invalid certificate for {name}")
        require(bound == int(stored_bound), f"Wrong stored bound for {name}")
        print(f"{name}: certificate at a={a} valid, bound {bound}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--lean-module", help="write the Lean data module to this path")
    parser.add_argument("--check", help="re-verify the certificates of a Lean data module")
    parser.add_argument("--json", help="write all level certificates to this JSON file")
    parser.add_argument("--frontier", action="store_true",
                        help="run the degree-five LP frontier search instead")
    parser.add_argument("--only", nargs="*", choices=[name for name, _, _ in GEOMETRIES], help="restrict to these geometry names")
    args = parser.parse_args()
    if args.check:
        check_module(args.check)
        return
    results = []
    for name, n, k in GEOMETRIES:
        if args.only and name not in args.only:
            continue
        lam = 2 * k - 1
        if args.frontier:
            verify_hahn_identity(n, isqrt(n * lam))
            result = frontier(name, n, k)
        else:
            cert = targeted_certificate(n, TARGET_CUTOFFS[name], lam)
            result = {"name": name, "n": n, "k": k, "lambda": lam,
                      "johnson_threshold": isqrt(n * lam) + 1,
                      "mask_threshold": cert["a"], "levels": [cert]}
        results.append(result)
        T, Tp = result["johnson_threshold"], result["mask_threshold"]
        first = result["levels"][0] if result["levels"] else None
        print(f"{name}: n={n} k={k} lambda={lam} Johnson threshold {T}, "
              f"Hahn threshold {Tp} ({T - Tp} levels)"
              + (f", bound at {Tp}: {first['bound']}" if first else ""), flush=True)
    if args.lean_module:
        Path(args.lean_module).write_text(lean_module(results))
    if args.json:
        with open(args.json, "w") as handle:
            json.dump(results, handle, indent=1)


if __name__ == "__main__":
    main()
