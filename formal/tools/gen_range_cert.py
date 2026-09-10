#!/usr/bin/env python3
"""Certify that the circuit's own `valid_index` polynomial vanishes exactly on the eight digits.

Usage: gen_range_cert.py vi.json > ../circuits/ECDSA/RangeCert.lean

`range_check/valid_index` asserts that a degree-8 interpolant vanishes on the wire. `Lagrange9`
already factors *a* copy of that polynomial, but not the circuit's: the compiler fuses the
evaluation, so products of residues appear that agree with the direct interpolant only modulo
`p`. `ring` cannot see that, which is why `linear_combination` against `Lagrange9` fails.

So certify the circuit's polynomial directly. Expand its cone symbolically -- it is univariate in
the digit wire, twelve nodes -- and factor:

    P(u) = lead * (u+8)(u+6)(u+4)(u+2)u(u-2)(u-4)(u-6)

with the residual given integrally as `p * W(u)`, the technique `ECDSA/NoRoot.lean` and
`gen_lagrange.py` both use. `W` is untrusted: a wrong one fails `ring`.

Input is the JSON `meaning_gen` dumps with `DUMP_CONE=valid_index`.
"""
import json
import sys

P = 115792089210356248762697446949407573530086143415290314195533631308867097853951


def polymul_int(a, b):
    """Same, but over the integers: this is what `ring` sees when the meaning chain is
    expanded, since the compiler's fused evaluation multiplies residues without reducing."""
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


def polyadd_int(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def polymul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % P
    return r


def polyadd(a, b):
    n = max(len(a), len(b))
    return [((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % P for i in range(n)]


def main():
    d = json.load(open(sys.argv[1]))
    nodes = {n["id"]: n for n in d["nodes"]}

    # The digit wire is the variable; `one` is the constant 1.
    digit = next(n["id"] for n in d["nodes"] if n.get("name", "").startswith("ers"))
    one = next(n["id"] for n in d["nodes"] if n.get("name") == "one")

    val = {}
    for n in d["nodes"]:
        i = n["id"]
        if "input" in n:
            val[i] = [0, 1] if i == digit else ([1] if i == one else None)
            assert val[i] is not None, f"unexpected input node {i}"
            continue
        acc = [0]
        for c, w0, w1 in n["sum"]:
            acc = polyadd(acc, polymul([int(c, 16)], polymul(val[w0], val[w1])))
        val[i] = acc

    # The same evaluation over the integers, with the *signed* constants the meaning chain
    # actually carries: `E2Meaning.consts_neg` writes a residue above `p/2` as `-(p - c)`, and
    # the two differ by `p` -- invisible to `ring`, and exactly the correction `Wred` supplies.
    def signed(c):
        return c if c <= P // 2 else c - P

    vali = {}
    for n in d["nodes"]:
        i = n["id"]
        if "input" in n:
            vali[i] = [0, 1] if i == digit else [1]
            continue
        acc = [0]
        for c, w0, w1 in n["sum"]:
            acc = polyadd_int(
                acc, polymul_int([signed(int(c, 16))], polymul_int(vali[w0], vali[w1]))
            )
        vali[i] = acc
    raw_coeffs = vali[d["root"]]
    raw_coeffs += [0] * (9 - len(raw_coeffs))

    coeffs = val[d["root"]]
    coeffs += [0] * (9 - len(coeffs))
    assert len(coeffs) == 9, f"degree {len(coeffs) - 1}, expected 8"

    nodesx = [2 * i - 8 for i in range(8)]
    lead = coeffs[8]
    prod = [1]
    for nk in nodesx:
        nxt = [0] * (len(prod) + 1)
        for j, a in enumerate(prod):
            nxt[j + 1] += a
            nxt[j] += -nk * a
        prod = nxt
    resid = [coeffs[j] - lead * prod[j] for j in range(9)]
    assert all(r % P == 0 for r in resid), "the circuit's range polynomial does not factor"
    W = [r // P for r in resid]

    def lit(v):
        return f"({v} : F)" if v >= 0 else f"(-{-v} : F)"

    def poly(cs, var="u"):
        return " + ".join(
            (lit(c) if j == 0 else f"{lit(c)} * {var}" if j == 1 else f"{lit(c)} * {var} ^ {j}")
            for j, c in enumerate(cs)
        )

    assert all((coeffs[j] - raw_coeffs[j]) % P == 0 for j in range(9)), "raw/reduced mismatch"
    # `linear_combination h + W*hp` checks `coeffs - raw - W*p = 0`, so W = (coeffs - raw)/p.
    Wred = [(coeffs[j] - raw_coeffs[j]) // P for j in range(9)]

    factors = " * ".join(
        ("u" if nk == 0 else f"(u + {-nk})" if nk < 0 else f"(u - {nk})") for nk in nodesx
    )
    pat = "h"
    for _ in range(8):
        pat = f"({pat} | h)"
    cases = ["  · exact absurd h hlead"]
    for idx in range(8):
        pre = "Or.inr (" * idx
        close = ")" * idx
        inner = "Or.inl (by linear_combination h)" if idx < 7 else "by linear_combination h"
        cases.append(f"  · exact {pre}{inner}{close}")

    print(f'''/-
# Copyright 2026 Google LLC.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
-/

import ECDSA.EcdsaV2

/-!
# `valid_index`, as the circuit actually computes it

Generated by `formal/tools/gen_range_cert.py`. Do not edit.

`Lagrange9.isDigit_of_range` factors a *directly interpolated* copy of the range polynomial. The
deployed circuit computes a fused one, and the two agree only modulo `p` — products of residues
appear that `ring` has no way to reduce. So this certifies the circuit's own polynomial: it
factors as `lead * (u+8)(u+6)(u+4)(u+2)u(u-2)(u-4)(u-6)`, with the residual given integrally as
`p * W u`. `W` is untrusted; a wrong one fails `ring`.
-/

namespace ECDSA2.RangeCert

variable {{F : Type}} [Field F] [CharP F {P}]

theorem hp : ({P} : F) = 0 := by
  exact_mod_cast CharP.cast_eq_zero F {P}

/-- The circuit's range polynomial, factored. -/
theorem factor (u : F) :
    {poly(coeffs)}
      = ({lead} : F) * {factors} := by
  linear_combination ({poly(W)}) * hp (F := F)

theorem lead_ne_zero : ({lead} : F) ≠ 0 := by
  have h : (({lead} : ℕ) : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F {P}]
    norm_num
  simpa using h

/-- **What `valid_index` buys**, from the deployed circuit's own assertion polynomial. -/
theorem isDigit_of_zero (u : F)
    (h : {poly(coeffs)} = 0) : ECDSA2.IsDigit u := by
  have hlead : ({lead} : F) ≠ 0 := lead_ne_zero (F := F)
  rw [factor] at h
  simp only [mul_eq_zero] at h
  rcases h with {pat}
{chr(10).join(cases)}

/-- **The form the meaning chain actually produces.** Expanding the cone leaves products of
    residues unreduced, so its coefficients differ from the reduced ones by multiples of `p`;
    `ring` cannot see that, and `Wred` supplies it. -/
theorem isDigit_of_zero_raw (u : F)
    (h : {poly(raw_coeffs)} = 0) : ECDSA2.IsDigit u := by
  refine isDigit_of_zero u ?_
  linear_combination h + ({poly(Wred)}) * hp (F := F)

end ECDSA2.RangeCert''')


main()
