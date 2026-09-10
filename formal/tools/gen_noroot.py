#!/usr/bin/env python3
"""Generate a Lean certificate that x^3 + a*x + b has no root in F_p.

Usage: gen_noroot.py P A B NAME PREFIX > ../circuits/ECDSA/<Name>NoRoot.lean

    P A B    curve field prime and the depressed-cubic coefficients (any int literal form)
    NAME     used for the theorem name, `<NAME>_cubic_no_root`
    PREFIX   one-letter namespace prefix for the abbrevs, e.g. `p` -> pp/pa/pb

Requires `ECDSA.Pratt` to already contain `prime_<P>`.

Advice produced (all of it untrusted -- wrong values fail their own checks in Lean):
  rTri = X^p mod f   (checked by reducing `powTri` in the kernel)
  U, V with U*f + V*g = 1 + p*W over ZZ, where g = rTri - X

The `p*W` term is the point worth remembering: `ring` cannot reduce modulo p, so a Bezout
identity stated over `ZMod p` will not close.  Certifying it *integrally* and letting
`(p : ZMod p) = 0` erase the remainder is what makes `linear_combination` discharge it.

Reproduce the known-good P-256 certificate (byte-identical advice) with:
    gen_noroot.py \\
      115792089210356248762697446949407573530086143415290314195533631308867097853951 \\
      115792089210356248762697446949407573530086143415290314195533631308867097853948 \\
      41058363725152142129326129780047268409114441015993725554835256314039467401291 \\
      p256 p
"""
import sys, json

def polymulmod(u, v, p):
    r = [0] * (len(u) + len(v) - 1)
    for i, a in enumerate(u):
        if a:
            for j, b in enumerate(v):
                r[i + j] = (r[i + j] + a * b) % p
    return r

def trim(u):
    while len(u) > 1 and u[-1] == 0:
        u = u[:-1]
    return u

def polydivmod(u, v, p):
    u = list(u); v = trim(list(v))
    dv = len(v) - 1
    inv = pow(v[-1], p - 2, p)
    q = [0] * max(1, len(u) - dv)
    while len(trim(u)) - 1 >= dv and trim(u) != [0]:
        u = trim(u)
        d = len(u) - 1 - dv
        c = u[-1] * inv % p
        if d >= len(q):
            q += [0] * (d + 1 - len(q))
        q[d] = c
        for i, b in enumerate(v):
            u[i + d] = (u[i + d] - c * b) % p
        u = trim(u)
        if u == [0]:
            break
    return trim(q), trim(u)

def polysub(u, v, p):
    n = max(len(u), len(v))
    return trim([( (u[i] if i < len(u) else 0) - (v[i] if i < len(v) else 0) ) % p for i in range(n)])

def polymul(u, v, p):
    return trim(polymulmod(u, v, p))

def egcd(a, b, p):
    """returns (g, s, t) with s*a + t*b = g in GF(p)[X]."""
    r0, r1 = trim(list(a)), trim(list(b))
    s0, s1 = [1], [0]
    t0, t1 = [0], [1]
    while r1 != [0]:
        q, r = polydivmod(r0, r1, p)
        r0, r1 = r1, r
        s0, s1 = s1, polysub(s0, polymul(q, s1, p), p)
        t0, t1 = t1, polysub(t0, polymul(q, t1, p), p)
    return r0, s0, t0

def xpowmod(e, f, p):
    """X^e mod f in GF(p)[X], f monic of degree 3."""
    def red(u):
        u = list(u)
        while len(u) > 3:
            c = u.pop()
            d = len(u) - 3   # coefficient of X^(d+3)
            for i, fc in enumerate(f[:-1]):
                u[i + d] = (u[i + d] - c * fc) % p
            u = trim(u)
        return u + [0] * (3 - len(u))
    result = [1, 0, 0]
    base = [0, 1, 0]
    while e:
        if e & 1:
            result = red(polymulmod(result, base, p))
        base = red(polymulmod(base, base, p))
        e >>= 1
    return result

def zmul(u, v):
    r = [0] * (len(u) + len(v) - 1)
    for i, a in enumerate(u):
        for j, b in enumerate(v):
            r[i + j] += a * b
    return r

def zadd(u, v):
    n = max(len(u), len(v))
    return [(u[i] if i < len(u) else 0) + (v[i] if i < len(v) else 0) for i in range(n)]

def main():
    p = int(sys.argv[1], 0)
    a = int(sys.argv[2], 0) % p
    b = int(sys.argv[3], 0) % p
    name = sys.argv[4]          # e.g. "secp256k1"
    prefix = sys.argv[5]        # e.g. "sq" -> sq/sa/sb abbrevs

    f = [b, a, 0, 1]
    r = xpowmod(p, f, p)                     # X^p mod f
    g = [r[0], (r[1] - 1) % p, r[2]]         # rTri - X, mod p
    gg, s, t = egcd(f, g, p)
    assert len(gg) == 1 and gg[0] != 0, f"gcd is not constant: degree {len(gg)-1}"
    inv = pow(gg[0], p - 2, p)
    U = [c * inv % p for c in s]
    V = [c * inv % p for c in t]

    # Integral witness: U*f + V*g - 1 = p*W over ZZ, with g taken over ZZ as rTri - X.
    gZ = [r[0], r[1] - 1, r[2]]
    lhs = zadd(zmul(U, f), zmul(V, gZ))
    lhs[0] -= 1
    W = []
    for c in lhs:
        assert c % p == 0, "Bezout residual not divisible by p"
        W.append(c // p)
    while len(W) > 1 and W[-1] == 0:
        W.pop()

    print(json.dumps({"p": p, "a": a, "b": b, "r": r, "U": U, "V": V, "W": W}, indent=1)[:200],
          file=sys.stderr)

    def poly(cs, var="x"):
        parts = []
        for i, c in enumerate(cs):
            if c == 0 and len(cs) > 1:
                continue
            lit = f"({c} : ZMod {prefix}p)" if c >= 0 else f"(-{-c} : ZMod {prefix}p)"
            if i == 0:
                parts.append(lit)
            elif i == 1:
                parts.append(f"{lit} * {var}")
            else:
                parts.append(f"{lit} * {var}^{i}")
        return " + ".join(parts) if parts else f"(0 : ZMod {prefix}p)"

    P = prefix
    out = f'''module

public import ECDSA.NoRoot
public import ECDSA.Pratt

/-!
# The {name} cubic has no root in `F_p`

`x^3 + a*x + b` is the {name} curve equation, so this is exactly
`CurveHasNoPointsOfOrder2 {name}_params`.  Everything below is a *checked certificate*:

* `{P}rTri` is `X^p mod f`, verified by reducing `powTri` in the kernel;
* `U, V` are Bezout polynomials with `U*f + V*g = 1` where `g = {P}rTri - X`;
* `W` witnesses that identity integrally, `U*f + V*g - 1 = p*W` over `ZZ`, which is what lets
  `linear_combination` discharge it with `ring` -- `ring` cannot reduce modulo `p`, but it can
  verify an identity that holds over `ZZ`, and `(p : ZMod p) = 0` removes the remainder.
-/

@[expose] public section

set_option maxRecDepth 100000
set_option exponentiation.threshold 400

namespace ECDSA

abbrev {P}p : ℕ := {p}
abbrev {P}a : ℕ := {a}
abbrev {P}b : ℕ := {b}

/-- `X^p mod (X^3 + {P}a*X + {P}b)`, as advice. -/
def {P}rTri : Tri := ({r[0]}, {r[1]}, {r[2]})

theorem {P}rTri_ok : powTri {P}p {P}a {P}b 300 (0, 1, 0) {P}p = {P}rTri := by decide

instance : Fact (Nat.Prime {P}p) := ⟨prime_{p}⟩

theorem {name}_cubic_no_root (x : ZMod {P}p) :
    x ^ 3 + ({P}a : ZMod {P}p) * x + ({P}b : ZMod {P}p) ≠ 0 := by
  intro h1
  -- `x` is also a root of `g = {P}rTri - X`, because `x^p = x`.
  have hx : evalTri {P}rTri x = x := by
    have h := evalTri_powTri {P}p {P}a {P}b x h1 300 (0, 1, 0) {P}p (by decide)
    rw [{P}rTri_ok] at h
    simpa [evalTri, ZMod.pow_card] using h
  have h2 : ({r[0]} : ZMod {P}p) + ({r[1]} : ZMod {P}p) * x + ({r[2]} : ZMod {P}p) * x ^ 2 - x = 0 := by
    simp only [evalTri, {P}rTri] at hx
    push_cast at hx
    linear_combination hx
  have hp : ({p} : ZMod {P}p) = 0 := by exact_mod_cast ZMod.natCast_self {P}p
  push_cast at h1
  have : (1 : ZMod {P}p) = 0 := by
    linear_combination ({poly(U)}) * h1 + ({poly(V)}) * h2 - ({poly(W)}) * hp
  exact one_ne_zero this

end ECDSA

end
'''
    sys.stdout.write(out)

main()
