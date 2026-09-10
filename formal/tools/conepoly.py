#!/usr/bin/env python3
"""Expand an assertion cone into a multivariate polynomial, twice.

The meaning chain rewrites a cone into a nested expression over the input wires, and `ring`
normalises that **over the integers**. A goal written with Lean's own `addE` / `doubleE` is a
different integer polynomial that agrees only modulo `p`, because the circuit's constants are
residues and the chain multiplies them without reducing. `ring` cannot bridge that, so every
meaning lemma of any size needs the integral correction

    chain_expansion - goal_expansion = p * W

with `W` supplied as advice. This module computes both expansions and `W`.

Two conventions have to match the emitted Lean exactly or `W` is wrong in a way that only shows
up as a failed `ring`:

* a residue above `p/2` is written `-(p - c)` by `E2Meaning.consts_neg`, so the *signed* value is
  what the chain carries;
* `one` is the wire at position 0, pinned to `1` by the `hone` hypothesis before expansion.

Used as a library by the meaning generators.
"""

P = 115792089210356248762697446949407573530086143415290314195533631308867097853951


def signed(c: int) -> int:
    """The integer the meaning chain actually carries for residue `c`."""
    return c if c <= P // 2 else c - P


class Poly:
    """Sparse multivariate polynomial: {(exponent tuple): coefficient}."""

    __slots__ = ("nvars", "terms")

    def __init__(self, nvars: int, terms=None):
        self.nvars = nvars
        self.terms = dict(terms or {})

    @staticmethod
    def const(nvars: int, c: int) -> "Poly":
        return Poly(nvars, {(0,) * nvars: c} if c else {})

    @staticmethod
    def var(nvars: int, i: int) -> "Poly":
        e = [0] * nvars
        e[i] = 1
        return Poly(nvars, {tuple(e): 1})

    def __add__(self, other: "Poly") -> "Poly":
        r = dict(self.terms)
        for m, c in other.terms.items():
            v = r.get(m, 0) + c
            if v:
                r[m] = v
            else:
                r.pop(m, None)
        return Poly(self.nvars, r)

    def __sub__(self, other: "Poly") -> "Poly":
        return self + other.scale(-1)

    def scale(self, k: int) -> "Poly":
        if k == 0:
            return Poly(self.nvars)
        return Poly(self.nvars, {m: c * k for m, c in self.terms.items()})

    def __mul__(self, other: "Poly") -> "Poly":
        r: dict = {}
        for m1, c1 in self.terms.items():
            for m2, c2 in other.terms.items():
                m = tuple(a + b for a, b in zip(m1, m2))
                v = r.get(m, 0) + c1 * c2
                if v:
                    r[m] = v
                else:
                    r.pop(m, None)
        return Poly(self.nvars, r)

    def divide_by(self, p: int) -> "Poly":
        assert all(c % p == 0 for c in self.terms.values()), "not divisible"
        return Poly(self.nvars, {m: c // p for m, c in self.terms.items()})

    def lean(self, names) -> str:
        """As Lean source, over the given variable names."""
        if not self.terms:
            return "(0 : F)"
        parts = []
        for m, c in sorted(self.terms.items(), key=lambda kv: (sum(kv[0]), kv[0])):
            factors = []
            for i, e in enumerate(m):
                if e == 1:
                    factors.append(names[i])
                elif e > 1:
                    factors.append(f"{names[i]} ^ {e}")
            lit = f"({c} : F)" if c >= 0 else f"(-{-c} : F)"
            parts.append(lit if not factors else f"{lit} * " + " * ".join(factors))
        return " + ".join(parts)


def expand_cone(nodes, root, atoms, one_node):
    """Expand a cone over `atoms` (node id -> variable index), `one_node` pinned to 1.

    Returns the polynomial the meaning chain produces: signed constants, no reduction.
    """
    nvars = len(atoms)
    val = {}
    for n in nodes:
        i = n["id"]
        if i in atoms:
            val[i] = Poly.var(nvars, atoms[i])
            continue
        if i == one_node:
            val[i] = Poly.const(nvars, 1)
            continue
        if "input" in n:
            raise AssertionError(f"input node {i} is neither an atom nor `one`")
        acc = Poly(nvars)
        for c, w0, w1, _ki in n["sum"]:
            acc = acc + Poly.const(nvars, signed(int(c, 16))) * val[w0] * val[w1]
        val[i] = acc
    return val[root]


# --- Lean's RCB formulas, mirrored exactly (see `ECDSA/EC.lean`) ---------------

def addE(p1, p2, a, k3b):
    """`ECDSA.addE`, let for let. Inputs and outputs are `Poly`."""
    X1, Y1, Z1 = p1
    X2, Y2, Z2 = p2
    t0 = X1 * X2
    t1 = Y1 * Y2
    t2 = Z1 * Z2
    t3 = (X1 + Y1) * (X2 + Y2)
    t4 = t0 + t1
    t3_2 = t3 - t4
    t4_2 = (X1 + Z1) * (X2 + Z2)
    t5 = t0 + t2
    t4_3 = t4_2 - t5
    t5_2 = (Y1 + Z1) * (Y2 + Z2)
    X3t = t1 + t2
    t5_3 = t5_2 - X3t
    Z3t = a * t4_3
    X3t_2 = k3b * t2
    Z3t_2 = X3t_2 + Z3t
    X3t_3 = t1 - Z3t_2
    Z3t_3 = t1 + Z3t_2
    Y3t = X3t_3 * Z3t_3
    t1_2 = t0 + t0
    t1_3 = t1_2 + t0
    t2_2 = a * t2
    t4_4 = k3b * t4_3
    t1_4 = t1_3 + t2_2
    t2_3 = t0 - t2_2
    t2_4 = a * t2_3
    t4_5 = t4_4 + t2_4
    t0_2 = t1_4 * t4_5
    Y3t_2 = Y3t + t0_2
    t0_3 = t5_3 * t4_5
    X3t_4 = t3_2 * X3t_3
    X3t_5 = X3t_4 - t0_3
    t0_4 = t3_2 * t1_4
    Z3t_4 = t5_3 * Z3t_3
    Z3t_5 = Z3t_4 + t0_4
    return (X3t_5, Y3t_2, Z3t_5)


def doubleE(p, a, k3b):
    """`ECDSA.doubleE`, let for let."""
    X, Y, Z = p
    t0 = X * X
    t1 = Y * Y
    t2 = Z * Z
    t3 = X * Y
    t3_2 = t3 + t3
    Z3t = X * Z
    Z3t_2 = Z3t + Z3t
    X3t = a * Z3t_2
    Y3t = k3b * t2
    Y3t_2 = X3t + Y3t
    X3t_2 = t1 - Y3t_2
    Y3t_3 = t1 + Y3t_2
    Y3t_4 = X3t_2 * Y3t_3
    X3t_3 = t3_2 * X3t_2
    Z3t_3 = k3b * Z3t_2
    t2_2 = a * t2
    t3_3 = t0 - t2_2
    t3_4 = a * t3_3
    t3_5 = t3_4 + Z3t_3
    Z3t_4 = t0 + t0
    t0_2 = Z3t_4 + t0
    t0_3 = t0_2 + t2_2
    t0_4 = t0_3 * t3_5
    Y3t_5 = Y3t_4 + t0_4
    t2_3 = Y * Z
    t2_4 = t2_3 + t2_3
    t0_5 = t2_4 * t3_5
    X3t_4 = X3t_3 - t0_5
    Z3t_5 = t2_4 * t1
    Z3t_6 = Z3t_5 + Z3t_5
    Z3t_7 = Z3t_6 + Z3t_6
    return (X3t_4, Y3t_5, Z3t_7)
