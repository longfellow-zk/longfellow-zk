import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
_HERE = _os.path.dirname(_os.path.abspath(__file__))
"""Emit the schedule bridge for one instance, to measure the regrouping `ring`."""
import re, sys, os
_sys.path.insert(0, _HERE)
from sha_parse import P256
from sha_classify import asserts, kind, nodes, consts, layout

ONE = {0, 238}
def sg(c):
    v = consts[c]; return v - P256 if v > P256//2 else v
def lname(n):
    k, v = nodes[n]
    return layout.get(v) if k == 'input' else None
def unwrap(n):
    k, v = nodes[n]
    if k == 'sum' and len(v) == 1:
        c, a, b = v[0]
        return b if a in ONE else a
    return n
def xlegs(n):
    k, v = nodes[n]
    if k == 'sum' and len(v) == 3: return (v[0][2], v[1][2])
    return None

sched = [(r,f) for (r,_,_) in asserts for (t,f) in [kind(r)] if t=='wrap' and len(f)==6]
root, facs = sched[0]
z = [n for n in facs if nodes[n][0]=='sum' and len(nodes[n][1])>10][0]

# ---- cone census & template indices ----
seen, stack = set(), [z]
while stack:
    n = stack.pop()
    if n in seen: continue
    seen.add(n)
    if nodes[n][0]=='sum':
        for c,a,b in nodes[n][1]: stack.extend([a,b])
leaves = sorted(n for n in seen if nodes[n][0]=='input')
leaves.remove(0); leaves = [0] + leaves          # node 0 must be template index 0
mids   = sorted(n for n in seen if nodes[n][0]=='sum' and n != z)
L, M = len(leaves), len(mids)
ti = {n: i for i, n in enumerate(leaves)}
ti.update({n: L + j for j, n in enumerate(mids)})
ti[z] = L + M
print(f"root {root} z {z}: L={L} mids={M} root idx={L+M}")

# ---- words ----
words = {}
for n in leaves:
    nm = lname(n)
    m = re.match(r'(.*)_(\d+)$', nm or "")
    if not m:
        print("  non-indexed leaf:", n, nm); continue
    words.setdefault(m.group(1), {})[int(m.group(2))] = n
print("words in cone:", {k: len(v) for k, v in sorted(words.items())})

# ---- sigma pairings from the quadratic root terms ----
pair = {}          # (wordname, out-bit j) -> (xor mid node, third leaf node)
for c,a,b in nodes[z][1]:
    if a in ONE or b in ONE: continue
    W = -sg(c) // 2
    u, other = (a, b) if xlegs(a) else (b, a)
    d = unwrap(other)
    la, lb = (lname(l) for l in xlegs(u))
    w = re.match(r'(.*)_\d+$', la).group(1)
    j = W.bit_length() - 1
    pair[(w, j)] = (u, d)
print("paired sigma bits:", len(pair))

# ---- classify the four source words ----
paircount = {}
for (w, j) in pair: paircount[w] = paircount.get(w, 0) + 1
s0w = [w for w, c in paircount.items() if c == 29][0]     # shr 3  -> 3 bits lose the third leg
s1w = [w for w, c in paircount.items() if c == 22][0]     # shr 10 -> 10 bits do
outw = [w for w in words if w.startswith('outw')][0]
plain = sorted(set(words) - {s0w, s1w, outw})
print(f"sigma0 <- {s0w}   sigma1 <- {s1w}   plain {plain}   out {outw}")

ROT = {s0w: (7, 18, 3), s1w: (17, 19, 10)}
def sigma_entry(w, j):
    r1, r2, sh = ROT[w]
    bits = words[w]
    spec = {(j + r1) % 32, (j + r2) % 32} | ({j + sh} if j + sh < 32 else set())
    if (w, j) in pair:
        u, d = pair[(w, j)]
        got = {int(re.match(r'.*_(\d+)$', lname(l)).group(1)) for l in xlegs(u)}
        got.add(int(re.match(r'.*_(\d+)$', lname(d)).group(1)))
        assert got == spec, (w, j, sorted(got), sorted(spec))
        return f"Quadcert.xorVal (V {ti[u]}) (lv {ti[d]})"
    else:
        a, b = bits[(j + r1) % 32], bits[(j + r2) % 32]
        assert spec == {(j + r1) % 32, (j + r2) % 32}, (w, j, sorted(spec))
        return f"Quadcert.xorVal (lv {ti[a]}) (lv {ti[b]})"

groups = {}
for w in (s0w, plain[0], s1w, plain[1]):
    if w in ROT:
        groups[w] = [(2**j, sigma_entry(w, j)) for j in range(31, -1, -1)]
    else:
        groups[w] = [(2**j, f"lv {ti[words[w][j]]}") for j in range(31, -1, -1)]
dsg = [(2**j, f"lv {ti[words[outw][j]]}") for j in range(31, -1, -1)]
print("groups built:", {w: len(g) for w, g in groups.items()}, "ds", len(dsg))
print("spec check passed for all sigma bits")

# ---- mids ----
copies, xors, merged = [], [], None
for n in mids:
    tms = nodes[n][1]
    if len(tms) == 1:   copies.append(n)
    elif len(tms) == 3: xors.append(n)
    else:               merged = n
print(f"mids: {len(copies)} copies, {len(xors)} xors, merged={merged} ({len(nodes[merged][1])} terms)")

# ---------------------------------------------------------------- emit
OUT = "/Users/abhi/Projects/longfellow-zk/formal/circuits/quadcert/Bridge/Sha256/S2Sched0.lean"
def T(n): return ti[n]
mid_terms = {n: [(k, T(a), T(b)) for k, a, b in nodes[n][1]] for n in mids}
ts_terms  = [(k, T(a), T(b)) for k, a, b in nodes[z][1]]
jm = T(merged) - L
ks = sorted({k for k, _, _ in ts_terms} | {k for n in mids for k, _, _ in mid_terms[n]})

def cdef(k):
    v = sg(k)
    return (f"  have c{k} : cnstw F {k} = (({v} : Nat) : F) := cnstw_pos {k} {v} (by rfl)" if v > 0
            else f"  have c{k} : cnstw F {k} = -(({-v} : Nat) : F) := cnstw_neg {k} {-v} (by rfl) (by norm_num)")

lst = lambda xs: "[" + ", ".join(xs) + "]"
Lst = []; A = Lst.append
A(f"""/-
# Schedule instance 0: `W16 = σ₀(W1) + W9 + σ₁(W14) + W0`, asserted at node {root}

Generated by `tools/gen_sched.py`. Do not edit. One of the 48 `sha256/schedule/N` assertions,
carried to the four-addend form `SHA256F.wrap_four_words` consumes.

Cone census: {L} leaves, {len(copies)} copy mids, {len(xors)} xor mids, one merged
{len(nodes[merged][1])}-term linear mid, root at index {L+M}.

The regrouping this file performs is step 3 of the schedule bridge. The circuit does not keep the
four addends apart: for a three-way σ output bit at weight `2^j` it emits `2^j·u` and
`-2^(j+1)·u·c` in the root but puts `2^j·c` inside the merged node, and it folds every remaining
linear term of all four addends into that same node. `tmpl_zS0` reassembles them, and the
reassembly is checked by `ring`.

Two choices keep that `ring` tractable. The xor mids stay **atoms** -- `midLeafVal` is never
unfolded at them, so the identity is degree 2 over ~{L + len(xors)} atoms rather than degree 3 over
{L}. The copy mids *are* rewritten to their leaves, because the merged node refers to the same bits
directly and the two spellings must meet.

The σ leg indices were checked against `SHA256.sigma0`/`sigma1` at generation time; `SHA/Sigma.lean`
turns that into a proof in step 4.
-/

import quadcert.Core.ConeXor
import quadcert.Bridge.Sha256.S2TmplZ

set_option maxRecDepth 8000000
set_option maxHeartbeats 4000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

variable {{F : Type}} [Field F]
""")
A(f"/-- The merged linear mid: {len(nodes[merged][1])} terms carrying the linear part of all four addends. -/")
A(f"def mergedS0 : List (Nat × Nat × Nat) :=\n  " + lst(f"({k}, {a}, {b})" for k,a,b in mid_terms[merged]) + "\n")
A("/-- The mid layer, as a function: copies and xors inline, the merged node by name. -/")
A("def mvS0 : Nat → List (Nat × Nat × Nat)")
for n in mids:
    j = T(n) - L
    A(f"  | {j} => " + (f"mergedS0" if n is merged else lst(f"({k}, {a}, {b})" for k,a,b in mid_terms[n])))
A("  | _ => []\n")
A(f"def tsS0 : List (Nat × Nat × Nat) :=\n  " + lst(f"({k}, {a}, {b})" for k,a,b in ts_terms) + "\n")
A(f"""def tnS0 : List TmplNode :=
  (List.range {L}).map (fun i => (TmplNode.leaf i : TmplNode))
    ++ (List.range {M}).map (fun j => TmplNode.sum (mvS0 j)) ++ [TmplNode.sum tsS0]

def mpS0 : List Nat :=
  """ + lst(str(n) for n in (leaves + mids + [z])) + "\n")
names = ["gS0a", "gS0b", "gS0c", "gS0d"]
for nm, w in zip(names, (s0w, plain[0], s1w, plain[1])):
    A(f"/-- Addend group: `{w}`. -/")
    A(f"def {nm} (lv : Nat → F) : List (Nat × F) :=\n  "
      + lst(f"({wt}, {e})".replace("V ", f"midLeafVal (cnstw F) lv {L} mvS0 ") for wt, e in groups[w]) + "\n")
A(f"/-- The output word `{outw}`. -/")
A(f"def dsS0 (lv : Nat → F) : List (Nat × F) :=\n  " + lst(f"({wt}, {e})" for wt, e in dsg) + "\n")

copy_haves = []
for n in copies:
    idx = T(n); leaf = T(unwrap(n))
    k, a, b = nodes[n][1][0]
    lem = "midLeafVal_copy_at" if a in ONE else "midLeafVal_copyR_at"
    copy_haves.append(f"  have k{idx} : midLeafVal (cnstw F) lv {L} mvS0 {idx} = lv {leaf} :=\n"
                      f"    {lem} (cnstw F) lv {L} mvS0 0 c0 hone {idx} {idx - L} (by norm_num) {leaf} (by rfl)")
A(f"""/-- **The regrouping.** `z` equals the four addend groups minus the output word. -/
theorem tmpl_zS0 [CharP F p256w] (lv : Nat → F) (hone : lv 0 = 1) :
    interpDag (tmplDag (cnstw F) tnS0) lv {L+M}
      = (((gS0a lv ++ gS0b lv ++ gS0c lv ++ gS0d lv)).map (fun q => (q.1 : F) * q.2)).sum
        - ((dsS0 lv).map (fun q => (q.1 : F) * q.2)).sum := by
  rw [show ({L+M} : Nat) = {L} + {M} from rfl,
    show tnS0 = (List.range {L}).map (fun i => (TmplNode.leaf i : TmplNode))
      ++ (List.range {M}).map (fun j => TmplNode.sum (mvS0 j)) ++ [TmplNode.sum tsS0] from rfl,
    interpDag_leafMidSum (cnstw F) lv {L} {M} mvS0 tsS0 (by decide +kernel) (by decide +kernel)]
  have c0 : cnstw F 0 = 1 := cnstw_0""")
A("\n".join(cdef(k) for k in ks if k != 0))
A("\n".join(copy_haves))
A(f"""  have mm : midLeafVal (cnstw F) lv {L} mvS0 {T(merged)}
      = mergedS0.foldl (fun acc t => acc + cnstw F t.1 * lv t.2.1 * lv t.2.2) 0 := by
    rw [midLeafVal_expand_at (cnstw F) lv {L} mvS0 {T(merged)} {jm} (by norm_num)]
    rfl
  simp only [tsS0, mergedS0, gS0a, gS0b, gS0c, gS0d, dsS0, Quadcert.xorVal, mm,
    {", ".join('k'+str(T(n)) for n in copies)},
    List.map_cons, List.map_nil, List.map_append, List.sum_cons, List.sum_nil, List.sum_append,
    List.foldl_cons, List.foldl_nil, hone, c0, {", ".join('c'+str(k) for k in ks if k != 0)}]
  push_cast
  ring

end Sha256Blk""")
open(OUT, "w").write("\n".join(Lst) + "\n")
print("emitted", OUT)
