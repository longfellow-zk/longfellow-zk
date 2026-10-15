import os, sys, pickle, re, glob
# Output root, derived from this file rather than hardcoded: these scripts were written
# on a different machine and carried its absolute paths.
_SHAROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SP = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, SP)
NL = chr(10)
OUT = os.path.join(_SHAROOT, "circuits", "quadcert", "Bridge", "Sha256")
T = pickle.load(open(os.path.join(SP, "asserttbl.pkl"), "rb"))
idx = T["idx"]

def readbp(pat, name_re):
    out = {}
    for f in glob.glob(pat):
        s = open(f).read()
        for m in re.finditer(r'def (' + name_re + r') : List \(Nat × Nat\) :=\s*\n\s*\[(.*?)\]\s*\n', s, re.S):
            out[m.group(1)] = [int(a) for a, b in re.findall(r'\((\d+),\s*(\d+)\)', m.group(2))]
    return out

B = OUT
sched = readbp(B + "/S2Sched?.lean", r"bpS\d+")
r6    = {k: v for k, v in readbp(B + "/S2Rnd?.lean", r"bpR6_\d+").items()}
r7    = {k: v for k, v in readbp(B + "/S2Rnd?.lean", r"bpR7_\d+").items()}
fin   = readbp(B + "/S2Final.lean", r"bpF\d+")
finL  = readbp(B + "/S2Final.lean", r"bpLF\d+")
print("tables:", len(sched), len(r6), len(r7), len(fin), len(finL))

def bisect(vals, lo, hi, var="q"):
    if hi - lo == 1: return str(vals[lo])
    mid = (lo + hi) // 2
    return f"if {var} < {mid} then {bisect(vals, lo, mid, var)} else {bisect(vals, mid, hi, var)}"

fams = [
    ("Sched", sched, "bpS", 16, 64, 160, "bpSchedAt", 16),
    ("R6",    r6,    "bpR6_", 0, 64, 224, "bpR6At", 0),
    ("R7",    r7,    "bpR7_", 0, 64, 288, "bpR7At", 0),
    ("Fin",   fin,   "bpF",  0, 8,  96,  "bpAt",  0),
    ("FinL",  finL,  "bpLF", 0, 8,  96,  "bpLAt", 0),
]
o = []; A = o.append
A('''/-
# The bridges' assertion hypotheses, from `Accepts`

Every node the 176 meaning bridges name is an asserted node of the artifact. `S2Flat.zeroFlat`
gives "the node at flat index `k` is zero"; this file supplies, per family, the flat index of
each named node and cashes that in for the hypothesis the bridge actually asks for.

42,168 references in all, over 6,840 assertions. The `decide`s are chunked because the cost is
dominated by the `getD` into each family's table, not by the bisections.
-/

import quadcert.Bridge.Sha256.S2Flat
import quadcert.Bridge.Sha256.S2Assemble

set_option maxRecDepth 8000000
set_option maxHeartbeats 4000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk
''')
for nm, tbl, pref, lo, hi, width, atname, base in fams:
    flatvals = []
    for t in range(lo, hi):
        row = tbl[f"{pref}{t}"]
        assert len(row) == width, (nm, t, len(row))
        flatvals += [idx[n] for n in row]
    A(f"/-- Flat assert index of reference `(t, j)` in the `{nm}` family. -/")
    A(f"def k{nm} (t j : Nat) : Nat :=")
    A(f"  let q := (t - {base}) * {width} + j")
    A("  " + bisect(flatvals, 0, len(flatvals)))
    A("")
# ---- chunked agreement decides + the family hypotheses ----
CH = {"Sched": 12, "R6": 20, "R7": 26, "Fin": 2, "FinL": 2}
for nm, tbl, pref, lo, hi, width, atname, base in fams:
    n = hi - lo
    nch = CH[nm]
    per = (n + nch - 1) // nch
    for c in range(nch):
        a, b = lo + c * per, min(lo + (c + 1) * per, hi)
        if a >= b: continue
        A(f"theorem ok{nm}{c} : ((List.range {b - a}).map (fun t => t + {a})).all")
        A(f"    (fun t => (List.range {width}).all (fun j =>")
        A(f"      decide (k{nm} t j < 6840 ∧ assertNode (k{nm} t j) = (({atname} t).getD j (0, 0)).1))) = true := by")
        A("  decide +kernel")
        A("")
    A(f"theorem ok{nm} : ∀ t, {lo} ≤ t → t < {hi} → ∀ j, j < {width} →")
    A(f"    k{nm} t j < 6840 ∧ assertNode (k{nm} t j) = (({atname} t).getD j (0, 0)).1 := by")
    A(f"  intro t hlo hhi j hj")
    for c in range(nch):
        a, b = lo + c * per, min(lo + (c + 1) * per, hi)
        if a >= b: continue
        A(f"  by_cases h{c} : t < {b}")
        A(f"  · have hb := ok{nm}{c}")
        A(f"    simp only [List.all_eq_true, List.mem_map, List.mem_range, decide_eq_true_eq] at hb")
        A(f"    exact hb t ⟨t - {a}, by omega, by omega⟩ j hj")
    A("  omega")
    A("")
A("variable {F : Type} [Field F]")
A("")
for nm, tbl, pref, lo, hi, width, atname, base in fams:
    A(f"""/-- The `{nm}` family's hypothesis, from `Accepts`. -/
theorem hb{nm} (inputs : Nat → F)
    (hacc : ∀ r ∈ raw.toRecs, interpDag (raw.toDag (cnstw F)) inputs r.assertedNode = 0) :
    ∀ t, {lo} ≤ t → t < {hi} → ∀ j, j < {width} →
      interpDag (raw.toDag (cnstw F)) inputs (({atname} t).getD j (0, 0)).1 = 0 := by
  intro t hlo hhi j hj
  obtain ⟨hk, heq⟩ := ok{nm} t hlo hhi j hj
  rw [← heq]
  exact zeroFlat inputs hacc (k{nm} t j) hk
""")
open(os.path.join(OUT, "S2Assert.lean"), "w").write(NL.join(o) + NL + "end Sha256Blk" + NL)
print("emitted S2Assert.lean with decides")
