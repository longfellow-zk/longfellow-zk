import os, sys, pickle
# Output root, derived from this file rather than hardcoded: these scripts were written
# on a different machine and carried its absolute paths.
_SHAROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SP = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, SP)
NL = chr(10)
OUT = os.path.join(_SHAROOT, "circuits", "quadcert", "Bridge", "Sha256")
T = pickle.load(open(os.path.join(SP, "asserttbl.pkl"), "rb"))
flat = T["flat"]
def bisect(vals, lo=0, hi=None, ind=0):
    hi = len(vals) if hi is None else hi
    if hi - lo == 1: return str(vals[lo])
    mid = (lo + hi) // 2
    return f"if k < {mid} then {bisect(vals, lo, mid)} else {bisect(vals, mid, hi)}"
o = []; A = o.append
A('''/-
# The assert list as a flat bisection

`zeroAt` gives every assertion by (sublist, position). The bridges name nodes. `assertNode` is
the flat index -> node bisection, and `assertNode_ok` is the one place the two meet: a `decide`
that the bisection agrees with the list, chunked so no single one exceeds the memory cap.

The sublist/position of a flat index is arithmetic, not a table: sublist 0 holds 205 entries and
the rest hold 22 (the last 13), so `k < 205` is sublist 0 and otherwise `(k-205)/22 + 1`.
-/

import quadcert.Bridge.Sha256.S2Connect

set_option maxRecDepth 8000000
set_option maxHeartbeats 4000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

/-- Sublist holding flat index `k`. -/
def subOfK (k : Nat) : Nat := if k < 205 then 0 else (k - 205) / 22 + 1

/-- Position of flat index `k` inside its sublist. -/
def posOfK (k : Nat) : Nat := if k < 205 then k else (k - 205) % 22

/-- The asserted node at flat index `k`. -/
def assertNode : Nat → Nat := fun k =>''')
A("  " + bisect(flat))
A("")
NCH = 12
step = (len(flat) + NCH - 1) // NCH
for c in range(NCH):
    a, b = c * step, min((c + 1) * step, len(flat))
    A(f"theorem assertNode_ok{c} : ((List.range {b - a}).map (fun k => k + {a})).all")
    A(f"    (fun k => decide (assertNode k")
    A(f"      = ((assertsAt (subOfK k)).getD (posOfK k) ⟨0, 0, 0⟩).assertedNode)) = true := by")
    A("  decide +kernel")
    A("")
A(f"""theorem assertNode_ok : ∀ k, k < {len(flat)} →
    assertNode k = ((assertsAt (subOfK k)).getD (posOfK k) ⟨0, 0, 0⟩).assertedNode := by
  intro k hk""")
for c in range(NCH):
    a, b = c * step, min((c + 1) * step, len(flat))
    A(f"  by_cases h{c} : k < {b}")
    A(f"  · have hb := assertNode_ok{c}")
    A(f"    simp only [List.all_eq_true, List.mem_map, List.mem_range, decide_eq_true_eq] at hb")
    A(f"    exact hb k ⟨k - {a}, by omega, by omega⟩")
A(f"  omega")
A("")
A('''/-- Sublist sizes, in closed form. -/
def sizeAt (i : Nat) : Nat := if i = 0 then 205 else if i = 302 then 13 else 22

theorem assertsAt_length : ∀ i, i < 303 → (assertsAt i).length = sizeAt i := by
  intro i hi
  match i, hi with''')
for i in range(303):
    A(f"  | {i}, _ => rfl")
A("  | (n + 303), hx => exact absurd hx (by omega)")
A("")
A('''theorem posOfK_lt : ∀ k, k < 6840 → posOfK k < sizeAt (subOfK k) := by
  intro k hk
  simp only [posOfK, subOfK, sizeAt]
  split <;> (try split) <;> (try split) <;> omega

theorem subOfK_lt : ∀ k, k < 6840 → subOfK k < 303 := by
  intro k hk
  simp only [subOfK]
  split <;> omega

variable {F : Type} [Field F]

/-- **Every assertion, by flat index.** -/
theorem zeroFlat (inputs : Nat → F)
    (hacc : ∀ r ∈ raw.toRecs, interpDag (raw.toDag (cnstw F)) inputs r.assertedNode = 0) :
    ∀ k, k < 6840 → interpDag (raw.toDag (cnstw F)) inputs (assertNode k) = 0 := by
  intro k hk
  rw [assertNode_ok k hk]
  exact zeroAt inputs hacc (subOfK k) (subOfK_lt k hk) (posOfK k)
    (by rw [assertsAt_length _ (subOfK_lt k hk)]; exact posOfK_lt k hk)

end Sha256Blk''')
open(os.path.join(OUT, "S2Flat.lean"), "w").write(NL.join(o) + NL)
print("emitted S2Flat.lean", len(o), "lines")
