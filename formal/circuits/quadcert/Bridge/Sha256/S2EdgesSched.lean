/-
# The 48 `sha256/schedule/N` wrapping products, as one edge list

The `n = 4` counterpart of `S2EdgesWrap`. Same machinery, same single `decide`: `edges_transfer`
is template-agnostic, so one edge list over `tnWrap4` covers the whole class.

The instance map is unusually simple because the product tree sits directly above `z` in the
node numbering — measured on the artifact, **all 48** cones have their tree at exactly
`z+1 … z+7` with the root at `z+7`, and share the constant nodes `0`, `238` (`1`) and `239`
(`1 * 1`). So the only per-instance datum is `z` itself.
-/

import quadcert.Core.ConeEdges
import quadcert.Bridge.Sha256.S2TmplWrap

set_option maxRecDepth 4000000
set_option maxHeartbeats 1000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

/-- `z` of each schedule assertion, in schedule order `t = 16 … 63`. -/
def zOfS : Nat → Nat := fun e => (if e < 24 then if e < 12 then if e < 6 then if e < 3 then if e < 1 then 35132 else if e < 2 then 17701 else 34468 else if e < 4 then 35985 else if e < 5 then 2201 else 36733 else if e < 9 then if e < 7 then 33009 else if e < 8 then 18245 else 33130 else if e < 10 then 31512 else if e < 11 then 25895 else 34858 else if e < 18 then if e < 15 then if e < 13 then 21993 else if e < 14 then 23590 else 28768 else if e < 16 then 6609 else if e < 17 then 1422 else 29863 else if e < 21 then if e < 19 then 23211 else if e < 20 then 22486 else 26197 else if e < 22 then 24760 else if e < 23 then 27043 else 31725 else if e < 36 then if e < 30 then if e < 27 then if e < 25 then 32125 else if e < 26 then 19101 else 29708 else if e < 28 then 23981 else if e < 29 then 12295 else 32329 else if e < 33 then if e < 31 then 21869 else if e < 32 then 19227 else 18925 else if e < 34 then 24968 else if e < 35 then 17902 else 3004 else if e < 42 then if e < 39 then if e < 37 then 16982 else if e < 38 then 20083 else 30115 else if e < 40 then 25522 else if e < 41 then 11969 else 6257 else if e < 45 then if e < 43 then 25408 else if e < 44 then 35381 else 10942 else if e < 46 then 3472 else if e < 47 then 8463 else 35708)

/-- The asserted product node. -/
def rootOfS : Nat → Nat := fun e => zOfS e + 7

/-- `tnWrap4` index to circuit node: three shared constants, then the product tree. -/
def mapOfS : Nat → Nat → Nat := fun e i =>
  if i < 3 then (if i < 1 then 0 else if i < 2 then 238 else 239) else zOfS e + (i - 3)

theorem schedEdges : edgesMatch nodeFn tnWrap4 mapOfS 48 = true := by decide +kernel

theorem mapOfS_lt : ∀ e, e < 48 → ∀ i, i < tnWrap4.length → mapOfS e i < raw.nodes.length := by
  have hb : (List.range 48).all
      (fun e => (List.range 11).all (fun i => decide (mapOfS e i < 37139))) = true := by
    decide +kernel
  intro e he i hi
  rw [nodes_len]
  have h11 : tnWrap4.length = 11 := rfl
  rw [h11] at hi
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  exact hb e he i hi

variable {F : Type} [Field F]

/-- **All 48 n=4 wrapping sums, from one edge list.** -/
theorem allWrap4 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hz : ∀ e, e < 48 → interpDag (raw.toDag (cnstw F)) inputs (rootOfS e) = 0) :
    ∀ e, e < 48 → SHA256F.wrapPoly 4 ((2 ^ 32 : Nat) : F)
      (interpDag (raw.toDag (cnstw F)) inputs (zOfS e)) = 0 := by
  intro e he
  have htr := edges_transfer raw (cnstw F) inputs nodeFn nodefn_ok tnWrap4 mapOfS 48
    schedEdges mapOfS_lt e he
  have hone : (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOfS e h)) 0 = 1 := by
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    have hdl : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdl, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hroot : interpDag (tmplDag (cnstw F) tnWrap4)
      (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOfS e h)) 10 = 0 := by
    rw [← htr 10 (by decide)]
    show interpDag (raw.toDag (cnstw F)) inputs (rootOfS e) = 0
    exact hz e he
  have hw := tmpl_wrap4 (cnstw F)
    (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOfS e h)) cnstw_0 cnstw_65 cnstw_66
    cnstw_67 hone hroot
  show SHA256F.wrapPoly 4 ((2 ^ 32 : Nat) : F)
    (interpDag (raw.toDag (cnstw F)) inputs (zOfS e)) = 0
  exact hw

end Sha256Blk
