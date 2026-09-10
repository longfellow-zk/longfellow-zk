/-
# The n=2 wrapping sums as an edge list

Same machinery as `S2Edges`, a different template -- which is the point: `edges_transfer` is
template-agnostic, so one `decide` over the edge list plus `tmpl_wrap2` covers the whole class.

Eight instances, so no slicing is needed here; `edgesMatch_of_chunks` is what handles the classes
that do need it. Note node 238 -- the constant `1` -- is shared by all eight maps, so CSE really
does collapse it.
-/

import quadcert.Core.ConeEdges
import quadcert.Bridge.Sha256.S2TmplWrap
set_option maxRecDepth 4000000
set_option maxHeartbeats 400000
namespace Sha256Blk
open Quadcert Quadcert.Gen.Sha256Blk

def zOfW : Nat → Nat := fun e => (if e < 4 then if e < 2 then if e < 1 then 19753 else 6705 else if e < 3 then 26618 else 31257 else if e < 6 then if e < 5 then 30865 else 13678 else if e < 7 then 21546 else 24339)
def f0OfW : Nat → Nat := fun e => (if e < 4 then if e < 2 then if e < 1 then 19754 else 6706 else if e < 3 then 26619 else 31258 else if e < 6 then if e < 5 then 30866 else 13679 else if e < 7 then 21547 else 24340)
def f1OfW : Nat → Nat := fun e => (if e < 4 then if e < 2 then if e < 1 then 19755 else 6707 else if e < 3 then 26620 else 31259 else if e < 6 then if e < 5 then 30867 else 13680 else if e < 7 then 21548 else 24341)
def rootOfW : Nat → Nat := fun e => (if e < 4 then if e < 2 then if e < 1 then 19756 else 6708 else if e < 3 then 26621 else 31260 else if e < 6 then if e < 5 then 30868 else 13681 else if e < 7 then 21549 else 24342)

/-- `tnWrap2` order: 0 the constant-1 input, 1 the hole for `z`, 2 the `1` node, 3 `z-0t`,
    4 `z-1t`, 5 the asserted product. -/
def mapOfW : Nat → Nat → Nat := fun e i =>
  if i < 1 then 0 else if i < 2 then zOfW e else if i < 3 then 238
  else if i < 4 then f0OfW e else if i < 5 then f1OfW e else rootOfW e

theorem wrapEdges : edgesMatch nodeFn tnWrap2 mapOfW 8 = true := by decide +kernel

theorem mapOfW_lt : ∀ e, e < 8 → ∀ i, i < tnWrap2.length → mapOfW e i < raw.nodes.length := by
  have hb : (List.range 8).all
      (fun e => (List.range 6).all (fun i => decide (mapOfW e i < 37139))) = true := by
    decide +kernel
  intro e he i hi
  rw [nodes_len]
  have h6 : tnWrap2.length = 6 := rfl
  rw [h6] at hi
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  exact hb e he i hi

variable {F : Type} [Field F]

/-- **All eight n=2 wrapping sums, from one edge list.** -/
theorem allWrap2 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hz : ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0) :
    ∀ e, e < 8 → SHA256F.wrapPoly 2 ((2 ^ 32 : Nat) : F)
      (interpDag (raw.toDag (cnstw F)) inputs (zOfW e)) = 0 := by
  intro e he
  have htr := edges_transfer raw (cnstw F) inputs nodeFn nodefn_ok tnWrap2 mapOfW 8
    wrapEdges mapOfW_lt e he
  have hone : (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOfW e h)) 0 = 1 := by
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    have hdl : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdl, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hroot : interpDag (tmplDag (cnstw F) tnWrap2)
      (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOfW e h)) 5 = 0 := by
    rw [← htr 5 (by decide)]
    show interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0
    exact hz e he
  have hw := tmpl_wrap2 (cnstw F)
    (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOfW e h)) cnstw_0 cnstw_65 hone hroot
  show SHA256F.wrapPoly 2 ((2 ^ 32 : Nat) : F)
    (interpDag (raw.toDag (cnstw F)) inputs (zOfW e)) = 0
  exact hw

end Sha256Blk
