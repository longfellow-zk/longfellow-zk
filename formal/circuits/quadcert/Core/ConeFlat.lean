/-
# Flat templates: a leaf block followed by one sum

`z`-cones have a special shape -- 97 leaves and a single 96-term sum node -- and reducing them
with `simp` is quadratic: each of the 96 operand lookups walks a 97-element accumulator through
`List.getD_cons_succ`, which is ~9,300 rewrite steps and leaves the result too tangled for `ring`
to close.

This module proves the evaluation **once**, by induction, so no `getD` ever unfolds at the
instance. It is the same fix `nodeFn`/`wireFn` already use for node lookups, applied to the
template's own accumulator.
-/

import quadcert.Core.ConeTmpl

namespace Quadcert

variable {F : Type} [Field F]

/-- A block of `m` leaves evaluates to the leaf valuation on `[0, m)`. -/
theorem interpDagAux_leafBlock (consts lv : Nat → F) :
    ∀ (m : Nat) (acc : List F),
      interpDagAux lv ((List.range m).map (fun i => (DagNode.input i : DagNode F))) acc
        = acc ++ (List.range m).map lv := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => intro acc; simp [interpDagAux]
    | succ k =>
        intro acc
        rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
        rw [interpDagAux_append, ih k (Nat.lt_succ_self k) acc]
        simp [interpDagAux, nodeValue, List.range_succ]

/-- Reading the leaf block back. -/
theorem getD_range_map (lv : Nat → F) (m i : Nat) (hi : i < m) :
    ((List.range m).map lv).getD i 0 = lv i := by
  have hlen : i < ((List.range m).map lv).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ hlen]
  simp

/-- **A flat template evaluates to the fold over its terms**, with no `getD` unfolding at the
    instance. `m` leaves then one sum node; the sum sits at index `m`. -/
theorem interpDag_leafSum (consts lv : Nat → F) (m : Nat) (ts : List (Nat × Nat × Nat))
    (hlt : ∀ t ∈ ts, t.2.1 < m ∧ t.2.2 < m) :
    interpDag (tmplDag consts
        ((List.range m).map (fun i => (TmplNode.leaf i : TmplNode)) ++ [TmplNode.sum ts])) lv m
      = ts.foldl (fun acc t => acc + consts t.1 * lv t.2.1 * lv t.2.2) 0 := by
  have hdag : tmplDag consts
      ((List.range m).map (fun i => (TmplNode.leaf i : TmplNode)) ++ [TmplNode.sum ts])
      = ((List.range m).map (fun i => (DagNode.input i : DagNode F)))
        ++ [DagNode.sum (ts.map (fun t => ⟨consts t.1, t.2.1, t.2.2⟩))] := by
    simp [tmplDag]
  have hblk := interpDagAux_leafBlock consts lv m []
  simp only [List.nil_append] at hblk
  show (interpDagAux lv _ []).getD m 0 = _
  rw [hdag, interpDagAux_append, hblk]
  simp only [interpDagAux, nodeValue, List.nil_append]
  have hlen : ((List.range m).map lv).length = m := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
  simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [List.foldl_map]
  exact foldl_congr ts _ _ (fun acc t ht => by
    rw [getD_range_map lv m t.2.1 (hlt t ht).1, getD_range_map lv m t.2.2 (hlt t ht).2]) 0

end Quadcert
