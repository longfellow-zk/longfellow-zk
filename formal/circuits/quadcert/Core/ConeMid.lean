/-
# Two-level templates: a leaf block, a block of sums over leaves, then one sum

`ConeFlat` handles the `n = 2` wrapping sums, whose `z` is a flat linear form: 97 leaves and one
96-term sum. The 48 `sha256/schedule/N` cones are one level deeper and cannot use it. Measured on
the artifact, all 48 have exactly the same shape:

| | count | contents |
|---|---:|---|
| leaves | 161 | input bits |
| mid sums | 104 | 51 xor nodes `a + b - 2ab`, 52 one-term copies, one merged 173-term linear node |
| root | 1 | 103 terms: 52 linear over mids, 51 degree-2 over pairs of mids |

and **no mid references another mid**, so two levels is exactly right rather than merely enough.

The xor nodes are why: the compiler emits `σ₀`'s three-way xor as two applications of
`a + b - 2ab`, and the first application is a named wire. So `z` is *not* a form over the leaves;
it is a form over the mids, which are themselves forms over the leaves.

## Why this needs a lemma rather than `simp`

The same reason `ConeFlat` does, one level worse. Evaluating a mid node by `interpDag_sum` reads
its operands out of the accumulator with `List.getD`, and the accumulator here is 265 entries. At
3 terms per xor mid that is ~1,600 rewrite steps per mid, and the root's 103 terms add ~55,000 --
well past the ~9,300 that already left `ring` unable to close in the flat case.

`interpDagAux_midBlock` proves the block evaluation once, by induction, so no `getD` unfolds at
the instance. The operand lookup that survives into the statement is `midLeafVal`, an `if` on a
literal index and a bisection call -- both O(1) at the instance.

## The shape of `midLeafVal`

Template index `i` means a leaf when `i < L` and mid `i - L` otherwise, which is forced: the
template list is a concatenation, and `coneIs` requires operands to precede their node. So the
generator emits `mv` as a bisection from mid index to term list, and never a list -- the same
choice `coneIs` makes for its instance map, for the same reason.
-/

import quadcert.Core.ConeFlat

namespace Quadcert

variable {F : Type} [Field F]

/-- Reading a template operand: a leaf below `L`, otherwise the value of mid `i - L`. -/
def midLeafVal (consts lv : Nat → F) (L : Nat) (mv : Nat → List (Nat × Nat × Nat)) (i : Nat) : F :=
  if i < L then lv i
  else (mv (i - L)).foldl (fun acc t => acc + consts t.1 * lv t.2.1 * lv t.2.2) 0

private theorem getD_append_lt (l₁ l₂ : List F) {i : Nat} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_ge (l₁ l₂ : List F) {i : Nat} (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i 0 = l₂.getD (i - l₁.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- **The mid block evaluates to the pointwise folds.** Each mid reads only leaves, so the prefix
    it reads from is the leaf block and is never disturbed. -/
theorem interpDagAux_midBlock (consts lv : Nat → F) (L : Nat)
    (mv : Nat → List (Nat × Nat × Nat)) :
    ∀ (M : Nat), (∀ j, j < M → ∀ t ∈ mv j, t.2.1 < L ∧ t.2.2 < L) →
      interpDagAux lv ((List.range M).map (fun j =>
          (DagNode.sum ((mv j).map (fun t => ⟨consts t.1, t.2.1, t.2.2⟩)) : DagNode F)))
        ((List.range L).map lv)
        = (List.range L).map lv ++ (List.range M).map (fun j =>
            (mv j).foldl (fun acc t => acc + consts t.1 * lv t.2.1 * lv t.2.2) 0) := by
  intro M
  induction M with
  | zero => intro _; simp [interpDagAux]
  | succ k ih =>
      intro hb
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        interpDagAux_append, ih (fun j hj => hb j (by omega))]
      simp only [interpDagAux, nodeValue, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc]
      congr 1
      congr 1
      refine List.cons_eq_cons.mpr ⟨?_, rfl⟩
      rw [List.foldl_map]
      refine foldl_congr (mv k) _ _ (fun acc t ht => ?_) 0
      have h1 : t.2.1 < L := (hb k (by omega) t ht).1
      have h2 : t.2.2 < L := (hb k (by omega) t ht).2
      have hlen : ((List.range L).map lv).length = L := by simp
      rw [getD_append_lt _ _ (by rw [hlen]; exact h1), getD_append_lt _ _ (by rw [hlen]; exact h2),
        getD_range_map lv L t.2.1 h1, getD_range_map lv L t.2.2 h2]

/-- **A two-level template evaluates to the fold over its root terms.** `L` leaves, then `M` sums
    over leaves, then the root sum at index `L + M`. -/
theorem interpDag_leafMidSum (consts lv : Nat → F) (L M : Nat)
    (mv : Nat → List (Nat × Nat × Nat)) (ts : List (Nat × Nat × Nat))
    (hmid : ∀ j, j < M → ∀ t ∈ mv j, t.2.1 < L ∧ t.2.2 < L)
    (hts : ∀ t ∈ ts, t.2.1 < L + M ∧ t.2.2 < L + M) :
    interpDag (tmplDag consts
        ((List.range L).map (fun i => (TmplNode.leaf i : TmplNode))
          ++ (List.range M).map (fun j => TmplNode.sum (mv j))
          ++ [TmplNode.sum ts])) lv (L + M)
      = ts.foldl (fun acc t => acc
          + consts t.1 * midLeafVal consts lv L mv t.2.1
                       * midLeafVal consts lv L mv t.2.2) 0 := by
  have hdag : tmplDag consts
      ((List.range L).map (fun i => (TmplNode.leaf i : TmplNode))
        ++ (List.range M).map (fun j => TmplNode.sum (mv j))
        ++ [TmplNode.sum ts])
      = ((List.range L).map (fun i => (DagNode.input i : DagNode F)))
        ++ ((List.range M).map (fun j =>
            (DagNode.sum ((mv j).map (fun t => ⟨consts t.1, t.2.1, t.2.2⟩)) : DagNode F)))
        ++ [DagNode.sum (ts.map (fun t => ⟨consts t.1, t.2.1, t.2.2⟩))] := by
    simp [tmplDag, Function.comp_def]
  have hblk := interpDagAux_leafBlock consts lv L []
  simp only [List.nil_append] at hblk
  show (interpDagAux lv _ []).getD (L + M) 0 = _
  rw [hdag, interpDagAux_append, interpDagAux_append, hblk,
    interpDagAux_midBlock consts lv L mv M hmid]
  simp only [interpDagAux, nodeValue]
  -- the accumulator is now `leaves ++ mids`; the root reads operands out of it
  set acc : List F := (List.range L).map lv ++ (List.range M).map (fun j =>
    (mv j).foldl (fun a t => a + consts t.1 * lv t.2.1 * lv t.2.2) 0) with hacc
  have hlenL : ((List.range L).map lv).length = L := by simp
  have hlen : acc.length = L + M := by rw [hacc]; simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
  simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [List.foldl_map]
  refine foldl_congr ts _ _ (fun a t ht => ?_) 0
  have hread : ∀ i, i < L + M → acc.getD i 0 = midLeafVal consts lv L mv i := by
    intro i hi
    by_cases h : i < L
    · rw [hacc, getD_append_lt _ _ (by rw [hlenL]; exact h), getD_range_map lv L i h,
        midLeafVal, if_pos h]
    · have hge : ((List.range L).map lv).length ≤ i := by rw [hlenL]; omega
      rw [hacc, getD_append_ge _ _ hge, hlenL,
        getD_range_map _ M (i - L) (by omega), midLeafVal, if_neg h]
  rw [hread t.2.1 (hts t ht).1, hread t.2.2 (hts t ht).2]

/-! ### Sanity check on the index conventions

`interpDag_leafMidSum` would still typecheck, and still be provable, with `i - L` written `i` or
the root read at `L + M - 1`: the statement would just describe a different template. So this
checks it against a concrete two-level instance evaluated *directly*, by kernel reduction, with
the lemma playing no part in the left-hand side.

3 leaves, 2 mids, root at index 5:
`mid₀ = c₀·l₀·l₁ = 2·1·2 = 4`, `mid₁ = c₁·l₁·l₂ = 3·2·3 = 18`,
`root = c₀·l₀·mid₀ + c₁·mid₀·mid₁ = 8 + 216 = 224`. -/

section Sanity

private def mvT : Nat → List (Nat × Nat × Nat)
  | 0 => [(0, 0, 1)]
  | 1 => [(1, 1, 2)]
  | _ => []

private def tsT : List (Nat × Nat × Nat) := [(0, 0, 3), (1, 3, 4)]
private def cT : Nat → ℚ := fun i => (i : ℚ) + 2
private def lT : Nat → ℚ := fun i => (i : ℚ) + 1

private def tnT : List TmplNode :=
  (List.range 3).map (fun i => (TmplNode.leaf i : TmplNode))
    ++ (List.range 2).map (fun j => TmplNode.sum (mvT j))
    ++ [TmplNode.sum tsT]

private theorem tnT_eq : tnT =
    [.leaf 0, .leaf 1, .leaf 2, .sum (mvT 0), .sum (mvT 1), .sum tsT] := rfl

/-- Direct evaluation, not using the lemma. -/
private theorem direct : interpDag (tmplDag cT tnT) lT 5 = 224 := by
  rw [tnT_eq]
  norm_num [interpDag, interpDagAux, nodeValue, tmplDag, tsT, mvT, cT, lT,
    List.map_cons, List.map_nil, List.getD]

/-- The lemma, applied. -/
private theorem viaLemma : interpDag (tmplDag cT tnT) lT (3 + 2)
    = tsT.foldl (fun acc t => acc + cT t.1 * midLeafVal cT lT 3 mvT t.2.1
                                          * midLeafVal cT lT 3 mvT t.2.2) 0 :=
  interpDag_leafMidSum cT lT 3 2 mvT tsT (by decide) (by decide)

/-- and its right-hand side agrees. -/
private theorem sides_agree :
    tsT.foldl (fun acc t => acc + cT t.1 * midLeafVal cT lT 3 mvT t.2.1
                                 * midLeafVal cT lT 3 mvT t.2.2) 0 = 224 := by
  norm_num [tsT, midLeafVal, mvT, cT, lT]

example : (224 : ℚ) = 224 := by rw [← direct, viaLemma, sides_agree]

end Sanity

end Quadcert
