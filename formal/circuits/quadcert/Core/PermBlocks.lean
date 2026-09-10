/-
# Layer permutations from a tiling of the group range

`sum_local` needs, per layer, that the grouped terms flatten to a permutation of the layer's
canonical term list. Proving that by sorting both sides does not survive SHA-256: layer 4 is
26,089 terms and `perm_of_msort_eq` costs 175 s / 18.2 GB and aborts at the 16 GB cap; layer 5 is
89,048. A sort does not split along ranges, so chunking the sort is not available.

What does split is the *group range*. Tile `[0, nw)` into blocks; the grouped side restricts to a
block by cutting the range, and the term side by filtering on the same bound. Each block is then
an independent small sort. Layer 5's worst block costs 34 s / 7.4 GB.

Two things make this work in practice, both learned the hard way:

* The filter must be distributed over the layer's expansion-chunk appends
  (`unfold allTerms_L; simp only [List.filter_append]`) before any `decide`. The kernel will not
  materialise 89,048 terms as one list -- even `allTerms_5.length = 89048` blows the cap --
  whereas `Sha256BlkFilt5` filters that same list in 8 s / 1.7 GB by distributing first.
* Blocks are sized by term count, not group count. Density is very uneven: layer 4's seven
  1000-group windows hold 1714, 4060, 2378, 1000, 4808, 7496 and 4633 terms, and cost tracks
  terms.

**This is a leaf module on purpose.** The natural home would be `RawGroup.lean`, but 602 modules
depend on that one -- `Check` imports it, so every artifact module does too. Only the `Perm{L}`
modules need what is here, and they are the ones iterated on.
-/

import quadcert.Core.RawGroup

namespace Quadcert

variable {α : Type}

/-- Membership of one `(lo, len)` block of key values, as a `Bool` so `List.filter` takes it. -/
def inBlk (key : α → Nat) (lo len : Nat) (t : α) : Bool :=
  decide (lo ≤ key t) && decide (key t < lo + len)

theorem tiles_le : ∀ (bs : List (Nat × Nat)) (lo n : Nat), tiles bs lo n = true → lo ≤ n := by
  intro bs
  induction bs with
  | nil => intro lo n h; simp only [tiles, beq_iff_eq] at h; omega
  | cons c rest ih =>
      obtain ⟨a, len⟩ := c
      intro lo n h
      simp only [tiles, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hrest⟩ := h
      have := ih (a + len) n hrest
      omega

theorem tiles_ge : ∀ (bs : List (Nat × Nat)) (lo n : Nat), tiles bs lo n = true →
    ∀ b ∈ bs, lo ≤ b.1 := by
  intro bs
  induction bs with
  | nil => intro lo n _ b hb; simp at hb
  | cons c rest ih =>
      obtain ⟨a, len⟩ := c
      intro lo n h b hb
      simp only [tiles, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hrest⟩ := h
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact Nat.le_refl _
      · have := ih (a + len) n hrest b hb'
        omega

/-- **The composition.** A contiguous tiling of the key range, plus one permutation per block,
    gives the whole-layer permutation -- with no whole-layer sort anywhere. Mirrors
    `okInv_of_chunks`, which does the same for the inverse check. -/
theorem perm_blocks (key : α → Nat) (f : Nat → List α) :
    ∀ (bs : List (Nat × Nat)) (l : List α) (lo n : Nat),
      tiles bs lo n = true →
      (∀ t ∈ l, lo ≤ key t ∧ key t < n) →
      (∀ b ∈ bs, (l.filter (inBlk key b.1 b.2)).Perm ((List.range' b.1 b.2).flatMap f)) →
      l.Perm ((List.range' lo (n - lo)).flatMap f) := by
  intro bs
  induction bs with
  | nil =>
      intro l lo n htiles hbound _
      simp only [tiles, beq_iff_eq] at htiles
      subst htiles
      have hl : l = [] := by
        cases l with
        | nil => rfl
        | cons x t => exact absurd (hbound x (List.mem_cons_self ..)) (by omega)
      subst hl
      simp
  | cons c rest ih =>
      obtain ⟨a, len⟩ := c
      intro l lo n htiles hbound hblk
      simp only [tiles, Bool.and_eq_true, beq_iff_eq] at htiles
      obtain ⟨rfl, hrest⟩ := htiles
      have han : a + len ≤ n := tiles_le rest (a + len) n hrest
      -- the head block, and everything else
      have hhead : (l.filter (inBlk key a len)).Perm ((List.range' a len).flatMap f) :=
        hblk (a, len) (List.mem_cons_self ..)
      -- outside the head block, and above `a`, means at or above `a + len`
      have hout : ∀ t ∈ l.filter (fun x => !(inBlk key a len) x), a + len ≤ key t ∧ key t < n := by
        intro t ht
        rw [List.mem_filter] at ht
        obtain ⟨htl, hnp⟩ := ht
        have hb := hbound t htl
        simp only [inBlk, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
          Nat.not_le, Nat.not_lt] at hnp
        omega
      -- a later block never overlaps the head block, so its filter ignores the `!p` guard
      have hlater : ∀ b ∈ rest,
          (l.filter (fun x => !(inBlk key a len) x)).filter (inBlk key b.1 b.2)
            = l.filter (inBlk key b.1 b.2) := by
        intro b hb
        have hbge : a + len ≤ b.1 := tiles_ge rest (a + len) n hrest b hb
        rw [List.filter_filter]
        congr 1
        funext t
        by_cases hin : inBlk key b.1 b.2 t = true
        · have : ¬ (key t < a + len) := by
            simp only [inBlk, Bool.and_eq_true, decide_eq_true_eq] at hin
            omega
          simp [hin, inBlk, this]
        · simp only [Bool.not_eq_true] at hin
          simp [hin]
      have ihres := ih (l.filter (fun x => !(inBlk key a len) x)) (a + len) n hrest hout
        (fun b hb => by rw [hlater b hb]; exact hblk b (List.mem_cons_of_mem _ hb))
      -- glue: split the target range the way `okInvRange_split` does -- forward `range'_append`
      -- will not match, since the goal carries `a + len` where the pattern wants `a + 1 * len`
      have hr : List.range' a (n - a)
          = List.range' a len ++ List.range' (a + len) (n - (a + len)) := by
        have hn : n - a = len + (n - (a + len)) := by omega
        rw [hn, ← List.range'_append, Nat.one_mul]
      rw [hr, List.flatMap_append]
      exact (List.filter_append_perm (inBlk key a len) l).symm.trans (hhead.append ihres)

/-- The form the generated modules use: `List.range`, and a tiling of `[0, nw)`. -/
theorem perm_of_blocks (key : α → Nat) (f : Nat → List α) (l : List α) (nw : Nat)
    (bs : List (Nat × Nat)) (htiles : tiles bs 0 nw = true)
    (hlt : ∀ t ∈ l, key t < nw)
    (hblk : ∀ b ∈ bs, (l.filter (inBlk key b.1 b.2)).Perm ((List.range' b.1 b.2).flatMap f)) :
    l.Perm ((List.range nw).flatMap f) := by
  rw [List.range_eq_range']
  have h := perm_blocks key f bs l 0 nw htiles (fun t ht => ⟨Nat.zero_le _, hlt t ht⟩) hblk
  simpa using h

end Quadcert
