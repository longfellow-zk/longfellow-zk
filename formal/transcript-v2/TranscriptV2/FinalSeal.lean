import TranscriptV2.Replay

namespace TranscriptV2
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {P Link C Out : Type} [DecidableEq P] {R : ℕ}

def finalSealBad {fuel : ℕ} (M : Chain P Link C Out R) (tree : Tree P (Link × C) Out fuel)
    (p : P) (H : P → Link × C) (a : Link × C) : Prop :=
  M.finalSealPoint (tree.run H).1 H = p ∧ p ∉ seen tree H ∧ a.1 = M.finalSeal (tree.run H).1

def FinalSealGuess {fuel : ℕ} (M : Chain P Link C Out R) (tree : Tree P (Link × C) Out fuel)
    (H : P → Link × C) : Prop := ∃ p, finalSealBad M tree p H (H p)

theorem finalSealBad_off {fuel : ℕ} (M : Chain P Link C Out R)
    (tree : Tree P (Link × C) Out fuel) (p : P) (H H' : P → Link × C)
    (h : AgreeOff p H H') (a : Link × C) : finalSealBad M tree p H a → finalSealBad M tree p H' a := by
  intro ⟨hpoint,hmissing,hseal⟩
  have hrun := run_eq_of_not_mem tree p h (by simpa [seen] using hmissing)
  have hfinal := M.finalSealPoint_off (tree.run H).1 (H := H) (H' := H')
    (by simpa only [hpoint] using h)
  refine ⟨?_,?_,?_⟩
  · rw [hrun]
    exact hfinal.symm.trans hpoint
  · simpa [seen, queried, hrun] using hmissing
  · simpa [hrun] using hseal

theorem final_seal_guess_ratio_le [Fintype P] [Fintype Link] [Nonempty Link] [DecidableEq Link]
    [Fintype C] [Nonempty C] [DecidableEq C] {fuel : ℕ}
    (M : Chain P Link C Out R) (tree : Tree P (Link × C) Out fuel) :
    ((univ.filter (FinalSealGuess M tree)).card : ℚ) /
      (Fintype.card (Link × C) : ℚ)^Fintype.card P ≤ 1 / (Fintype.card Link : ℚ) := by
  -- Replay may choose the final point from other oracle answers. On each run
  -- there is still only one possible unqueried final point to charge.
  let weight := fun p H => if M.finalSealPoint (tree.run H).1 H = p ∧ p ∉ seen tree H
    then Fintype.card C else 0
  have hlocal : ∀ p H, (univ.filter (finalSealBad M tree p H)).card ≤ weight p H := by
    intro p H
    by_cases hg : M.finalSealPoint (tree.run H).1 H = p ∧ p ∉ seen tree H
    · have heq : univ.filter (finalSealBad M tree p H) =
          {M.finalSeal (tree.run H).1} ×ˢ (univ : Finset C) := by
        ext a
        simp [finalSealBad, hg.1, hg.2, Prod.ext_iff, eq_comm]
      rw [heq, card_product]
      simp [weight, hg]
    · have hempty : univ.filter (finalSealBad M tree p H) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact hg ⟨(mem_filter.mp ha).2.1, (mem_filter.mp ha).2.2.1⟩
      rw [hempty]
      simp [weight, hg]
  have htotal : ∀ H, ∑ p, weight p H ≤ Fintype.card C := by
    intro H
    calc
      (∑ p, weight p H) ≤ ∑ p, if M.finalSealPoint (tree.run H).1 H = p then Fintype.card C else 0 := by
        apply sum_le_sum
        intro p _
        dsimp [weight]
        split_ifs <;> simp_all
      _ = Fintype.card C := by simp
  have h := ratio_exists_coord_le (FinalSealGuess M tree) (finalSealBad M tree) (fun _ h => h)
    (finalSealBad_off M tree) weight (fun p H => by simpa only [finalSealBad] using hlocal p H)
    (Fintype.card C) htotal
  apply h.trans_eq
  simp only [Fintype.card_prod, Nat.cast_mul]
  have hC : (Fintype.card C : ℚ) ≠ 0 := by positivity
  field_simp

namespace Chain
variable (M : Chain P Link C Out R)

/-- Except for a guessed predecessor link, a queried child requires its parent
to have been queried already, not merely later in the search. -/
theorem parent_queried_before {fuel : ℕ} (tree : Tree P (Link × C) Out fuel)
    (H : P → Link × C) (out : Out) (hguess : ¬ LinkGuess M.toLinks tree H)
    {n : ℕ} (hn : n < R) (hchild : M.point out H (n+1) ∈ seen tree H) :
    M.point out H n ∈ seen tree H ∧
      M.point out H (n+1) ∉ before tree H (M.point out H n) := by
  have hbefore : M.point out H (n+1) ∉ before tree H (M.point out H n) := by
    intro hmem
    apply hguess
    refine ⟨M.point out H n, M.point out H (n+1), ?_, (M.point_link out H hn).symm⟩
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr hmem, M.point_parent out H hn⟩
  refine ⟨?_, hbefore⟩
  by_contra hp
  apply hbefore
  rw [before_eq_of_not_queried tree H _ (by simpa [seen] using hp)]
  exact List.mem_toFinset.mp hchild

theorem all_points_queried {fuel : ℕ} (tree : Tree P (Link × C) Out fuel)
    (H : P → Link × C) (out : Out) (hguess : ¬ LinkGuess M.toLinks tree H)
    (hfinal : M.finalSealPoint out H ∈ seen tree H) :
    ∀ k ≤ R, M.point out H k ∈ seen tree H := by
  have descend : ∀ d, d ≤ R → M.point out H (R-d) ∈ seen tree H := by
    intro d
    induction d with
    | zero => simpa [finalSealPoint] using hfinal
    | succ d ih =>
      intro hd
      have hc := ih (by omega)
      have hn : R-(d+1) < R := by omega
      have heq : R-(d+1)+1 = R-d := by omega
      exact (M.parent_queried_before tree H out hguess hn (by simpa [heq] using hc)).1
  intro k hk
  have h := descend (R-k) (by omega)
  have heq : R-(R-k) = k := by omega
  simpa only [heq] using h

/-- The final seal forces the final query; feedback then forces every earlier
boundary query. The count is on distinct points, so branch exploration adds work. -/
theorem required_fresh_queries {fuel : ℕ} (tree : Tree P (Link × C) Out fuel)
    (H : P → Link × C) (hlink : ¬ LinkGuess M.toLinks tree H) (hseal : ¬ FinalSealGuess M tree H)
    (hvalid : (H (M.finalSealPoint (tree.run H).1 H)).1 = M.finalSeal (tree.run H).1) :
    R+1 ≤ (seen tree H).card := by
  let out := (tree.run H).1
  have hfinal : M.finalSealPoint out H ∈ seen tree H := by
    by_contra hm
    exact hseal ⟨M.finalSealPoint out H, rfl, hm, hvalid⟩
  let f := fun i : Fin (R+1) => M.point out H i.val
  have hsub : univ.image f ⊆ seen tree H := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := mem_image.mp hp
    exact M.all_points_queried tree H out hlink hfinal i.val (by omega)
  have hc := card_le_card hsub
  simpa [f, card_image_of_injective _ (M.points_injective out H)] using hc

end Chain
end TranscriptV2
