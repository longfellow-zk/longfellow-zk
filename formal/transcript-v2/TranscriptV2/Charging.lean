import TranscriptV2.FinalSeal

namespace TranscriptV2
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {P Link C Out : Type} [DecidableEq P] {R : ℕ}

def ChainException {fuel : ℕ} (M : Chain P Link C Out R)
    (tree : Tree P (Link × C) Out fuel) (H : P → Link × C) : Prop :=
  LinkGuess M.toLinks tree H ∨ FinalSealGuess M tree H

theorem chain_exception_ratio_le [Fintype P] [Fintype Link] [Nonempty Link] [DecidableEq Link]
    [Fintype C] [Nonempty C] [DecidableEq C] {fuel Q : ℕ}
    (M : Chain P Link C Out R) (tree : Tree P (Link × C) Out fuel)
    (hbudget : ∀ H, (seen tree H).card ≤ Q) :
    ((univ.filter (ChainException M tree)).card : ℚ) /
      (Fintype.card (Link × C) : ℚ)^Fintype.card P ≤ (Q+1 : ℚ) / Fintype.card Link := by
  have heq : univ.filter (ChainException M tree) =
      (univ.filter (LinkGuess M.toLinks tree)) ∪ (univ.filter (FinalSealGuess M tree)) := by
    ext H; simp [ChainException]
  have hc : ((univ.filter (ChainException M tree)).card : ℚ) ≤
      (univ.filter (LinkGuess M.toLinks tree)).card + (univ.filter (FinalSealGuess M tree)).card := by
    rw [heq]
    exact_mod_cast card_union_le _ _
  have hd := div_le_div_of_nonneg_right hc
    (show (0 : ℚ) ≤ (Fintype.card (Link × C) : ℚ)^Fintype.card P by positivity)
  rw [add_div] at hd
  apply (hd.trans (add_le_add (link_guess_ratio_le M.toLinks tree hbudget)
    (final_seal_guess_ratio_le M tree))).trans_eq
  ring

/-- A search with fewer than the required boundary and final queries can
produce a valid seal only through one of the counted guessing events. -/
theorem short_search_ratio_le [Fintype P] [Fintype Link] [Nonempty Link] [DecidableEq Link]
    [Fintype C] [Nonempty C] [DecidableEq C] {fuel Q : ℕ}
    (M : Chain P Link C Out R) (tree : Tree P (Link × C) Out fuel)
    (hbudget : ∀ H, (seen tree H).card ≤ Q) (hshort : Q < R+1) :
    ((univ.filter fun H => (H (M.finalSealPoint (tree.run H).1 H)).1 =
      M.finalSeal (tree.run H).1).card : ℚ) /
      (Fintype.card (Link × C) : ℚ)^Fintype.card P ≤ (Q+1 : ℚ) / Fintype.card Link := by
  have hsub : (univ.filter fun H => (H (M.finalSealPoint (tree.run H).1 H)).1 =
      M.finalSeal (tree.run H).1) ⊆ univ.filter (ChainException M tree) := by
    intro H hH
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    by_contra hn
    have hlink : ¬ LinkGuess M.toLinks tree H := fun h => hn (Or.inl h)
    have hseal : ¬ FinalSealGuess M tree H := fun h => hn (Or.inr h)
    have hrequired := M.required_fresh_queries tree H hlink hseal (mem_filter.mp hH).2
    have hlimit := hbudget H
    omega
  exact (div_le_div_of_nonneg_right (show (↑(_) : ℚ) ≤ ↑(_) by
    exact_mod_cast card_le_card hsub) (by positivity)).trans (chain_exception_ratio_le M tree hbudget)

/-- The algebraic protocol reduction supplies a bad boundary and a valid seal.
Neither field asserts that the boundary was queried; charging proves that. -/
structure Reduction (M : Chain P Link C Out R)
    (Bad : P → (P → Link × C) → (Link × C) → Prop)
    (Failure : Out → (P → Link × C) → Prop) : Prop where
  exists_bad_point : ∀ out H, Failure out H →
    ∃ n < R, Bad (M.point out H n) H (H (M.point out H n))
  final_seal_valid : ∀ out H, Failure out H → (H (M.finalSealPoint out H)).1 = M.finalSeal out

namespace Reduction

variable {M : Chain P Link C Out R}
  {Bad : P → (P → Link × C) → (Link × C) → Prop}
  {Failure : Out → (P → Link × C) → Prop}
  (D : Reduction M Bad Failure)

include D

/-- An accepting failure is charged to an actually queried bad point, unless
the search guessed a predecessor link or its unqueried final seal. -/
theorem failure_charged {fuel : ℕ} (tree : Tree P (Link × C) Out fuel)
    (H : P → Link × C) (hf : Failure (tree.run H).1 H)
    (hchain : ¬ ChainException M tree H) :
    ∃ p ∈ seen tree H, Bad p H (H p) := by
  have hlink : ¬ LinkGuess M.toLinks tree H := fun h => hchain (Or.inl h)
  have hseal : ¬ FinalSealGuess M tree H := fun h => hchain (Or.inr h)
  have hfinal : M.finalSealPoint (tree.run H).1 H ∈ seen tree H := by
    by_contra hm
    exact hseal ⟨M.finalSealPoint (tree.run H).1 H, rfl, hm, D.final_seal_valid _ _ hf⟩
  obtain ⟨n,hn,hbad⟩ := D.exists_bad_point _ _ hf
  exact ⟨M.point (tree.run H).1 H n,
    M.all_points_queried tree H _ hlink hfinal n (by omega), hbad⟩

theorem failure_ratio_le [Fintype P] [Fintype Link] [Nonempty Link] [DecidableEq Link]
    [Fintype C] [Nonempty C] [DecidableEq C] {fuel Q num den : ℕ}
    (tree : Tree P (Link × C) Out fuel) (hbudget : ∀ H, (seen tree H).card ≤ Q)
    (hoff : ∀ p H H', AgreeOff p H H' → ∀ a, Bad p H a → Bad p H' a)
    (hden : 0 < den)
    (hlocal : ∀ p H, (univ.filter (Bad p H)).card * den ≤ num * Fintype.card (Link × C)) :
    ((univ.filter fun H => Failure (tree.run H).1 H).card : ℚ) /
      (Fintype.card (Link × C) : ℚ)^Fintype.card P ≤
      (Q*num : ℚ) / den + (Q+1 : ℚ) / Fintype.card Link := by
  let A := univ.filter (ChainException M tree)
  let B := univ.filter fun H => ∃ p ∈ seen tree H, Bad p H (H p)
  have hsub : (univ.filter fun H => Failure (tree.run H).1 H) ⊆ A ∪ B := by
    intro H hH
    by_cases hchain : ChainException M tree H
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hchain⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, D.failure_charged tree H (mem_filter.mp hH).2 hchain⟩)
  have hc : ((univ.filter fun H => Failure (tree.run H).1 H).card : ℚ) ≤ (A.card : ℚ) + B.card := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le A B)
  have hd := div_le_div_of_nonneg_right hc
    (show (0 : ℚ) ≤ (Fintype.card (Link × C) : ℚ)^Fintype.card P by positivity)
  rw [add_div] at hd
  apply (hd.trans (add_le_add (chain_exception_ratio_le M tree hbudget)
    (queried_bad_ratio_le_scaled tree hbudget Bad hoff hden hlocal))).trans_eq
  ring

end Reduction
end TranscriptV2
