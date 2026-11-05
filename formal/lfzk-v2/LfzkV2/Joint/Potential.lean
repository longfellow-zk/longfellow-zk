import LfzkV2.Joint.Backend

/-!
# Shared-query accounting

A query can fail several field checks simultaneously. Summing the existing
nonnegative residual charges is a union bound on this single sample space;
no product of field acceptance probabilities occurs. Backend challenge
charges remain separate because their typed coins are sampled separately.
-/

namespace LfzkV2.Joint.Family

open RecursivePolygero NonrecursiveFS LigeroFamily Finset
open scoped Classical

variable {k s n t : ℕ} {C : Type} [Fintype C]
variable (G : Family k s n t) (cutoff : G.Index → ℕ)
variable (decodeCoin : (i : G.Index) → C → (G.participant i).Coin)
variable (decodeQuery : C → QuerySet n t)
variable (P : (i : G.Index) → TerminalPotential (G.participant i).backend (cutoff i)
  (decodeCoin i) ((G.participant i).localQuery ∘ decodeQuery))

def NoSat (σ : G.Statement) (W : G.Oracle) (i : G.Index) : Prop :=
  ∀ g ∈ Counting.committedCandidates (G.participant i).backend (W i) (cutoff i),
    ¬ (G.participant i).backend.layer.satisfies (σ i)
      ((Counting.tupleCounts (G.participant i).backend).witness g)

noncomputable def challengeCharge (σ : G.Statement) (W : G.Oracle)
    (i : G.Index) (coin : (G.participant i).Coin) : ℚ :=
  if G.NoSat cutoff σ W i then (P i).weight (σ i) (W i) coin else 0

noncomputable def queryCharge (σ : G.Statement) (W : G.Oracle) (coins : G.Coin)
    (response : G.Response) (Q : QuerySet n t) : ℚ :=
  ∑ i, if G.NoSat cutoff σ W i ∧
      (G.participant i).backend.layer.verify (σ i) (W i) (coins i) (response i)
        ((G.participant i).localQuery Q)
    then 1-(P i).weight (σ i) (W i) (coins i) else 0

theorem challengeCharge_nonneg (σ : G.Statement) (W : G.Oracle) (i : G.Index)
    (coin : (G.participant i).Coin) :
    0 ≤ G.challengeCharge cutoff decodeCoin decodeQuery P σ W i coin := by
  unfold challengeCharge
  split_ifs
  · exact (P i).nonneg _ _ _
  · rfl

theorem queryCharge_nonneg (σ : G.Statement) (W : G.Oracle) (coins : G.Coin)
    (response : G.Response) (Q : QuerySet n t) :
    0 ≤ G.queryCharge cutoff decodeCoin decodeQuery P σ W coins response Q := by
  apply sum_nonneg
  intro i _
  split_ifs
  · exact sub_nonneg.mpr ((P i).le_one _ _ _)
  · rfl

theorem challengeCharge_sum_le (σ : G.Statement) (W : G.Oracle) (i : G.Index) :
    (∑ c, G.challengeCharge cutoff decodeCoin decodeQuery P σ W i (decodeCoin i c)) ≤
      (P i).challengeBudget := by
  unfold challengeCharge
  by_cases h : G.NoSat cutoff σ W i
  · simpa only [if_pos h] using (P i).challenge_le (σ i) (W i)
  · simpa only [if_neg h, sum_const_zero] using (P i).challengeBudget_nonneg

/-- The sum, not the maximum or a product, pays for the common query. -/
theorem queryCharge_sum_le (σ : G.Statement) (W : G.Oracle) (coins : G.Coin)
    (response : G.Response) :
    (∑ c, G.queryCharge cutoff decodeCoin decodeQuery P σ W coins response (decodeQuery c)) ≤
      ∑ i, (P i).queryBudget := by
  unfold queryCharge
  rw [sum_comm]
  apply sum_le_sum
  intro i _
  by_cases h : G.NoSat cutoff σ W i
  · simp only [h, true_and]
    convert! (P i).query_le (σ i) (W i) h (coins i) (response i) using 1
  · simp only [h, false_and, if_false, sum_const_zero]
    exact (P i).queryBudget_nonneg

theorem backend_path_ge_one (σ : G.Statement) (W : G.Oracle) (coins : G.Coin)
    (response : G.Response) (Q : QuerySet n t)
    (hbad : ∃ i, G.NoSat cutoff σ W i) (haccept : G.Verify σ W coins response Q) :
    1 ≤ (∑ i, G.challengeCharge cutoff decodeCoin decodeQuery P σ W i (coins i)) +
      G.queryCharge cutoff decodeCoin decodeQuery P σ W coins response Q := by
  obtain ⟨i, hi⟩ := hbad
  have hc := single_le_sum (fun j _ =>
    G.challengeCharge_nonneg cutoff decodeCoin decodeQuery P σ W j (coins j)) (mem_univ i)
  have hq : 1-(P i).weight (σ i) (W i) (coins i) ≤
      G.queryCharge cutoff decodeCoin decodeQuery P σ W coins response Q := by
    unfold queryCharge
    have h := single_le_sum (s := univ) (a := i)
      (f := fun j => if G.NoSat cutoff σ W j ∧
        (G.participant j).backend.layer.verify (σ j) (W j) (coins j) (response j)
          ((G.participant j).localQuery Q) then 1-(P j).weight (σ j) (W j) (coins j) else 0)
      (by intro j _; split_ifs; exact sub_nonneg.mpr ((P j).le_one _ _ _); rfl) (mem_univ i)
    simpa only [hi, haccept i, and_self, if_true] using h
  simp only [challengeCharge, hi, if_true] at hc
  dsimp only [challengeCharge]
  linarith

end LfzkV2.Joint.Family
