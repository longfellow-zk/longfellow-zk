import TranscriptV2.SharedCharging
import TranscriptV2.SharedFailure

/-! Accepted-path charging with both single-answer events and grouped
parent/child events. Link feedback proves the order needed by the grouped
term; the reduction does not assume an ordered adversarial query trace. -/
namespace TranscriptV2
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {P Link C Out Parent Response : Type} [DecidableEq P] {R : ℕ}

private theorem first_left_of_not_before {A : Type} {fuel : ℕ}
    (tree : Tree P A Out fuel) (H : P → A) (p c : P)
    (hc : c ∈ seen tree H) (hbefore : c ∉ before tree H p) :
    firstOfTwo tree H p c = .left := by
  induction tree with
  | done _ => simp [seen, queried] at hc
  | query q next ih =>
      by_cases hp : q = p
      · simp only [firstOfTwo, if_pos hp]
      · by_cases hq : q = c
        · exact (hbefore (by
            simp only [before, if_neg hp, List.mem_cons]
            exact Or.inl hq.symm)).elim
        · have ht : c ∈ seen (next (H q)) H := by
            simpa [seen, queried_query, Ne.symm hq] using hc
          have hb : c ∉ before (next (H q)) H p := by
            intro h
            exact hbefore (by simp only [before, if_neg hp]; exact List.mem_cons_of_mem q h)
          simpa only [firstOfTwo, if_neg hp, if_neg hq] using ih (H q) ht hb

/-- The whole-answer construction supplies the same accepted-path interface
used by other transcript realizations. The final seal forces membership;
parent feedback then supplies the order of adjacent queries. -/
theorem Chain.accepted_path_queries (model : Chain P Link C Out R)
    {fuel : ℕ} (tree : Tree P (Link × C) Out fuel) (H : P → Link × C)
    (good : ¬ChainException model tree H)
    (sealValid : (H (model.finalSealPoint (tree.run H).1 H)).1 = model.finalSeal (tree.run H).1) :
    (∀ i ≤ R, model.point (tree.run H).1 H i ∈ seen tree H) ∧
      (∀ i < R, firstOfTwo tree H (model.point (tree.run H).1 H i)
        (model.point (tree.run H).1 H (i+1)) = .left) := by
  have links : ¬LinkGuess model.toLinks tree H := fun h => good (Or.inl h)
  have finalSeal : ¬FinalSealGuess model tree H := fun h => good (Or.inr h)
  have terminal : model.finalSealPoint (tree.run H).1 H ∈ seen tree H := by
    by_contra missing
    exact finalSeal ⟨model.finalSealPoint (tree.run H).1 H,rfl,missing,sealValid⟩
  have queried := model.all_points_queried tree H _ links terminal
  refine ⟨queried,?_⟩
  intro i before
  have child := queried (i+1) (by omega)
  exact first_left_of_not_before tree H _ _ child
    (model.parent_queried_before tree H _ links before child).2

/-- The algebraic reduction names a failing boundary or an adjacent pair.
The final seal is checked in both cases. Query membership and query order
are conclusions of the chain argument, not premises of this certificate. -/
structure SharedReduction (M : Chain P Link C Out R)
    (parent : Parent → P) (child : Parent → Response → P)
    (single : P → (P → Link × C) → (Link × C) → ℚ)
    (pair : Parent → Response → (P → Link × C) → (Link × C) → (Link × C) → ℚ)
    (Failure : Out → (P → Link × C) → Prop) : Prop where
  cover : ∀ out H, Failure out H →
    (∃ n < R, 1 ≤ single (M.point out H n) H (H (M.point out H n))) ∨
    (∃ n < R, ∃ p r, parent p = M.point out H n ∧ child p r = M.point out H (n+1) ∧
      1 ≤ pair p r H (H (parent p)) (H (child p r)))
  final_seal_valid : ∀ out H, Failure out H → (H (M.finalSealPoint out H)).1 = M.finalSeal out

namespace SharedReduction
variable [Fintype Parent] [Fintype Response]
variable {M : Chain P Link C Out R} {parent : Parent → P} {child : Parent → Response → P}
variable {single : P → (P → Link × C) → (Link × C) → ℚ}
variable {pair : Parent → Response → (P → Link × C) → (Link × C) → (Link × C) → ℚ}
variable {Failure : Out → (P → Link × C) → Prop}
variable (D : SharedReduction M parent child single pair Failure)

def charges {fuel : ℕ} (tree : Tree P (Link × C) Out fuel) (H : P → Link × C) : ℚ :=
  (∑ z ∈ seen tree H, single z H (H z)) +
    ∑ p, ∑ r, if firstOfTwo tree H (parent p) (child p r) = .left then
      pair p r H (H (parent p)) (H (child p r)) else 0

theorem charges_nonneg {fuel : ℕ} (tree : Tree P (Link × C) Out fuel) (H : P → Link × C)
    (hs : ∀ z H a, 0 ≤ single z H a) (hp : ∀ p r H a b, 0 ≤ pair p r H a b) :
    0 ≤ charges (parent := parent) (child := child) (single := single) (pair := pair) tree H := by
  apply add_nonneg
  · exact sum_nonneg (fun z _ => hs z H (H z))
  · apply sum_nonneg
    intro p _
    apply sum_nonneg
    intro r _
    split_ifs
    · exact hp p r H _ _
    · exact le_rfl

/-- The positive-charge argument needs only query membership and order on
an accepted path. It does not depend on how the transcript encodes parents. -/
theorem charges_of_cover {fuel : ℕ} (tree : Tree P (Link × C) Out fuel) (H : P → Link × C)
    (point : ℕ → P)
    (hqueries : ∀ n, n ≤ R → point n ∈ seen tree H)
    (horder : ∀ n, n < R → firstOfTwo tree H (point n) (point (n+1)) = .left)
    (hs : ∀ z H a, 0 ≤ single z H a) (hp : ∀ p r H a b, 0 ≤ pair p r H a b)
    (hcover : (∃ n < R, 1 ≤ single (point n) H (H (point n))) ∨
      (∃ n < R, ∃ p r, parent p = point n ∧ child p r = point (n+1) ∧
        1 ≤ pair p r H (H (parent p)) (H (child p r)))) :
    1 ≤ charges (parent := parent) (child := child) (single := single) (pair := pair) tree H := by
  let pairs := fun p => ∑ r, if firstOfTwo tree H (parent p) (child p r) = .left then
    pair p r H (H (parent p)) (H (child p r)) else 0
  have hpair p r : 0 ≤ (if firstOfTwo tree H (parent p) (child p r) = .left then
      pair p r H (H (parent p)) (H (child p r)) else 0) := by
    split_ifs
    · exact hp p r H _ _
    · exact le_rfl
  have hpairs p : 0 ≤ pairs p := sum_nonneg (fun r _ => hpair p r)
  rcases hcover with ⟨i,hi,hbad⟩ | ⟨i,hi,p,r,hpPoint,hcPoint,hbad⟩
  · have hsum := single_le_sum (fun z _ => hs z H (H z)) (hqueries i (by omega))
    exact (hbad.trans hsum).trans (le_add_of_nonneg_right (sum_nonneg (fun p _ => hpairs p)))
  · have hfirst : firstOfTwo tree H (parent p) (child p r) = .left := by
      rw [hpPoint, hcPoint]
      exact horder i hi
    have hinner := single_le_sum (fun r _ => hpair p r) (mem_univ r)
    rw [if_pos hfirst] at hinner
    have houter := single_le_sum (fun p _ => hpairs p) (mem_univ p)
    exact ((hbad.trans hinner).trans houter).trans
      (le_add_of_nonneg_left (sum_nonneg (fun z _ => hs z H (H z))))

include D in
theorem failure_charged {fuel : ℕ} (tree : Tree P (Link × C) Out fuel) (H : P → Link × C)
    (hs : ∀ z H a, 0 ≤ single z H a) (hp : ∀ p r H a b, 0 ≤ pair p r H a b)
    (hf : Failure (tree.run H).1 H) (hchain : ¬ ChainException M tree H) :
    1 ≤ charges (parent := parent) (child := child) (single := single) (pair := pair) tree H := by
  obtain ⟨hall,horder⟩ := M.accepted_path_queries tree H hchain (D.final_seal_valid _ _ hf)
  exact charges_of_cover tree H (M.point (tree.run H).1 H) hall horder hs hp (D.cover _ _ hf)

include D in
/-- One shared query budget and one chain exception for the full reduction.
The per-point bound includes the high-response cost at each parent, so it
must be checked after combining all charges belonging to that query role. -/
theorem failure_ratio_le [Fintype P] [Fintype Link] [Nonempty Link] [DecidableEq Link]
    [Fintype C] [Nonempty C] [DecidableEq C] {fuel Q : ℕ}
    (tree : Tree P (Link × C) Out fuel) (hqueries : ∀ H, (seen tree H).card ≤ Q)
    (hne : ∀ p r, parent p ≠ child p r)
    (hsingleOff : ∀ p H H', AgreeOff p H H' → ∀ a, single p H a = single p H' a)
    (hsingleNonneg : ∀ p H a, 0 ≤ single p H a)
    (hpairOff : ∀ p r H H',
      (∀ z, z ≠ parent p → z ≠ child p r → H z = H' z) →
      ∀ a b, pair p r H a b = pair p r H' a b)
    (hpairNonneg : ∀ p r H a b, 0 ≤ pair p r H a b)
    (singleBudget : P → ℚ) (pairBudget : Parent → ℚ) (epsilon : ℚ)
    (he : 0 ≤ epsilon)
    (hsingle : ∀ p H, ∑ a, single p H a ≤ Fintype.card (Link × C) * singleBudget p)
    (hpair : ∀ p H, ∑ r, ∑ a, ∑ b, pair p r H a b ≤
      (Fintype.card (Link × C) : ℚ)^2 * pairBudget p)
    (hpoint : ∀ z, singleBudget z +
      (∑ p, if parent p = z then pairBudget p else 0) ≤ epsilon) :
    ((univ.filter fun H => Failure (tree.run H).1 H).card : ℚ) /
      (Fintype.card (Link × C) : ℚ)^Fintype.card P ≤
      (Q : ℚ)*epsilon + (Q+1 : ℚ)/Fintype.card Link := by
  let cost := charges (parent := parent) (child := child) (single := single) (pair := pair) tree
  have averaged := SharedFailure.failure_ratio_le
    (fun H => Failure (tree.run H).1 H) (ChainException M tree) cost
    (chargeBound := (Q : ℚ)*epsilon) (exceptionBound := (Q+1 : ℚ)/Fintype.card Link)
    (fun H => charges_nonneg tree H hsingleNonneg hpairNonneg)
    (fun H hf hc => D.failure_charged tree H hsingleNonneg hpairNonneg hf hc)
    (by
      simpa only [cost, charges, Fintype.card_fun, Nat.cast_pow] using
        (shared_queried_sum_le tree hqueries parent child hne single hsingleOff pair hpairOff
          hpairNonneg singleBudget pairBudget epsilon he hsingle hpair hpoint))
    (by
      simpa only [Fintype.card_fun, Nat.cast_pow] using chain_exception_ratio_le M tree hqueries)
  simpa only [Fintype.card_fun, Nat.cast_pow] using averaged

end SharedReduction
end TranscriptV2
