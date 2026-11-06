import Bcs.TotalOracle
import Mathlib.Tactic

/-! Adaptive query prefixes, stopped before the first occurrence of a point.
No fresh-answer tape or assumed query ordering is used here. -/
namespace TranscriptV2
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {P A Out : Type} [DecidableEq P]

def before : {fuel : ℕ} → Tree P A Out fuel → (P → A) → P → List P
  | _, .done _, _, _ => []
  | _, .query q next, H, p =>
      if q = p then [] else q :: before (next (H q)) H p

theorem before_congr {fuel : ℕ} (tree : Tree P A Out fuel) (p : P)
    {H H' : P → A} (h : AgreeOff p H H') : before tree H p = before tree H' p := by
  induction tree with
  | done _ => rfl
  | query q next ih =>
    by_cases hq : q = p
    · simp [before, hq]
    · simp only [before, if_neg hq]
      have heq := h q hq
      rw [← heq]
      exact congrArg (List.cons q) (ih (H q))

theorem before_subset {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) (p : P) :
    before tree H p ⊆ queried tree H := by
  induction tree with
  | done _ => simp [before]
  | query q next ih =>
    by_cases hq : q = p
    · simp [before, hq]
    · simp only [before, if_neg hq, queried_query]
      exact List.cons_subset_cons q (ih (H q))

theorem before_eq_of_not_queried {fuel : ℕ} (tree : Tree P A Out fuel)
    (H : P → A) (p : P) (hp : p ∉ queried tree H) :
    before tree H p = queried tree H := by
  induction tree with
  | done _ => rfl
  | query q next ih =>
    have hq : q ≠ p := by intro h; apply hp; simp [queried_query, h]
    have ht : p ∉ queried (next (H q)) H := by
      intro h; exact hp (by rw [queried_query]; exact List.mem_cons_of_mem q h)
    simp only [before, if_neg hq, queried_query, ih (H q) ht]

def seen {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) : Finset P :=
  (queried tree H).toFinset

theorem seen_card_le {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) :
    (seen tree H).card ≤ fuel :=
  (List.toFinset_card_le _).trans (queried_length_le tree H)

/-- Charge bad answers only at points the adversary queried. Prefix-dependent
data may read the whole oracle off the charged point. -/
theorem queried_bad_ratio_le [Fintype P] [Fintype A] [Nonempty A] [DecidableEq A]
    {fuel Q β : ℕ} (tree : Tree P A Out fuel)
    (hbudget : ∀ H, (seen tree H).card ≤ Q)
    (Bad : P → (P → A) → A → Prop)
    (hoff : ∀ p H H', AgreeOff p H H' → ∀ a, Bad p H a → Bad p H' a)
    (hlocal : ∀ p H, (univ.filter (Bad p H)).card ≤ β) :
    ((univ.filter fun H : P → A => ∃ p ∈ seen tree H, Bad p H (H p)).card : ℚ) /
      (Fintype.card A : ℚ)^Fintype.card P ≤ (Q*β : ℚ) / Fintype.card A := by
  let Hit := fun p H a => p ∈ seen tree H ∧ Bad p H a
  let weight := fun p H => if p ∈ seen tree H then β else 0
  have hOff : ∀ p H H', AgreeOff p H H' → ∀ a, Hit p H a → Hit p H' a := by
    intro p H H' h a ha
    refine ⟨?_, hoff p H H' h a ha.2⟩
    exact List.mem_toFinset.mpr ((mem_queried_iff tree p h).mp (List.mem_toFinset.mp ha.1))
  have hLocal : ∀ p H, (univ.filter (Hit p H)).card ≤ weight p H := by
    intro p H
    by_cases hp : p ∈ seen tree H
    · simpa [Hit, weight, hp] using hlocal p H
    · simp [Hit, weight, hp]
  have hTotal : ∀ H, ∑ p, weight p H ≤ Q*β := by
    intro H
    have heq : (∑ p, weight p H) = (seen tree H).card * β := by
      simp [weight]
    rw [heq]
    exact Nat.mul_le_mul_right β (hbudget H)
  simpa only [Hit, Nat.cast_mul] using ratio_exists_coord_le _ Hit (fun _ h => h) hOff weight
    (fun p H => by simpa only [Hit] using hLocal p H) (Q*β) hTotal

/-- A scaled local count avoids divisibility assumptions on the answer space.
In particular, an empty fingerprint vector needs no special pivot coordinate. -/
theorem queried_bad_ratio_le_scaled [Fintype P] [Fintype A] [Nonempty A] [DecidableEq A]
    {fuel Q num den : ℕ} (tree : Tree P A Out fuel)
    (hbudget : ∀ H, (seen tree H).card ≤ Q)
    (Bad : P → (P → A) → A → Prop)
    (hoff : ∀ p H H', AgreeOff p H H' → ∀ a, Bad p H a → Bad p H' a)
    (hden : 0 < den)
    (hlocal : ∀ p H, (univ.filter (Bad p H)).card * den ≤ num * Fintype.card A) :
    ((univ.filter fun H : P → A => ∃ p ∈ seen tree H, Bad p H (H p)).card : ℚ) /
      (Fintype.card A : ℚ)^Fintype.card P ≤ (Q*num : ℚ) / den := by
  let β := num * Fintype.card A / den
  have hβ : ∀ p H, (univ.filter (Bad p H)).card ≤ β :=
    fun p H => (Nat.le_div_iff_mul_le hden).mpr (hlocal p H)
  have hround : (β : ℚ) * den ≤ (num : ℚ) * Fintype.card A := by
    exact_mod_cast Nat.div_mul_le_self (num * Fintype.card A) den
  apply (queried_bad_ratio_le tree hbudget Bad hoff hβ).trans
  apply (div_le_div_iff₀ (by positivity) (by exact_mod_cast hden)).mpr
  calc
    (Q : ℚ)*β*den = Q*((β : ℚ)*den) := by ring
    _ ≤ Q*((num : ℚ)*Fintype.card A) := mul_le_mul_of_nonneg_left hround (by positivity)
    _ = (Q*num : ℚ)*Fintype.card A := by ring

end TranscriptV2
