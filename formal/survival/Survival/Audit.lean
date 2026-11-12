import Survival.Hybrid

/-! Saturated payoff integration. Generic chronological primitives live in
`ChronologicalAudit`; this module adds the numerical W refinement. -/
noncomputable section
namespace Survival.Hybrid
open Finset Merkle.RandomOracle Bcs.FiniteProbability
open scoped Classical
variable {P A Out : Type} [Fintype A] [Nonempty A]

theorem audit_mean (safe : P → A → Prop) (marked : P → Bool) (allowance : ℚ)
    {fuel : ℕ} (tree : Tree P A Out fuel) :
    TranscriptV2.FreshOracle.mean (reward allowance) (audit safe marked tree) =
      payoff safe marked allowance tree := by
  induction tree with
  | done _ => simp [audit, TranscriptV2.FreshOracle.mean, reward, indicator, payoff]
  | query point next ih =>
      have each (answer : A) :
          TranscriptV2.FreshOracle.mean (reward allowance)
            (if safe point answer then
              (audit safe marked (next answer)).map fun result =>
                (result.1, result.2 + if marked point then 1 else 0)
             else .done (true, if marked point then 1 else 0)) =
          (if safe point answer then payoff safe marked allowance (next answer) else 1) +
            (if marked point then allowance else 0) := by
        by_cases hs : safe point answer
        · simp only [hs, if_true, mean_map]
          have values : (fun result : Bool × ℕ =>
              reward allowance (result.1, result.2 + if marked point then 1 else 0)) =
              fun result => reward allowance result + (if marked point then allowance else 0) := by
            funext result
            cases marked point <;> simp [reward, Nat.cast_add, mul_add, add_assoc]
          rw [values, mean_add, mean_const, ih]
        · cases hm : marked point <;>
            simp [hs, TranscriptV2.FreshOracle.mean, reward, indicator]
      simp only [audit, TranscriptV2.FreshOracle.mean]
      simp_rw [each]
      simp only [payoff, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, add_div]
      have nonzero : (Fintype.card A : ℚ) ≠ 0 := by positivity
      field_simp
      ring

theorem audit_law [Fintype P] [DecidableEq P]
    (safe : P → A → Prop) (marked : P → Bool) (allowance : ℚ)
    {fuel : ℕ} (tree : Tree P A Out fuel)
    (fresh : TranscriptV2.FreshOracle.FreshFrom (fun _ => False) tree) :
    density (fun H => ((audit safe marked tree).run H).1.1 = true) +
      allowance * ((∑ H : P → A, (((audit safe marked tree).run H).1.2 : ℚ)) /
        Fintype.card (P → A)) = payoff safe marked allowance tree := by
  have law := TranscriptV2.FreshOracle.uniform_mean (reward allowance) (audit safe marked tree)
    (audit_fresh safe marked tree fresh)
  rw [audit_mean] at law
  rw [FiniteCover.density_indicator]
  rw [← mul_div_assoc, mul_sum, ← add_div, ← sum_add_distrib]
  rw [Fintype.card_fun, Nat.cast_pow]
  apply Eq.trans ?_ law
  congr 1
  apply sum_congr rfl
  intro H _
  cases hb : ((audit safe marked tree).run H).1.1 <;> simp [reward, indicator, hb]

/-- Integration contract. The backend's global charge may depend on both
answers, but its mean must be paid by opaque counts in this stopped audit.
There is no conditional backend-probability premise. -/
theorem failure_le [Fintype P] [DecidableEq P]
    (safe : P → A → Prop) (marked : P → Bool) (rate opaqueFraction correction : ℚ)
    (hr : 0 ≤ rate) (hr1 : rate ≤ 1) (hl : 0 ≤ opaqueFraction) (hl1 : opaqueFraction ≤ 1)
    (opaque_safe : ∀ point, marked point = true → ∀ answer, safe point answer)
    (hazard : ∀ point, marked point = false → density (fun answer => ¬safe point answer) ≤ rate)
    {fuel : ℕ} (tree : Tree P A Out fuel) (budget : rate*fuel ≤ 1)
    (fresh : TranscriptV2.FreshOracle.FreshFrom (fun _ => False) tree)
    (failed hash : (P → A) → Prop) (cost : (P → A) → ℚ)
    (nonnegative : ∀ H, 0 ≤ cost H)
    (cover : ∀ H, failed H → ¬hash H →
      ((audit safe marked tree).run H).1.1 = true ∨ 1 ≤ cost H)
    (cost_mean : (∑ H, cost H) / Fintype.card (P → A) ≤
      opaqueFraction*rate*((∑ H : P → A, (((audit safe marked tree).run H).1.2 : ℚ)) /
        Fintype.card (P → A)))
    (hash_mean : density hash ≤ correction) :
    density failed ≤ envelope rate opaqueFraction fuel + correction := by
  have law := (audit_law safe marked (opaqueFraction*rate) tree fresh).trans_le
    (payoff_le safe marked rate opaqueFraction hr hr1 hl hl1 opaque_safe hazard tree budget)
  exact (FiniteCover.failure_le failed hash _ _ cost (opaqueFraction*rate) _ nonnegative cover cost_mean law).trans
    (add_le_add le_rfl hash_mean)

end Survival.Hybrid
