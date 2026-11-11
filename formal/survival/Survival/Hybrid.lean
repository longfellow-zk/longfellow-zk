import Survival.StoppedSearch
import Survival.QueryStep

/-! Application hazards and an opaque Polygero charge share one budget.

Opaque queries incur an allowance `opaqueFraction * rate`; they need no per-answer
hazard theorem. Stop the search at the first application escape. The required
Polygero bridge is a mean-charge bound on that stopped search, NOT a bound
conditional on eventual application safety.
-/
noncomputable section
namespace Survival.Hybrid
open Finset Merkle.RandomOracle Bcs.FiniteProbability
open scoped Classical

variable {P A Out : Type} [Fintype A] [Nonempty A]

def envelope (rate opaqueFraction : ℚ) (fuel : ℕ) : ℚ :=
  opaqueFraction*rate*fuel + (1-opaqueFraction)*(1-(1-rate)^fuel)

theorem envelope_nonneg (rate opaqueFraction : ℚ) (hr : 0 ≤ rate) (hr1 : rate ≤ 1)
    (hl : 0 ≤ opaqueFraction) (hl1 : opaqueFraction ≤ 1) (fuel : ℕ) : 0 ≤ envelope rate opaqueFraction fuel := by
  unfold envelope
  exact add_nonneg (by positivity)
    (mul_nonneg (by linarith) (sub_nonneg.mpr (pow_le_one₀ (by linarith) (by linarith))))

theorem envelope_le_one (rate opaqueFraction : ℚ) (hr1 : rate ≤ 1)
    (hl : 0 ≤ opaqueFraction) (hl1 : opaqueFraction ≤ 1) (fuel : ℕ)
    (budget : rate*fuel ≤ 1) : envelope rate opaqueFraction fuel ≤ 1 := by
  have bound := mul_le_mul_of_nonneg_left budget hl
  have positive : 0 ≤ (1-rate)^fuel := pow_nonneg (by linarith) _
  unfold envelope
  nlinarith

theorem application_step (rate opaqueFraction : ℚ) (hl : 0 ≤ opaqueFraction) (fuel : ℕ) :
    rate+(1-rate)*envelope rate opaqueFraction fuel ≤ envelope rate opaqueFraction (fuel+1) := by
  have nonnegative : 0 ≤ opaqueFraction*rate^2*(fuel : ℚ) := by positivity
  simp only [envelope, Nat.cast_add, Nat.cast_one, pow_succ]
  nlinarith

theorem opaque_step (rate opaqueFraction : ℚ) (hr : 0 ≤ rate) (hr1 : rate ≤ 1)
    (hl1 : opaqueFraction ≤ 1) (fuel : ℕ) :
    opaqueFraction*rate+envelope rate opaqueFraction fuel ≤ envelope rate opaqueFraction (fuel+1) := by
  have nonnegative : 0 ≤ (1-opaqueFraction)*rate*(1-rate)^fuel :=
    mul_nonneg (mul_nonneg (by linarith) hr) (pow_nonneg (by linarith) _)
  simp only [envelope, Nat.cast_add, Nat.cast_one, pow_succ]
  nlinarith

/-- Expected escape indicator plus the opaque allowances collected BEFORE
the first application escape. Adaptive role choices and stopping are allowed. -/
def payoff (safe : P → A → Prop) (marked : P → Bool) (allowance : ℚ) :
    {fuel : ℕ} → Tree P A Out fuel → ℚ
  | _, .done _ => 0
  | _, .query point next => (if marked point then allowance else 0) +
      (∑ answer : A, if safe point answer then payoff safe marked allowance (next answer) else 1) /
        Fintype.card A

theorem payoff_le (safe : P → A → Prop) (marked : P → Bool) (rate opaqueFraction : ℚ)
    (hr : 0 ≤ rate) (hr1 : rate ≤ 1) (hl : 0 ≤ opaqueFraction) (hl1 : opaqueFraction ≤ 1)
    (opaque_safe : ∀ point, marked point = true → ∀ answer, safe point answer)
    (hazard : ∀ point, marked point = false → density (fun answer => ¬safe point answer) ≤ rate)
    {fuel : ℕ} (tree : Tree P A Out fuel) (budget : rate*fuel ≤ 1) :
    payoff safe marked (opaqueFraction*rate) tree ≤ envelope rate opaqueFraction fuel := by
  induction tree with
  | done output => exact envelope_nonneg rate opaqueFraction hr hr1 hl hl1 _
  | @query fuel point next ih =>
      have tailBudget : rate*(fuel : ℚ) ≤ 1 := by
        push_cast at budget
        nlinarith
      let step : QueryStep A := ⟨marked point, safe point, opaque_safe point⟩
      exact QueryStep.step_le step rate (opaqueFraction*rate) (envelope rate opaqueFraction fuel)
        (envelope rate opaqueFraction (fuel+1))
        (envelope_le_one rate opaqueFraction hr1 hl hl1 fuel tailBudget) (hazard point)
        (application_step rate opaqueFraction hl fuel) (opaque_step rate opaqueFraction hr hr1 hl1 fuel)
        (fun answer => payoff safe marked (opaqueFraction*rate) (next answer)) (fun answer => ih answer tailBudget)

/-- A sufficient numerical handoff: if survival is at least 1/3, opaque
allowances cost at most 51% of the application rate, and rate*Q <= 1, the
combined error including a 1/8 hash allowance is below 1. -/
theorem nonvacuous_of_survival (rate opaqueFraction correction : ℚ)
    (hl : 0 ≤ opaqueFraction) (hl51 : opaqueFraction ≤ 51/100) (fuel : ℕ)
    (budget : rate*fuel ≤ 1) (survives : (1/3 : ℚ) ≤ (1-rate)^fuel)
    (hash : correction ≤ 1/8) :
    envelope rate opaqueFraction fuel+correction ≤ 577/600 := by
  have weighted := mul_le_mul_of_nonneg_left budget hl
  have tail := mul_le_mul_of_nonneg_left survives (show 0 ≤ 1-opaqueFraction by linarith)
  unfold envelope
  nlinarith

end Survival.Hybrid
