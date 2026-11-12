import TranscriptV2.FreshOracle
import Bcs.FiniteProbability
import Mathlib.Tactic.Positivity

/-! Chronological safety on fresh adaptive query trees.

The query name must contain everything needed to decide the current safe
answer set. In a strand application that includes the privately completed
ancestor state. An arbitrary own-answer-independent global predicate does
not satisfy this interface automatically.
-/
noncomputable section
namespace Survival
open Finset Merkle.RandomOracle Bcs.FiniteProbability
open scoped Classical

variable {P A Out : Type} [Fintype A] [Nonempty A]

def indicator (b : Bool) : ℚ := if b then 1 else 0

/-- Stop on the first escape; the event is determined by the past and the
current answer. Stopping early also retains the original fuel bound. -/
def monitor (safe : ℕ → P → A → Prop) : {fuel : ℕ} →
    ℕ → Tree P A Out fuel → Tree P A Bool fuel
  | _, _, .done _ => .done true
  | _, time, .query point next => .query point fun answer =>
      if safe time point answer then monitor safe (time+1) (next answer)
      else .done false

def product (lower : ℕ → ℚ) : ℕ → ℕ → ℚ
  | _, 0 => 1
  | time, fuel+1 => lower time * product lower (time+1) fuel

theorem product_nonneg (lower : ℕ → ℚ) (nonnegative : ∀ time, 0 ≤ lower time)
    (time fuel : ℕ) : 0 ≤ product lower time fuel := by
  induction fuel generalizing time with
  | zero => norm_num [product]
  | succ fuel ih => exact mul_nonneg (nonnegative time) (ih (time+1))

theorem product_le_one (lower : ℕ → ℚ) (nonnegative : ∀ time, 0 ≤ lower time)
    (bounded : ∀ time, lower time ≤ 1) (time fuel : ℕ) : product lower time fuel ≤ 1 := by
  induction fuel generalizing time with
  | zero => exact le_rfl
  | succ fuel ih =>
      exact (mul_le_mul_of_nonneg_left (ih (time+1)) (nonnegative time)).trans
        (by simpa only [mul_one] using bounded time)

theorem product_const (value : ℚ) (time fuel : ℕ) :
    product (fun _ => value) time fuel = value^fuel := by
  induction fuel generalizing time with
  | zero => simp [product]
  | succ fuel ih => rw [product, ih, pow_succ]; ring

omit [Fintype A] [Nonempty A] in
theorem monitor_fresh {fuel : ℕ} {known : P → Prop}
    (safe : ℕ → P → A → Prop) (time : ℕ) (tree : Tree P A Out fuel)
    (fresh : TranscriptV2.FreshOracle.FreshFrom known tree) :
    TranscriptV2.FreshOracle.FreshFrom known (monitor safe time tree) := by
  induction tree generalizing time known with
  | done _ => simp only [monitor, TranscriptV2.FreshOracle.FreshFrom]
  | query point next ih =>
      refine ⟨fresh.1, fun answer => ?_⟩
      change TranscriptV2.FreshOracle.FreshFrom _
        (if safe time point answer then monitor safe (time+1) (next answer) else .done false)
      split_ifs
      · exact ih answer (time+1) (fresh.2 answer)
      · trivial

/-- Product survival for an adaptive tree. Each local bound holds for every
past state, so no independence of the escape events is required. -/
theorem mean_survival_ge (safe : ℕ → P → A → Prop) (lower : ℕ → ℚ)
    (nonnegative : ∀ time, 0 ≤ lower time) (bounded : ∀ time, lower time ≤ 1)
    (hazard : ∀ time point,
      lower time ≤ ((univ.filter (safe time point)).card : ℚ) / Fintype.card A)
    {fuel : ℕ} (time : ℕ) (tree : Tree P A Out fuel) :
    product lower time fuel ≤ TranscriptV2.FreshOracle.mean indicator (monitor safe time tree) := by
  induction tree generalizing time with
  | done output =>
      simpa only [monitor, TranscriptV2.FreshOracle.mean, indicator, if_true] using
        product_le_one lower nonnegative bounded time _
  | @query fuel point next ih =>
      have tail := product_nonneg lower nonnegative (time+1) fuel
      have each (answer : A) :
          (if safe time point answer then product lower (time+1) fuel else 0) ≤
          TranscriptV2.FreshOracle.mean indicator
            (if safe time point answer then monitor safe (time+1) (next answer) else .done false) := by
        split_ifs
        · exact ih answer (time+1)
        · exact le_rfl
      have sumBound := div_le_div_of_nonneg_right (sum_le_sum (s := univ) (fun answer _ => each answer))
        (show (0 : ℚ) ≤ Fintype.card A by positivity)
      have sumEq : (∑ answer : A, if safe time point answer then product lower (time+1) fuel else 0) =
          (univ.filter (safe time point)).card * product lower (time+1) fuel := by
        rw [← sum_filter]
        simp only [sum_const, nsmul_eq_mul]
      have scaled := mul_le_mul_of_nonneg_right (hazard time point) tail
      rw [sumEq] at sumBound
      exact (scaled.trans_eq (by ring)).trans sumBound

/-- Uniform-oracle form of the product theorem. Freshness means repeated
raw inputs were memoized before this tree was constructed. -/
theorem survival_ge [Fintype P] [DecidableEq P]
    (safe : ℕ → P → A → Prop) (lower : ℕ → ℚ)
    (nonnegative : ∀ time, 0 ≤ lower time) (bounded : ∀ time, lower time ≤ 1)
    (hazard : ∀ time point,
      lower time ≤ ((univ.filter (safe time point)).card : ℚ) / Fintype.card A)
    {fuel : ℕ} (time : ℕ) (tree : Tree P A Out fuel)
    (fresh : TranscriptV2.FreshOracle.FreshFrom (fun _ => False) tree) :
    product lower time fuel ≤ density (fun H => ((monitor safe time tree).run H).1 = true) := by
  classical
  have law := TranscriptV2.FreshOracle.uniform_mean indicator (monitor safe time tree)
    (monitor_fresh safe time tree fresh)
  have densityEq : density (fun H => ((monitor safe time tree).run H).1 = true) =
      (∑ H : P → A, indicator ((monitor safe time tree).run H).1) /
        (Fintype.card A : ℚ)^Fintype.card P := by
    unfold density
    rw [Fintype.card_fun, Nat.cast_pow]
    congr 1
    have same : ∀ H : P → A, indicator ((monitor safe time tree).run H).1 =
        if ((monitor safe time tree).run H).1 = true then 1 else 0 := by
      intro H
      cases ((monitor safe time tree).run H).1 <;> rfl
    simp_rw [same]
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
    congr 1
    ext H
    simp
  rw [densityEq, law]
  exact mean_survival_ge safe lower nonnegative bounded hazard time tree

theorem escape_le [Fintype P] [DecidableEq P]
    (safe : P → A → Prop) (rate : ℚ) (rate_nonneg : 0 ≤ rate) (rate_le_one : rate ≤ 1)
    (hazard : ∀ point,
      density (fun a => ¬safe point a) ≤ rate)
    {fuel : ℕ} (tree : Tree P A Out fuel)
    (fresh : TranscriptV2.FreshOracle.FreshFrom (fun _ => False) tree) :
    density (fun H => ¬((monitor (fun _ => safe) 0 tree).run H).1 = true) ≤
      1-(1-rate)^fuel := by
  classical
  have localSafe (time : ℕ) (point : P) :
      1-rate ≤ ((univ.filter (safe point)).card : ℚ) / Fintype.card A := by
    have complementary := density_not (safe point)
    have bad := hazard point
    have good : 1-rate ≤ density (safe point) := by linarith
    simpa only [density] using good
  have survived := survival_ge (fun _ => safe) (fun _ => 1-rate)
    (fun _ => sub_nonneg.mpr rate_le_one) (fun _ => by linarith) localSafe 0 tree fresh
  rw [product_const] at survived
  rw [density_not]
  linarith

end Survival
