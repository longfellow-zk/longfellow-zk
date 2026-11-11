import Survival.StoppedCharges
import Survival.PrefixCache
import Survival.SharedBudget
import Survival.QueryStep
import Bcs.ProbabilityBounds

/-! A chronological monitor for the existing nonnegative single charges.
Its test is fixed by the explicit cache before the current answer is drawn. -/
noncomputable section
namespace Survival.ChargeMonitor
open Finset Merkle.RandomOracle TranscriptV2 Bcs.FiniteProbability
open scoped Classical

variable {P D C Parent Response Out : Type}
variable [DecidableEq P] [Fintype D] [Fintype C] [Fintype Response]
variable (original : Composition.LocalCharges P D C Parent Response)

def safe (marked : P → Bool) (fallback : D × C)
    (state : List (P × (D × C)) × P) (answer : D × C) : Prop :=
  marked state.2 = true ∨ original.single state.2 (PrefixCache.cache fallback state.1) answer < 1

theorem opaque_safe (marked : P → Bool) (fallback : D × C)
    (past : List (P × (D × C))) (point : P) (markedPoint : marked point = true) (answer : D × C) :
    safe original marked fallback (past,point) answer := Or.inl markedPoint

variable [Nonempty D] [Nonempty C]

theorem hazard (marked : P → Bool) (fallback : D × C) (rate : ℚ)
    (budget : ∀ point, marked point = false → original.singleBudget point ≤ rate)
    (past : List (P × (D × C))) (point : P) (transparent : marked point = false) :
    density (fun answer => ¬safe original marked fallback (past,point) answer) ≤ rate := by
  have mean := (original.single_mean point (PrefixCache.cache fallback past)).trans
    (mul_le_mul_of_nonneg_left (budget point transparent) (Nat.cast_nonneg _))
  exact QueryStep.charge_hazard (marked point) (original.single point (PrefixCache.cache fallback past)) rate
    (original.single_nonneg point _) mean

omit [Nonempty D] [Nonempty C] in
theorem no_escape_single {fuel : ℕ} (marked : P → Bool) (fallback : D × C)
    (tree : Tree P (D × C) Out fuel) (H : P → D × C)
    (survived : ((History.audit (safe original marked fallback) marked PrefixCache.advance [] tree).run H).1.1 = false)
    (point : P) (present : point ∈ seen tree H) (transparent : marked point = false)
    (cached : ∀ past rest answer,
      (tree.run H).2 = past ++ (point,answer)::rest → past.map Prod.fst = before tree H point →
      original.single point (PrefixCache.cache fallback past) answer = original.single point H answer) :
    original.single point H (H point) < 1 := by
  obtain ⟨past,rest,answer,trace,before⟩ := trace_split_before tree H point present
  have test := History.safe_at_prefix (safe original marked fallback) marked PrefixCache.advance [] tree H
    survived past rest point answer trace
  rw [PrefixCache.advance_fold, List.nil_append] at test
  have actual := Merkle.RandomOracle.Tree.trace_sound tree H (point,answer) (by
    rw [trace]
    exact List.mem_append_right _ List.mem_cons_self)
  simp only [safe, transparent, Bool.false_eq_true, false_or] at test
  change answer = H point at actual
  rw [cached past rest answer trace before, actual] at test
  exact test

omit [Nonempty D] [Nonempty C] in
theorem stopped_charge_of_cover [Fintype Parent] {fuel rounds : ℕ}
    (marked : P → Bool) (fallback : D × C) (tree : Tree P (D × C) Out fuel) (H : P → D × C)
    (path : ℕ → P) (queriedPath : Composition.PathQueries (rounds := rounds) tree H path)
    (cover : original.Covers (rounds := rounds) path H)
    (survived : ((History.audit (safe original marked fallback) marked PrefixCache.advance [] tree).run H).1.1 = false)
    (transparent : ∀ i < rounds, marked (path i) = false → original.single (path i) H (H (path i)) < 1) :
    1 ≤ (StoppedCharges.restrict original marked).charge
      (History.audit (safe original marked fallback) marked PrefixCache.advance [] tree) H := by
  let stopped := History.audit (safe original marked fallback) marked PrefixCache.advance [] tree
  have same := History.audit_trace (safe original marked fallback) marked PrefixCache.advance [] tree H survived
  change (stopped.run H).2 = (tree.run H).2 at same
  have queries i (within : i ≤ rounds) : path i ∈ seen stopped H := by
    simpa only [seen, Bcs.TotalOracle.queried, same] using queriedPath.queried i within
  have ordered i (within : i < rounds) : Bcs.TotalOracle.firstOfTwo stopped H (path i) (path (i+1)) = .left := by
    rw [History.order_preserved (safe original marked fallback) marked PrefixCache.advance [] tree H survived]
    exact queriedPath.ordered i within
  exact SharedReduction.charges_of_cover stopped H path queries ordered
    (StoppedCharges.restrict original marked).single_nonneg
    (StoppedCharges.restrict original marked).pair_nonneg
    (StoppedCharges.covers_restrict original marked path H cover transparent)

omit [Nonempty D] [Nonempty C] in
theorem stopped_charge_of_cached_cover [Fintype Parent] {fuel rounds : ℕ}
    (marked : P → Bool) (fallback : D × C) (tree : Tree P (D × C) Out fuel) (H : P → D × C)
    (path : ℕ → P) (queriedPath : Composition.PathQueries (rounds := rounds) tree H path)
    (cover : original.Covers (rounds := rounds) path H)
    (survived : ((History.audit (safe original marked fallback) marked PrefixCache.advance [] tree).run H).1.1 = false)
    (cached : ∀ i < rounds, ∀ past rest answer,
      (tree.run H).2 = past ++ (path i,answer)::rest → past.map Prod.fst = before tree H (path i) →
      original.single (path i) (PrefixCache.cache fallback past) answer = original.single (path i) H answer) :
    1 ≤ (StoppedCharges.restrict original marked).charge
      (History.audit (safe original marked fallback) marked PrefixCache.advance [] tree) H := by
  apply stopped_charge_of_cover original marked fallback tree H path queriedPath cover survived
  intro i within transparent
  exact no_escape_single original marked fallback tree H survived (path i)
    (queriedPath.queried i within.le) transparent (cached i within)

/-- Leading linear accounting on the same chronological audit used by the
saturated refinement. There is no restriction on `rate * queries`. -/
theorem linear_law_le_support [Fintype P] {fuel queries : ℕ}
    (marked : P → Bool) (fallback : D × C) (tree : Tree P (D × C) Out fuel)
    (rate allowance : ℚ) (rate_nonnegative : 0 ≤ rate) (allowance_le : allowance ≤ rate)
    (localBudget : ∀ point, marked point = false → original.singleBudget point ≤ rate)
    (fresh : FreshOracle.FreshFrom (fun _ => False) tree)
    (queriesBound : ∀ H, (seen tree H).card ≤ queries) :
    density (fun H => ((History.audit (safe original marked fallback) marked PrefixCache.advance [] tree).run H).1.1 = true) +
      allowance*((∑ H : P → D × C,
        (((History.audit (safe original marked fallback) marked PrefixCache.advance [] tree).run H).1.2 : ℚ)) /
          Fintype.card (P → D × C)) ≤ rate*queries := by
  apply SharedBudget.accounting_le _ (StoppedSearch.transparent (safe original marked fallback)
    marked PrefixCache.advance [] tree) _ rate allowance queries rate_nonnegative allowance_le
  · exact StoppedSearch.counts_le_support (safe original marked fallback) marked PrefixCache.advance [] tree fresh queriesBound
  · exact StoppedSearch.escape_le (safe original marked fallback) marked PrefixCache.advance rate
      (opaque_safe original marked fallback) (hazard original marked fallback rate localBudget) [] tree fresh

/-- Integrate the common stopped cover and cost with the unrestricted
leading shared-budget bound. Saturation is not used by this theorem. -/
theorem linear_failure_le_support [Fintype P] {fuel queries : ℕ}
    (marked : P → Bool) (fallback : D × C) (tree : Tree P (D × C) Out fuel)
    (rate allowance : ℚ) (rate_nonnegative : 0 ≤ rate) (allowance_le : allowance ≤ rate)
    (localBudget : ∀ point, marked point = false → original.singleBudget point ≤ rate)
    (fresh : FreshOracle.FreshFrom (fun _ => False) tree)
    (queriesBound : ∀ H, (seen tree H).card ≤ queries)
    (failed hash : (P → D × C) → Prop) (cost : (P → D × C) → ℚ)
    (nonnegative : ∀ H, 0 ≤ cost H)
    (cover : ∀ H, failed H → ¬hash H →
      ((History.audit (safe original marked fallback) marked PrefixCache.advance [] tree).run H).1.1 = true ∨ 1 ≤ cost H)
    (cost_mean : (∑ H, cost H)/Fintype.card (P → D × C) ≤
      allowance*((∑ H : P → D × C,
        (((History.audit (safe original marked fallback) marked PrefixCache.advance [] tree).run H).1.2 : ℚ)) /
          Fintype.card (P → D × C))) :
    density failed ≤ rate*queries + density hash := by
  have bound := SharedBudget.linear_le failed hash _
    (StoppedSearch.transparent (safe original marked fallback) marked PrefixCache.advance [] tree) _
    cost rate allowance queries rate_nonnegative allowance_le nonnegative cover
    (StoppedSearch.counts_le_support (safe original marked fallback) marked PrefixCache.advance [] tree fresh queriesBound)
    (StoppedSearch.escape_le (safe original marked fallback) marked PrefixCache.advance rate
      (opaque_safe original marked fallback) (hazard original marked fallback rate localBudget) [] tree fresh)
    cost_mean
  simpa only [add_comm] using bound

end Survival.ChargeMonitor
