import Survival.HistoryBounds
import Survival.ChargeMonitor

/-! Cached-monitor compatibility during migration to causal local charges. -/
noncomputable section
open Finset Merkle.RandomOracle Bcs.FiniteProbability TranscriptV2 Bcs.TotalOracle
open scoped Classical
namespace Survival.ChargeMonitor
variable {P D C Parent Response Out : Type}
variable [DecidableEq P] [Fintype D] [Fintype C] [Fintype Response]
variable (original : Composition.LocalCharges P D C Parent Response)
variable [Nonempty D] [Nonempty C]

/-- Compose the local round bound, original distinct-query budget and stopped
cost mean once. Runtime clients need only their causal cover and cost analysis. -/
theorem failure_le_support [Fintype P] {fuel queries : ℕ}
    (marked : P → Bool) (fallback : D × C) (tree : Tree P (D × C) Out fuel)
    (rate opaqueFraction : ℚ) (hr : 0 ≤ rate) (hr1 : rate ≤ 1) (hl : 0 ≤ opaqueFraction) (hl1 : opaqueFraction ≤ 1)
    (localBudget : ∀ point, marked point = false → original.singleBudget point ≤ rate)
    (queryBudget : rate*queries ≤ 1)
    (fresh : FreshOracle.FreshFrom (fun _ => False) tree)
    (queriesBound : ∀ H, (seen tree H).card ≤ queries)
    (failed hash : (P → D × C) → Prop) (cost : (P → D × C) → ℚ)
    (nonnegative : ∀ H, 0 ≤ cost H)
    (cover : ∀ H, failed H → ¬hash H →
      ((History.audit (safe original marked fallback) marked PrefixCache.advance [] tree).run H).1.1 = true ∨ 1 ≤ cost H)
    (cost_mean : (∑ H, cost H)/Fintype.card (P → D × C) ≤
      (opaqueFraction*rate)*((∑ H : P → D × C,
        (((History.audit (safe original marked fallback) marked PrefixCache.advance [] tree).run H).1.2 : ℚ)) /
          Fintype.card (P → D × C))) :
    density failed ≤ Hybrid.envelope rate opaqueFraction queries + density hash := by
  apply FiniteCover.failure_le failed hash _ _ cost (opaqueFraction*rate) _ nonnegative cover cost_mean
  exact QueryBudget.history_law_le_support (safe original marked fallback) marked PrefixCache.advance
    rate opaqueFraction hr hr1 hl hl1 (opaque_safe original marked fallback)
    (hazard original marked fallback rate localBudget) [] tree queryBudget fresh queriesBound

end Survival.ChargeMonitor
