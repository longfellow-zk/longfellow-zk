import Survival.Audit
import Survival.ChargeMonitor

/-! Saturation is a refinement of the same chronological search and failure
cover. Only this layer requires `rate * queries ≤ 1`; generic linear shared
budget accounting is independent of W. Constant namespaces are preserved. -/
noncomputable section
open Finset Merkle.RandomOracle Bcs.FiniteProbability TranscriptV2 Bcs.TotalOracle
open scoped Classical
namespace Survival.History
variable {P A Out S : Type}

variable [Fintype A] [Nonempty A]

omit [Nonempty A] in
private theorem mean_rename {Q X : Type} (rename : Q → P) (value : X → ℚ)
    {fuel : ℕ} (tree : Tree Q A X fuel) :
    FreshOracle.mean value (mapQueries rename tree) = FreshOracle.mean value tree := by
  induction tree with
  | done _ => rfl
  | query point next ih => simp only [mapQueries, FreshOracle.mean, ih]

theorem audit_mean_le (safe : S × P → A → Prop) (marked : P → Bool) (step : S → P → A → S)
    (rate opaqueFraction : ℚ) (hr : 0 ≤ rate) (hr1 : rate ≤ 1) (hl : 0 ≤ opaqueFraction) (hl1 : opaqueFraction ≤ 1)
    (opaque_safe : ∀ state point, marked point = true → ∀ answer, safe (state,point) answer)
    (hazard : ∀ state point, marked point = false → density (fun answer => ¬safe (state,point) answer) ≤ rate)
    {fuel : ℕ} (state : S) (tree : Tree P A Out fuel) (budget : rate*fuel ≤ 1) :
    FreshOracle.mean (Hybrid.reward (opaqueFraction*rate)) (audit safe marked step state tree) ≤
      Hybrid.envelope rate opaqueFraction fuel := by
  rw [audit, mean_rename, Hybrid.audit_mean]
  exact Hybrid.payoff_le safe (fun point => marked point.2) rate opaqueFraction hr hr1 hl hl1
    (fun point => opaque_safe point.1 point.2) (fun point => hazard point.1 point.2)
    (enrich step state tree) budget

/-- The chronological branch bound is the actual uniform finite-oracle law,
including the number of opaque queries reached before the first escape. -/
theorem audit_law_le [Fintype P] [DecidableEq P]
    (safe : S × P → A → Prop) (marked : P → Bool) (step : S → P → A → S)
    (rate opaqueFraction : ℚ) (hr : 0 ≤ rate) (hr1 : rate ≤ 1) (hl : 0 ≤ opaqueFraction) (hl1 : opaqueFraction ≤ 1)
    (opaque_safe : ∀ state point, marked point = true → ∀ answer, safe (state,point) answer)
    (hazard : ∀ state point, marked point = false → density (fun answer => ¬safe (state,point) answer) ≤ rate)
    {fuel : ℕ} (state : S) (tree : Tree P A Out fuel) (budget : rate*fuel ≤ 1)
    (fresh : FreshOracle.FreshFrom (fun _ => False) tree) :
    density (fun H => ((audit safe marked step state tree).run H).1.1 = true) +
      (opaqueFraction*rate) * ((∑ H : P → A, (((audit safe marked step state tree).run H).1.2 : ℚ)) /
        Fintype.card (P → A)) ≤ Hybrid.envelope rate opaqueFraction fuel := by
  have law := FreshOracle.uniform_mean (Hybrid.reward (opaqueFraction*rate))
    (audit safe marked step state tree) (audit_fresh safe marked step state tree fresh)
  have bound := audit_mean_le safe marked step rate opaqueFraction hr hr1 hl hl1 opaque_safe hazard
    state tree budget
  rw [FiniteCover.density_indicator, ← mul_div_assoc, mul_sum, ← add_div, ← sum_add_distrib]
  rw [Fintype.card_fun, Nat.cast_pow]
  apply le_trans ?_ (law.trans_le bound)
  apply le_of_eq
  congr 1
  apply sum_congr rfl
  intro H _
  cases hb : ((audit safe marked step state tree).run H).1.1 <;>
    simp [Hybrid.reward, indicator, hb]

/-- Stateful finite-oracle integration. The cost is charged on the stopped
trace; its weights can retain the original, unstopped commitment cut. -/
theorem failure_le [Fintype P] [DecidableEq P]
    (safe : S × P → A → Prop) (marked : P → Bool) (step : S → P → A → S)
    (rate opaqueFraction correction : ℚ) (hr : 0 ≤ rate) (hr1 : rate ≤ 1) (hl : 0 ≤ opaqueFraction) (hl1 : opaqueFraction ≤ 1)
    (opaque_safe : ∀ state point, marked point = true → ∀ answer, safe (state,point) answer)
    (hazard : ∀ state point, marked point = false → density (fun answer => ¬safe (state,point) answer) ≤ rate)
    {fuel : ℕ} (state : S) (tree : Tree P A Out fuel) (budget : rate*fuel ≤ 1)
    (fresh : FreshOracle.FreshFrom (fun _ => False) tree)
    (failed hash : (P → A) → Prop) (cost : (P → A) → ℚ)
    (nonnegative : ∀ H, 0 ≤ cost H)
    (cover : ∀ H, failed H → ¬hash H →
      ((audit safe marked step state tree).run H).1.1 = true ∨ 1 ≤ cost H)
    (cost_mean : (∑ H, cost H) / Fintype.card (P → A) ≤
      opaqueFraction*rate*((∑ H : P → A, (((audit safe marked step state tree).run H).1.2 : ℚ)) /
        Fintype.card (P → A)))
    (hash_mean : density hash ≤ correction) :
    density failed ≤ Hybrid.envelope rate opaqueFraction fuel + correction := by
  have law := audit_law_le safe marked step rate opaqueFraction hr hr1 hl hl1 opaque_safe hazard state tree budget fresh
  exact (FiniteCover.failure_le failed hash _ _ cost (opaqueFraction*rate) _ nonnegative cover cost_mean law).trans
    (add_le_add le_rfl hash_mean)

end Survival.History

namespace Survival.QueryBudget
variable {P A Out : Type}

/-- Apply the stateful hybrid law using the adversary's distinct-query
bound, irrespective of the much larger memoized syntactic fuel. -/
theorem history_law_le_support {S : Type} [Fintype P] [DecidableEq P] [Fintype A] [Nonempty A]
    (safe : S × P → A → Prop) (marked : P → Bool) (step : S → P → A → S)
    (rate opaqueFraction : ℚ) (hr : 0 ≤ rate) (hr1 : rate ≤ 1) (hl : 0 ≤ opaqueFraction) (hl1 : opaqueFraction ≤ 1)
    (opaque_safe : ∀ state point, marked point = true → ∀ answer, safe (state,point) answer)
    (hazard : ∀ state point, marked point = false →
      Bcs.FiniteProbability.density (fun answer => ¬safe (state,point) answer) ≤ rate)
    {fuel queries : ℕ} (state : S) (tree : Tree P A Out fuel) (budget : rate*queries ≤ 1)
    (fresh : TranscriptV2.FreshOracle.FreshFrom (fun _ => False) tree)
    (bounded : ∀ H, (TranscriptV2.seen tree H).card ≤ queries) :
    Bcs.FiniteProbability.density (fun H => ((History.audit safe marked step state tree).run H).1.1 = true) +
      (opaqueFraction*rate) * ((∑ H : P → A, (((History.audit safe marked step state tree).run H).1.2 : ℚ)) /
        Fintype.card (P → A)) ≤ Hybrid.envelope rate opaqueFraction queries := by
  have depth : AtMost queries tree := atMost_of_distinct tree fresh bounded
  have capped := History.audit_law_le safe marked step rate opaqueFraction hr hr1 hl hl1 opaque_safe hazard
    state (cap queries tree depth) budget (cap_fresh tree depth fresh)
  simpa only [cap_historyAudit_run] using capped

end Survival.QueryBudget

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
