import Survival.Basic
import Survival.FiniteCover

/-! The chronological stopped audit, finite means, and freshness primitives.
The constant namespace `Hybrid` is retained for API compatibility; this
module has no dependency on the numerical potential or its recurrence.
-/
noncomputable section
namespace Survival.Hybrid
open Finset Merkle.RandomOracle Bcs.FiniteProbability
open scoped Classical

variable {P A Out : Type} [Fintype A] [Nonempty A]

def audit (safe : P → A → Prop) (marked : P → Bool) :
    {fuel : ℕ} → Tree P A Out fuel → Tree P A (Bool × ℕ) fuel
  | _, .done _ => .done (false, 0)
  | _, .query point next => .query point fun answer =>
      if safe point answer then
        (audit safe marked (next answer)).map fun result =>
          (result.1, result.2 + if marked point then 1 else 0)
      else .done (true, if marked point then 1 else 0)

def reward (allowance : ℚ) (result : Bool × ℕ) : ℚ :=
  indicator result.1 + allowance * result.2

omit [Nonempty A] in
theorem mean_map {X Y : Type} (f : X → Y) (value : Y → ℚ) {fuel : ℕ}
    (tree : Tree P A X fuel) :
    TranscriptV2.FreshOracle.mean value (tree.map f) =
      TranscriptV2.FreshOracle.mean (fun x => value (f x)) tree := by
  induction tree with
  | done _ => rfl
  | query point next ih => simp only [Merkle.RandomOracle.Tree.map, TranscriptV2.FreshOracle.mean, ih]

omit [Nonempty A] in
theorem mean_add {X : Type} (f g : X → ℚ) {fuel : ℕ} (tree : Tree P A X fuel) :
    TranscriptV2.FreshOracle.mean (fun x => f x + g x) tree =
      TranscriptV2.FreshOracle.mean f tree + TranscriptV2.FreshOracle.mean g tree := by
  induction tree with
  | done _ => rfl
  | query point next ih =>
      simp only [TranscriptV2.FreshOracle.mean, ih, sum_add_distrib, add_div]

theorem mean_const {X : Type} (value : ℚ) {fuel : ℕ} (tree : Tree P A X fuel) :
    TranscriptV2.FreshOracle.mean (fun _ => value) tree = value := by
  induction tree with
  | done _ => rfl
  | query point next ih => simp [TranscriptV2.FreshOracle.mean, ih, Fintype.card_ne_zero]

omit [Fintype A] [Nonempty A] in
theorem fresh_map [DecidableEq P] {X Y : Type} (f : X → Y) {fuel : ℕ}
    (tree : Tree P A X fuel) {known : P → Prop}
    (fresh : TranscriptV2.FreshOracle.FreshFrom known tree) :
    TranscriptV2.FreshOracle.FreshFrom known (tree.map f) := by
  induction tree generalizing known with
  | done _ => trivial
  | query point next ih => exact ⟨fresh.1, fun a => ih a (fresh.2 a)⟩

omit [Fintype A] [Nonempty A] in
theorem audit_fresh [DecidableEq P] (safe : P → A → Prop) (marked : P → Bool)
    {fuel : ℕ} (tree : Tree P A Out fuel) {known : P → Prop}
    (fresh : TranscriptV2.FreshOracle.FreshFrom known tree) :
    TranscriptV2.FreshOracle.FreshFrom known (audit safe marked tree) := by
  induction tree generalizing known with
  | done _ => trivial
  | query point next ih =>
      refine ⟨fresh.1, fun answer => ?_⟩
      change TranscriptV2.FreshOracle.FreshFrom _
        (if safe point answer then _ else .done _)
      by_cases hs : safe point answer
      · simp only [hs, if_true]
        exact fresh_map _ _ (ih answer (fresh.2 answer))
      · simp only [hs, if_false, TranscriptV2.FreshOracle.FreshFrom]

end Survival.Hybrid
