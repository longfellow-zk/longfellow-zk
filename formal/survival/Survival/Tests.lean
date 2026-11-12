import Survival.HistoryBounds
import Survival.CausalTests
import Survival.State
import Survival.Sumcheck
import Mathlib.Tactic.FinCases

/-! Boundary examples: adaptive state-dependent root sets, reversed private
challenge revelation, early stopping, repeated names, Q=0, and the invalid
inference from own-coordinate root bounds to product survival.
-/
namespace Survival.Tests
open Finset Merkle.RandomOracle Bcs.FiniteProbability

abbrev Name := Bool × (Fin 5 × Fin 5)

def first : Name := (false, 0, 1)
def second (answer : Fin 5) : Name := (true, answer, ⟨(answer.val+1)%5, Nat.mod_lt _ (by decide)⟩)

def safe (point : Name) (answer : Fin 5) : Prop :=
  answer ∉ ({point.2.1, point.2.2} : Finset (Fin 5))

def adaptive : Tree Name (Fin 5) Unit 2 :=
  .query first fun r => .query (second r) fun _ => .done ()

/-- The first private challenge selects the next root set. The later
challenge can be revealed first, because both were cached in creation order. -/
theorem adaptive_fresh : TranscriptV2.FreshOracle.FreshFrom (fun _ => False) adaptive := by
  refine ⟨fun h => h, fun r => ⟨?_, fun _ => trivial⟩⟩
  rintro (same | impossible)
  · exact Bool.noConfusion (congrArg Prod.fst same)
  · exact impossible

theorem adaptive_hazard (point : Name) :
    density (fun answer => ¬safe point answer) ≤ (2/5 : ℚ) := by
  classical
  have count : ({point.2.1, point.2.2} : Finset (Fin 5)).card ≤ 2 := by
    simpa only [card_singleton] using card_insert_le point.2.1 ({point.2.2} : Finset (Fin 5))
  have scaled : (({point.2.1, point.2.2} : Finset (Fin 5)).card : ℚ)/5 ≤ 2/5 := by
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr count) (by norm_num)
  have seteq : univ.filter (fun answer => ¬safe point answer) =
      ({point.2.1, point.2.2} : Finset (Fin 5)) := by
    ext answer
    simp only [mem_filter, mem_univ, true_and, safe, not_not]
  apply density_le_of_ratio_le (fun answer => ¬safe point answer) (2/5)
  rw [seteq]
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using scaled

theorem adaptive_saturation :
    density (fun H => ¬((monitor (fun _ => safe) 0 adaptive).run H).1 = true) ≤ 16/25 := by
  have bound := Survival.escape_le safe (2/5) (by norm_num) (by norm_num)
    adaptive_hazard adaptive adaptive_fresh
  norm_num at bound ⊢
  exact bound

/-- Exact observation-law test for reversing two privately cached answers.
This is a finite permutation test, not a new arbitrary-adversary coupling. -/
theorem reversed_private_view (event : (Fin 5 × Fin 5) → Prop) :
    density (fun cache : Fin 5 × Fin 5 => event (cache.2,cache.1)) = density event :=
  density_equiv (Equiv.prodComm (Fin 5) (Fin 5)) event

def inflated : Tree Name (Fin 5) Unit 100 :=
  .query first fun r => .query (second r) fun _ => .done (fuel := 98) ()

theorem inflated_two : QueryBudget.AtMost 2 inflated := by
  intro _ _
  trivial

theorem inflated_run (H : Name → Fin 5) :
    (QueryBudget.cap 2 inflated inflated_two).run H = adaptive.run H := by
  rw [QueryBudget.cap_run]
  rfl

theorem repeated_not_fresh : ¬TranscriptV2.FreshOracle.FreshFrom (fun _ => False)
    (Tree.query first fun _ : Fin 5 => Tree.query first fun _ => Tree.done (fuel := 0) ()) := by
  intro fresh
  exact (fresh.2 0).1 (Or.inl rfl)

theorem zero_queries (rate opaqueFraction : ℚ) : Hybrid.envelope rate opaqueFraction 0 = 0 := by
  simp [Hybrid.envelope]

/-- Escaping at a transparent round must stop before paying a later opaque
query; reversing those two rounds must retain the already-paid opaque slot. -/
def mixedSafe (point answer : Bool) : Prop := point = true ∨ answer = false

def transparentFirst : Tree Bool Bool Unit 2 :=
  .query false fun _ => .query true fun _ => .done ()

def opaqueFirst : Tree Bool Bool Unit 2 :=
  .query true fun _ => .query false fun _ => .done ()

theorem stops_before_opaque (H : Bool → Bool) (escaped : H false = true) :
    ((Hybrid.audit mixedSafe id transparentFirst).run H).1 = (true,0) := by
  simp [transparentFirst, Hybrid.audit, mixedSafe, escaped]

theorem retains_prior_opaque (H : Bool → Bool) (escaped : H false = true) :
    ((Hybrid.audit mixedSafe id opaqueFirst).run H).1 = (true,1) := by
  simp [opaqueFirst, Hybrid.audit, mixedSafe, escaped]

/-- Fingerprint/opening charges can exceed one: the common round bound uses
nonnegativity and a mean bound, without assuming a Boolean indicator. -/
theorem multiple_indicator_query_step :
    density (fun answer : Bool => ¬(QueryStep.ofCharge false (fun a => if a then 2 else 0)).safe answer) ≤ 1 := by
  apply QueryStep.charge_hazard false (fun a : Bool => if a then 2 else 0) 1
  · intro answer; cases answer <;> norm_num
  · norm_num [Fintype.sum_bool]

def difference (cache : Fin 5 × Fin 5) : ℕ := (cache.2.val+5-cache.1.val)%5
def firstEvent (cache : Fin 5 × Fin 5) : Prop := difference cache = 0 ∨ difference cache = 1
def secondEvent (cache : Fin 5 × Fin 5) : Prop := difference cache = 2 ∨ difference cache = 3

instance firstEventDecidable : DecidablePred firstEvent := fun cache =>
  inferInstanceAs (Decidable (difference cache = 0 ∨ difference cache = 1))
instance secondEventDecidable : DecidablePred secondEvent := fun cache =>
  inferInstanceAs (Decidable (difference cache = 2 ∨ difference cache = 3))

theorem first_event_count : (univ.filter firstEvent).card = 10 := by decide +kernel
theorem second_event_count : (univ.filter secondEvent).card = 10 := by decide +kernel
theorem union_event_count : (univ.filter fun cache => firstEvent cache ∨ secondEvent cache).card = 20 := by
  decide +kernel

/-- Both events have probability 2/5, but their union is 4/5 rather than
at most 1-(1-2/5)^2. Their tests are not chronological at the first reveal. -/
theorem root_bounds_do_not_imply_product : (20/25 : ℚ) > 1-(1-10/25)^2 := by norm_num

end Survival.Tests
