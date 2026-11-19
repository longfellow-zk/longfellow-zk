import Survival.CausalCharges
import Lean.Util.CollectAxioms

/-! Adaptive prefix-state tests, early stopping around opaque queries, and
an independent import/axiom audit for the causal interface. -/
namespace Survival.CausalTests
open Merkle.RandomOracle TranscriptV2 Bcs.FiniteProbability

def charges : CausalCharges Bool (Fin 5) (fun _ => Fin 5) where
  extract _ past := match past.getLast? with
    | none => 0
    | some qa => qa.2
  single _ state answer := if answer = state then 1 else 0
  budget _ := 1/5
  nonneg _ _ _ := by split_ifs <;> norm_num
  mean _ state := by
    classical
    change (∑ answer : Fin 5, if answer = state then (1 : ℚ) else 0) ≤ 5*(1/5)
    norm_num

def adaptive : Tree Bool (Fin 5) Unit 2 :=
  .query false fun _ => .query true fun _ => .done ()

theorem adaptive_fresh : FreshOracle.FreshFrom (fun _ => False) adaptive := by
  refine ⟨fun h => h, fun _ => ⟨?_, fun _ => trivial⟩⟩
  rintro (same | impossible)
  · cases same
  · exact impossible

/-- The second root is the first answer, so the bad-answer set really
depends on the strict prefix. The exact two-query survival bound applies. -/
theorem adaptive_saturation :
    density (fun H => ((charges.audit (fun _ => false) adaptive).run H).1.1 = true) ≤ 9/25 := by
  have bound := charges.saturated_law_le_support (queries := 2) (fun _ => false) adaptive
    (1/5) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ => le_rfl) (by norm_num) adaptive_fresh
    (fun H => by simpa using Finset.card_le_univ (s := seen adaptive H))
  norm_num [Hybrid.envelope] at bound
  exact bound

theorem stops_before_opaque (H : Bool → Fin 5) (escaped : H false = 0) :
    ((charges.audit id adaptive).run H).1 = (true,0) := by
  simp [CausalCharges.audit, adaptive, History.audit_query, CausalCharges.safe,
    charges, escaped, Tree.run_query, Tree.run_done]

def opaqueFirst : Tree Bool (Fin 5) Unit 2 :=
  .query true fun _ => .query false fun _ => .done ()

theorem retains_prior_opaque (H : Bool → Fin 5) (escaped : H false = H true) :
    ((charges.audit id opaqueFirst).run H).1 = (true,1) := by
  simp [CausalCharges.audit, opaqueFirst, History.audit_query, CausalCharges.safe,
    CausalCharges.advance, charges, escaped, Tree.run_query, Tree.run_map, Tree.run_done]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for moduleName in env.header.moduleNames do
    if moduleName.toString == "Survival.PrefixCache" ||
        moduleName.toString.startsWith "LfzkV2" then
      throwError "Causal interface imports forbidden module {moduleName}"
  for endpoint in #[``CausalCharges.linear_failure_le_support,
      ``CausalCharges.failure_le_support, ``CausalCharges.stopped_charge_of_causal_cover,
      ``adaptive_saturation, ``stops_before_opaque, ``retains_prior_opaque] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"

end Survival.CausalTests
