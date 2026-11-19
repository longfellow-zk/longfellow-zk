import Bcs.OracleReachability

/-! A public constraint x=0 has an unreachable, unsatisfiable x=1 request.
Validity on actual results holds; validity at every context would fail. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeReachability
open Merkle.RandomOracle Bcs.OracleReachability

private def before : Tree Unit Unit Bool 0 := .done false
private def satisfies (request : Bool) : Prop := (if request then (1 : ℚ) else 0) = 0

theorem returned_requests_valid : ∀ context, Returns before context → satisfies context := by
  intro context returned
  obtain ⟨H,same⟩ := returned
  have value : context = false := same.symm
  rw [value]
  rfl

theorem unreachable_request_invalid : ¬ satisfies true := by norm_num [satisfies]

theorem no_global_witness_condition : ¬ ∀ context, satisfies context := by
  intro allContexts
  exact unreachable_request_invalid (allContexts true)

/-- The reached-output interface genuinely applies despite the invalid
unreachable request, for every possible oracle. -/
theorem reached_interface_applies (H : Unit → Unit) : satisfies (before.run H).1 :=
  valid_on_run before satisfies returned_requests_valid H

private def values (H : Unit → Bool) : Bool := H ()

private def beforeFamily (visible : Bool) : Tree Unit Bool Bool 1 :=
  .query () fun answer => .done (visible && !answer)

/-- A setup derived from the same oracle prevents an invalid request that
would be reachable in an inconsistent frozen-setup experiment. -/
theorem setup_consistent_requests_valid :
    ∀ context, FamilyReturns values beforeFamily context → satisfies context := by
  intro context returned
  obtain ⟨H,same⟩ := returned
  have selected : ((beforeFamily (values H)).run H).1 = false := by
    cases answer : H () <;> simp [beforeFamily,values,Tree.run_query,Tree.run_done,answer]
  have value : context = false := same.symm.trans selected
  rw [value]
  rfl

theorem inconsistent_setup_can_return_invalid :
    ((beforeFamily true).run (fun _ => false)).1 = true := rfl

end LfzkV2.Current.Tests.ZeroKnowledgeReachability
