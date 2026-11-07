import LfzkV2.Current.ZeroKnowledge.OracleWindow

/-! The query domain in this test is infinite. The later target depends on
the earlier answer, and finite-window transport still retains the full trace. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeOracleWindow

open Merkle.RandomOracle ZeroKnowledge.OracleWindow

def prior : Tree ℕ Bool ℕ 1 :=
  .query 7 fun answer => .done (if answer then 18 else 22)

example (H : ℕ → Bool) :
    (prior.run H).1 ∈ queries (withTarget prior id) := target_mem prior id H

example (H : ℕ → Bool) :
    prior.run (extend (window prior id 0) (fun query => H query.val) (fun _ => false)) =
      prior.run H := run_extend _ prior (queries_subset_window prior id 0) H _

example (H : ℕ → Bool) :
    (targetInWindow prior id 0 (prior.run H).1).val = (prior.run H).1 :=
  targetInWindow_run prior id 0 H

#print axioms trace_mem_queries
#print axioms restrict_run
#print axioms restrict_extend_run
#print axioms run_extend
#print axioms target_mem
#print axioms queries_subset_window
#print axioms targetInWindow_run

end LfzkV2.Current.Tests.ZeroKnowledgeOracleWindow
