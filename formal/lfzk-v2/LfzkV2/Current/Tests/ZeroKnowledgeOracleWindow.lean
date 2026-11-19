import LfzkV2.Current.OracleWindow

/-! The query domain in this test is infinite. The later target depends on
the earlier answer, and finite-window transport still retains the full trace. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeOracleWindow

open Merkle.RandomOracle OracleWindow

def prior : Tree ℕ Bool ℕ 1 :=
  .query 7 fun answer => .done (if answer then 18 else 22)

#print axioms trace_mem_queries
#print axioms restrict_run
#print axioms restrict_extend_run

end LfzkV2.Current.Tests.ZeroKnowledgeOracleWindow
