import LfzkV2.Current.ZeroKnowledge.BackendRuntimeRefreshCoins

/-! The primary-mask split is an exact equivalence of actual source coins.
Its unused label tape remains independent of the primary-mask samples. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeRefreshCoins
open ZeroKnowledge

#check @BackendRuntimeRefreshCoins.split
#check @BackendRuntimeRefreshCoins.tableEquiv
#print axioms BackendRuntimeRefreshCoins.split_symm
#print axioms BackendRuntimeRefreshCoins.tableEquiv_apply

end LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeRefreshCoins
