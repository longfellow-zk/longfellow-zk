import Bcs.ProbabilityBounds

/-! Compatibility names for the generic finite-probability bounds.
Their implementation lives in Bcs and has no runtime dependencies. -/
namespace LfzkV2.Current.ProtocolProbability
export Bcs.FiniteProbability
  (event_union_le density_le_one mean_card density_le_mean mean_add_mul_le
   density_add_mean_le density_shared_budget mean_le mean_density_le_one query_bound_or_one)
end LfzkV2.Current.ProtocolProbability
