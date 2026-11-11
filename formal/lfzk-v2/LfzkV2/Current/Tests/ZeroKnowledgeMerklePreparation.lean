import LfzkV2.Current.ZeroKnowledge.MerklePreparation

/-! The preparation bound includes adaptively chosen prior requests and
arbitrary later oracle postprocessing. The background oracle is a coupling
coin, not a component appended to the observer's public view. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMerklePreparation

open ZeroKnowledge.MerklePreparation

example : error (2^256) (2^256) 2443 0 =
    23865668/(2:ℚ)^256 := by
  simpa only [Nat.cast_zero,mul_zero,add_zero,zero_div] using rate7_error 0

#print axioms numerator_ratio_le
#print axioms prior_card
#print axioms disagreement_card
#print axioms fixed_statClose
#print axioms refreshEquiv
#print axioms preparation_statClose
#print axioms rate7_error

end LfzkV2.Current.Tests.ZeroKnowledgeMerklePreparation
