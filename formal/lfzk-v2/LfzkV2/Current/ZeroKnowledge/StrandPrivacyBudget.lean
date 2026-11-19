import LfzkV2.Current.Messages
import LfzkV2.Current.ZeroKnowledge.ProbabilityInstances

/-! Concrete nonce entropy for the indexed-leaf privacy bound. Arithmetic
stays symbolic in the powers of two, avoiding exhaustive oracle tables or
large exponent normalization in the protocol theorem. -/
namespace LfzkV2.Current.ZeroKnowledge.StrandPrivacyBudget

theorem at_query_budget (prior later : ℕ) (budget : prior+later ≤ 2^128) :
    ((prior+later : ℕ) : ℚ) / (Fintype.card MerkleNonce : ℚ) ≤ 1/(2:ℚ)^128 := by
  have entropy : (Fintype.card MerkleNonce : ℚ) = (2:ℚ)^128*(2:ℚ)^128 := by
    rw [Fintype.card_fun,Fintype.card_fin,Fintype.card_fin,Nat.cast_pow]
    change (256:ℚ)^merkleNonceBytes = (2:ℚ)^128*(2:ℚ)^128
    rw [show (256:ℚ) = (2:ℚ)^8 by norm_num,← pow_mul,← pow_add]
    rfl
  rw [entropy,div_mul_eq_div_div]
  apply div_le_div_of_nonneg_right _ (le_of_lt (pow_pos (by norm_num : (0:ℚ) < 2) _))
  apply (div_le_one (pow_pos (by norm_num : (0:ℚ) < 2) _)).mpr
  exact_mod_cast budget

end LfzkV2.Current.ZeroKnowledge.StrandPrivacyBudget
