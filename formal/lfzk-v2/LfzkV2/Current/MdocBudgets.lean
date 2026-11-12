import LfzkV2.Current.AdapterParameters

/-! Rounding the global per-query bound and collecting digest-sized
remainders. Actual role-local budgets and their maximum are proved in
`ApplicationCharging` and `GlobalCharges`; this module contains only the
arithmetic shared by their final Fiat--Shamir composition. -/
namespace LfzkV2.Current
open Adapter.Mdoc

private theorem rounded_query_budget (d q : ℚ) (Q : ℕ) (h : d ≤ 2/q+3/q^2) :
    (Q : ℚ)*d+(Q+1 : ℚ)/q^2 ≤ 2*Q/q+(4*Q+1 : ℚ)/q^2 := by
  have hQ : (Q : ℚ)*d ≤ (Q : ℚ)*(2/q+3/q^2) :=
    mul_le_mul_of_nonneg_left h (show (0 : ℚ) ≤ Q from Nat.cast_nonneg Q)
  linear_combination hQ

/-- Rounding the nonzero-sampling correction and adding one 256-bit chain
exception gives the desired leading term. Merkle explanation is additional. -/
theorem mdoc_chained_budget (Q : ℕ) :
    (Q : ℚ)*(2/((binaryOrder-1 : ℕ) : ℚ)) + (Q+1 : ℚ)/(binaryOrder : ℚ)^2 ≤
      2*Q/(binaryOrder : ℚ) + (4*Q+1 : ℚ)/(binaryOrder : ℚ)^2 := by
  apply rounded_query_budget
  simp only [binaryOrder]
  decide +kernel

end LfzkV2.Current
