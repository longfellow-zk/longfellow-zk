import LfzkV2.Current.Soundness.Rate7
import LfzkV2.Current.Parameters.Rate7
import LfzkV2.Current.StrandRecovery

/-! Attach the exact numerical certificates to the actual runtime profile
and its existing hash correction, rather than a duplicate free parameter. -/
namespace Survival.RuntimeRate7
open LfzkV2.Current
local notation "profile" => FixedRate.Rate7.certificate

theorem parent_budget :
    ParameterBounds.parentBudget (profile).n (profile).k (profile).s (profile).t
      (profile).activeCutoff (profile).activeList ≤
        Rate7.polygeroFraction * (2/((Adapter.Mdoc.binaryOrder-1 : ℕ) : ℚ)) := by
  change Rate7.parentBudget ≤ Rate7.polygeroFraction*Rate7.rate
  exact Rate7.polygeroFraction_mul_rate.ge

theorem range (queries : ℕ) (bounded : queries < 2^127) : queries < Rate7.q/2 := by
  norm_num [Rate7.q, Adapter.Mdoc.binaryOrder]
  exact bounded

theorem query_budget (queries : ℕ) (bounded : queries < 2^127) :
    (2/((Adapter.Mdoc.binaryOrder-1 : ℕ) : ℚ))*queries ≤ 1 :=
  Rate7.query_budget queries (range queries bounded)

theorem auxiliary_budget (queries : ℕ) (bounded : queries < 2^127) :
    (2*queries : ℚ)/2^256 ≤ Rate7.polygeroFraction*(2/((Adapter.Mdoc.binaryOrder-1 : ℕ) : ℚ)) := by
  have bound := Rate7.auxiliary_exact_budget queries (range queries bounded)
  norm_num [Rate7.q, Rate7.rate, Adapter.Mdoc.binaryOrder] at bound ⊢
  exact bound

theorem correction_eq (queries rounds : ℕ) :
    StrandRecovery.hashCorrection queries rounds (profile).n = Rate7.correction queries rounds := by
  have depth : Heap.heapDepth (profile).n = 12 := by decide +kernel
  unfold StrandRecovery.hashCorrection Rate7.correction
  rw [depth, Nat.choose_two_right]
  norm_num [Rate7.q, Adapter.Mdoc.binaryOrder]
  ring

end Survival.RuntimeRate7
