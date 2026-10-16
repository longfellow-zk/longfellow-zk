import Lfzk.V1StrongV7Mass
import Lfzk.ZkPotentialBalance
import LigeroFamily.Soundness.ResponseLowQuery

/-! One-answer low-agreement budget for the v7 V1 query decoder. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.V1StrongV7LowQuery

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open scoped Classical

/-- A fixed transmitted response below the cutoff has query-decoder cost
at most the checked low-cover term, even if its parent challenge was queried
later. -/
theorem decoded_low_query_le (i : Fin 4)
    {F Equations Coin : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    [Fintype Coin] [Nonempty Coin]
    {w nw nq : ℕ}
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (oracle : Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (challenge : Ligero.V1.Challenge F nw nq 1 Equations)
    (response : Response F (row i).openings w (row i).n 1)
    (decodeQuery : Coin → QuerySet (row i).n (row i).openings)
    (kquery : ℕ)
    (hqueryBalance : ∀ query,
      (univ.filter fun c : Coin => decodeQuery c = query).card ≤ kquery)
    (hkquery : kquery * Fintype.card
      (QuerySet (row i).n (row i).openings) ≤ Fintype.card Coin)
    (hlow : (policyAcceptingCoordinates
      (Ligero.V1.potentialFailedPolicy (Equations := Equations)
        (e := (row i).e) (g := (row i).g)
        ((row i).code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow) oracle)
      oracle statement challenge response).card ≤ cutoff (row i)) :
    (∑ c : Coin,
      if (Ligero.V1.potentialFailedPolicy (Equations := Equations)
        (e := (row i).e) (g := (row i).g)
        ((row i).code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow) oracle).accepts
          statement challenge response (decodeQuery c)
          (openSchemeOracle oracle (decodeQuery c)) then (1 : ℚ) else 0) ≤
      Fintype.card Coin * cover (row i) (cutoff (row i)) := by
  let R := row i
  let C := R.code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow
  let policy := Ligero.V1.potentialFailedPolicy (Equations := Equations)
    (e := R.e) (g := R.g) C oracle
  have hrn : R.openings ≤ R.n := by fin_cases i <;> native_decide
  letI : Nonempty (QuerySet R.n R.openings) := QuerySet.nonempty hrn
  have hformal := low_response_query_ratio_le C
    (ConstraintLayout.identity w) policy oracle statement challenge response
    (cutoff R) hrn hlow
  have hraw := ZkPotentialBalance.decoded_query_charge_le decodeQuery
    (fun query => policy.accepts statement challenge response query
      (openSchemeOracle oracle query)) 1 (by norm_num) kquery
    hqueryBalance (cover R (cutoff R))
    (by simpa only [R, cover, one_mul] using hformal)
  have hcover : 0 ≤ cover R (cutoff R) := by
    unfold cover hypergeometricRatio
    positivity
  have hcount : (kquery : ℚ) * Fintype.card
      (QuerySet R.n R.openings) ≤ Fintype.card Coin := by
    exact_mod_cast hkquery
  have hbound := mul_le_mul_of_nonneg_right hcount hcover
  simpa only [R, C, policy, one_mul, mul_assoc] using hraw.trans hbound

end Lfzk.V1StrongV7LowQuery
