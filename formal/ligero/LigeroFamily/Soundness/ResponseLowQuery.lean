import LigeroFamily.Soundness.PolicyProfiledMaster
import LigeroFamily.Soundness.Hypergeometric

/-! Query cover below an agreement cutoff, for a fixed response. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LigeroFamily

open Finset
open scoped Classical

/-- A low-agreement response has at most the cutoff's hypergeometric query
cover.  The challenge and response may be arbitrary but are held fixed while
the query is sampled. -/
theorem low_response_query_ratio_le
    {F Equations CheckedMask DirectMask Challenge Response : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    [Fintype CheckedMask] [DecidableEq CheckedMask]
    [Fintype Challenge] [DecidableEq Challenge]
    {logicalWidth r w n nw nq : ℕ}
    (C : MultiplicativeCode F r w n)
    (layout : ConstraintLayout F logicalWidth w)
    (policy : SchemeProtocolPolicy (Equations := Equations) C layout
      Challenge Response CheckedMask DirectMask nw nq 1)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (challenge : Challenge) (response : Response) (cutoff : ℕ)
    (hrn : r ≤ n)
    (hlow : (policyAcceptingCoordinates policy oracle statement
      challenge response).card ≤ cutoff) :
    ((univ.filter fun query : QuerySet n r =>
      policy.accepts statement challenge response query
        (openSchemeOracle oracle query)).card : ℚ) /
      Fintype.card (QuerySet n r) ≤
        hypergeometricRatio cutoff n r := by
  let good := policyAcceptingCoordinates policy oracle statement
    challenge response
  have hsub : (univ.filter fun query : QuerySet n r =>
      policy.accepts statement challenge response query
        (openSchemeOracle oracle query)) ⊆ queriesWithin good := by
    intro query hquery
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      query_subset_policyAcceptingCoordinates_of_accepts policy oracle
        statement challenge response query (Finset.mem_filter.mp hquery).2⟩
  have hcard :
      (univ.filter fun query : QuerySet n r =>
        policy.accepts statement challenge response query
          (openSchemeOracle oracle query)).card ≤ cutoff.choose r :=
    (Finset.card_le_card hsub).trans
      ((card_queriesWithin_le good le_rfl).trans
        (Nat.choose_le_choose r hlow))
  have hden : (0 : ℚ) < n.choose r := by
    exact_mod_cast Nat.choose_pos hrn
  simpa only [QuerySet.fintype_card, hypergeometricRatio] using
    (div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden.le)

end LigeroFamily
