import LigeroFamily.Soundness.PolicyProfiledMaster
import LigeroFamily.Soundness.Hypergeometric

/-!
# Query cover above a response-agreement cutoff

The same accepting-coordinate set that defines response agreement contains
every accepted query.  Thus the conditional high-agreement query mass is
bounded by the exact hypergeometric cover at that response's agreement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LigeroFamily

open Finset
open scoped Classical

theorem high_response_query_ratio_le
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
    (hrn : r ≤ n) :
    let good := policyAcceptingCoordinates policy oracle statement
      challenge response
    ((univ.filter fun query : QuerySet n r =>
      cutoff < good.card ∧ policy.accepts statement challenge response query
        (openSchemeOracle oracle query)).card : ℚ) /
      Fintype.card (QuerySet n r) ≤
        if cutoff < good.card then
          hypergeometricRatio good.card n r else 0 := by
  classical
  let good := policyAcceptingCoordinates policy oracle statement challenge response
  change ((univ.filter fun query : QuerySet n r =>
      cutoff < good.card ∧ policy.accepts statement challenge response query
        (openSchemeOracle oracle query)).card : ℚ) /
      Fintype.card (QuerySet n r) ≤
        if cutoff < good.card then
          hypergeometricRatio good.card n r else 0
  have hden : (0 : ℚ) < n.choose r := by
    exact_mod_cast Nat.choose_pos hrn
  by_cases hhigh : cutoff < good.card
  · have hsub : (univ.filter fun query : QuerySet n r =>
        cutoff < good.card ∧ policy.accepts statement challenge response query
          (openSchemeOracle oracle query)) ⊆ queriesWithin good := by
      intro query hquery
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        query_subset_policyAcceptingCoordinates_of_accepts
          policy oracle statement challenge response query
          (Finset.mem_filter.mp hquery).2.2⟩
    have hcard : (univ.filter fun query : QuerySet n r =>
        cutoff < good.card ∧ policy.accepts statement challenge response query
          (openSchemeOracle oracle query)).card ≤ good.card.choose r :=
      (Finset.card_le_card hsub).trans (card_queriesWithin_le good le_rfl)
    have hcardQ :
        ((univ.filter fun query : QuerySet n r =>
          cutoff < good.card ∧ policy.accepts statement challenge response query
            (openSchemeOracle oracle query)).card : ℚ) ≤
          (good.card.choose r : ℕ) := by exact_mod_cast hcard
    simpa only [QuerySet.fintype_card, if_pos hhigh,
      hypergeometricRatio] using
      (div_le_div_of_nonneg_right hcardQ hden.le)
  · have hempty : (univ.filter fun query : QuerySet n r =>
        cutoff < good.card ∧ policy.accepts statement challenge response query
          (openSchemeOracle oracle query)) = ∅ := by
      ext query
      simp [hhigh]
    rw [hempty]
    simp [hhigh]

end LigeroFamily
