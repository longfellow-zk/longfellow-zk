import LigeroFamily.Soundness.PolicyPotential
import LigeroFamily.Protocol.FiniteResponse

/-!
# A response-uniform extraction-failure potential

The first challenge is exposed before the prover chooses its response.  We
therefore maximize the accepting-coordinate count over *all* responses at
each challenge.  The classifier theorem is uniform over response strategies,
so the maximizing strategy satisfies the same full tail bound.  No response
list-size factor is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace LigeroFamily

open Finset LigeroFamily.AgreementProfile
open scoped Classical

variable {F Equations CheckedMask DirectMask Challenge Response : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable [Fintype CheckedMask] [DecidableEq CheckedMask]
variable [Fintype Challenge] [DecidableEq Challenge] [Nonempty Challenge]
variable [Fintype Response] [Nonempty Response]
variable {logicalWidth r w n nw nq e g profileDenominator failureDenominator : ℕ}
variable {C : MultiplicativeCode F r w n}
variable {layout : ConstraintLayout F logicalWidth w}
variable {policy : SchemeProtocolPolicy (Equations := Equations) C layout
  Challenge Response CheckedMask DirectMask nw nq 1}
variable {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}
variable {statement : ConstraintSystem F nw nq logicalWidth Equations}
variable {failureProfile arithmeticProfile : AgreementProfile n}

/-- Maximum agreement of an accepting response, chosen after the challenge. -/
noncomputable def policyMaxResponseAgreement
    (policy : SchemeProtocolPolicy (Equations := Equations) C layout
      Challenge Response CheckedMask DirectMask nw nq 1)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (challenge : Challenge) : ℕ :=
  (univ : Finset Response).sup fun response =>
    (policyAcceptingCoordinates policy oracle statement challenge response).card

theorem policyMaxResponseAgreement_le (challenge : Challenge) :
    policyMaxResponseAgreement policy oracle statement challenge ≤ n := by
  unfold policyMaxResponseAgreement
  exact Finset.sup_le fun response _ =>
    policyAcceptingCoordinates_card_le policy oracle statement challenge response

private theorem maximizingResponse_exists (challenge : Challenge) :
    ∃ response : Response,
      (policyAcceptingCoordinates policy oracle statement challenge response).card =
        policyMaxResponseAgreement policy oracle statement challenge := by
  classical
  obtain ⟨response, _, h⟩ := Finset.exists_mem_eq_sup (univ : Finset Response)
    Finset.univ_nonempty (fun response =>
      (policyAcceptingCoordinates policy oracle statement challenge response).card)
  exact ⟨response, h.symm⟩

noncomputable def maximizingResponse (challenge : Challenge) : Response :=
  (maximizingResponse_exists (policy := policy) (oracle := oracle)
    (statement := statement) challenge).choose

theorem maximizingResponse_agreement (challenge : Challenge) :
    (policyAcceptingCoordinates policy oracle statement challenge
      (maximizingResponse (policy := policy) (oracle := oracle)
        (statement := statement) challenge)).card =
        policyMaxResponseAgreement policy oracle statement challenge :=
  (maximizingResponse_exists (policy := policy) (oracle := oracle)
    (statement := statement) challenge).choose_spec

/-- The profile tail controls the best response selected after the challenge,
provided the existing classifier is available for every response strategy. -/
theorem maxResponseAgreement_tail_le
    (hclassifier : ∀ respond : Challenge → Response,
      Nonempty (PolicyDoublyProfiledSoundnessClassifier policy oracle statement
        respond failureProfile arithmeticProfile profileDenominator
          failureDenominator e g))
    (hfailure : 0 < failureDenominator)
    (hprofile : 0 < profileDenominator)
    (a : ℕ) (ha : a ≤ n) :
    ((tailSet (policyMaxResponseAgreement policy oracle statement) a).card : ℚ) /
        Fintype.card Challenge ≤
      PolicyDoublyProfiledSoundnessClassifier.gradedTail
        failureProfile arithmeticProfile failureDenominator
          profileDenominator e g a := by
  classical
  let respond := maximizingResponse (policy := policy) (oracle := oracle)
    (statement := statement)
  let classifier := Classical.choice (hclassifier respond)
  have heq : ∀ challenge,
      classifier.responseAgreement challenge =
        policyMaxResponseAgreement policy oracle statement challenge := by
    intro challenge
    exact maximizingResponse_agreement (policy := policy) (oracle := oracle)
      (statement := statement) challenge
  have hfun : classifier.responseAgreement =
      policyMaxResponseAgreement policy oracle statement := funext heq
  rw [← hfun]
  exact classifier.responseAgreement_tail_le_graded a ha hfailure hprofile

theorem maxResponseAgreement_mean_le_graded
    (ψ : PotentialProfile.Curve n)
    (hclassifier : ∀ respond : Challenge → Response,
      Nonempty (PolicyDoublyProfiledSoundnessClassifier policy oracle statement
        respond failureProfile arithmeticProfile profileDenominator
          failureDenominator e g))
    (hfailure : 0 < failureDenominator)
    (hprofile : 0 < profileDenominator) :
    (∑ challenge : Challenge,
        ψ.value (policyMaxResponseAgreement policy oracle statement challenge)) /
          Fintype.card Challenge ≤
      ∑ a ∈ range (n + 1), ψ.increment a *
        PolicyDoublyProfiledSoundnessClassifier.gradedTail
          failureProfile arithmeticProfile failureDenominator
            profileDenominator e g a := by
  apply ψ.mean_le_tail_sum (policyMaxResponseAgreement policy oracle statement)
    (policyMaxResponseAgreement_le (policy := policy) (oracle := oracle)
      (statement := statement))
    (PolicyDoublyProfiledSoundnessClassifier.gradedTail
      failureProfile arithmeticProfile failureDenominator profileDenominator e g)
  intro a ha
  exact maxResponseAgreement_tail_le (policy := policy) (oracle := oracle)
    (statement := statement) hclassifier hfailure hprofile a ha

/-- Every accepted query is contained in its response's accepting-coordinate
set, whose size is at most the response-uniform maximum. -/
theorem acceptingQueries_card_le_maxAgreement (challenge : Challenge)
    (response : Response) :
    (univ.filter fun query : QuerySet n r =>
      policy.accepts statement challenge response query
        (openSchemeOracle oracle query)).card ≤
      (policyMaxResponseAgreement policy oracle statement challenge).choose r := by
  classical
  let allowed := policyAcceptingCoordinates policy oracle statement challenge response
  have hsub : (univ.filter fun query : QuerySet n r =>
      policy.accepts statement challenge response query
        (openSchemeOracle oracle query)) ⊆ queriesWithin allowed := by
    intro query hquery
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      query_subset_policyAcceptingCoordinates_of_accepts policy oracle statement
        challenge response query (Finset.mem_filter.mp hquery).2⟩
  have hsize : allowed.card ≤
      policyMaxResponseAgreement policy oracle statement challenge := by
    exact Finset.le_sup (f := fun response =>
      (policyAcceptingCoordinates policy oracle statement challenge response).card)
      (Finset.mem_univ response)
  exact ((Finset.card_le_card hsub).trans
    (card_queriesWithin_le allowed le_rfl)).trans
      (Nat.choose_le_choose r hsize)

/-- Query-stage success after a fixed response, charged only for the portion
of progress not already assigned to the combination challenge. -/
theorem query_positive_increase_le (ψ : PotentialProfile.Curve n)
    (challenge : Challenge) (response : Response) :
    (1 - ψ.value (policyMaxResponseAgreement policy oracle statement challenge)) *
      (((univ.filter fun query : QuerySet n r =>
        policy.accepts statement challenge response query
          (openSchemeOracle oracle query)).card : ℚ) / n.choose r) ≤
    ψ.queryCost (fun a => hypergeometricRatio a n r) := by
  let a := policyMaxResponseAgreement policy oracle statement challenge
  have ha : a ≤ n := policyMaxResponseAgreement_le (policy := policy)
    (oracle := oracle) (statement := statement) challenge
  have hfirst : ((univ.filter fun query : QuerySet n r =>
      policy.accepts statement challenge response query
        (openSchemeOracle oracle query)).card : ℚ) / n.choose r ≤
      hypergeometricRatio a n r := by
    unfold hypergeometricRatio
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast (acceptingQueries_card_le_maxAgreement
        (policy := policy) (oracle := oracle) (statement := statement)
        challenge response)) (Nat.cast_nonneg _)
  have hnonneg : 0 ≤ 1 - ψ.value a := sub_nonneg.mpr (ψ.le_one a ha)
  have hcharge := mul_le_mul_of_nonneg_left hfirst hnonneg
  have hsup : (1 - ψ.value a) * hypergeometricRatio a n r ≤
      ψ.queryCost (fun a => hypergeometricRatio a n r) := by
    unfold PotentialProfile.Curve.queryCost
    rw [Finset.le_sup'_iff]
    exact ⟨a, Finset.mem_range.mpr (by omega), le_rfl⟩
  exact hcharge.trans hsup

end LigeroFamily
