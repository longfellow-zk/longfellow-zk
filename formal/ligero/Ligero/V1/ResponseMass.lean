import Ligero.V1.PotentialExtraction
import LigeroFamily.Soundness.ResponseOverlap

/-!
# Response-mass extraction envelope for scalar Ligero V1

This combines the V1 extraction-failure classifier, the complete-response
overlap theorem, and a radius-dependent uniform-family packing bound. It is
an IOP statement about all responses at each challenge. An adaptive FS
compiler needs an additional grouped-revelation theorem to use this mass as
its challenge-stage charge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Ligero.V1

open Finset LigeroFamily LigeroFamily.ResponseMass CodingTheory
open scoped Classical

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq e g d outerBound threshold cutoff : ℕ}
variable {localBound bound packing : ℕ → ℕ}

/-- Average potential mass of *all* V1 extraction-failing responses. The
maximizing-response tail is response-uniform; the packing premise limits how
many distinct complete responses may occupy each high-agreement level. -/
theorem scalarGap_response_mass_le
    (C : MultiplicativeCode F r w n)
    (oracle : Oracle F nw nq n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    {L : ℕ}
    (hcard : (univ : Finset (SchemeLiftCandidate C oracle (e + g))).card ≤ L)
    (hrows : CoreRowsNonempty nw nq)
    (mask : V1MaskRange C threshold bound)
    (hk : 0 < C.k)
    (ψ : PotentialProfile.Curve n)
    (hlambda : 2 * C.k - 1 ≤ cutoff)
    (hpacking : ∀ a, cutoff < a → a ≤ n →
      UniformFamilyBound n a (2 * C.k - 1) (packing a)) :
    let policy := potentialFailedPolicy (e := e) (g := g) C oracle
    (∑ challenge : Challenge F nw nq 1 Equations,
      ∑ response : Response F r w n 1,
        ψ.value (policyAcceptingCoordinates policy oracle statement
          challenge response).card) /
        Fintype.card (Challenge F nw nq 1 Equations) ≤
      ∑ a ∈ range (n + 1), ψ.increment a *
        (if a ≤ cutoff then Fintype.card (Response F r w n 1)
          else packing a : ℕ) *
        PolicyDoublyProfiledSoundnessClassifier.gradedTail
          (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
            (Fintype.card F) n e g d outerBound localBound)
          (maskAgreementProfile (Fintype.card F) n L threshold bound)
          (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
            (Fintype.card F) g)
          (Fintype.card F) e g a := by
  classical
  let policy : SchemeProtocolPolicy (Equations := Equations) C
      (ConstraintLayout.identity w)
      (Challenge F nw nq 1 Equations) (Response F r w n 1)
      NoMask Mask nw nq 1 :=
    potentialFailedPolicy (e := e) (g := g) C oracle
  let good := policyAcceptingCoordinates policy oracle statement
  let maximum := policyMaxResponseAgreement policy oracle statement
  letI : Nonempty (Response F r w n 1) :=
    ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩⟩
  have hmax (challenge : Challenge F nw nq 1 Equations)
      (response : Response F r w n 1) :
      (good challenge response).card ≤ maximum challenge := by
    exact Finset.le_sup (f := fun response => (good challenge response).card)
      (Finset.mem_univ response)
  have hoverlap (challenge : Challenge F nw nq 1 Equations)
      (first second : Response F r w n 1) (hne : first ≠ second) :
      ((good challenge first) ∩ (good challenge second)).card ≤
        2 * C.k - 1 := by
    apply complete_response_overlap C scheme oracle statement challenge
      first second (good challenge first) (good challenge second)
    · intro j hj
      obtain ⟨query, haccept, hmem⟩ :=
        (Finset.mem_filter.mp hj).2
      exact ⟨query, haccept.1, hmem⟩
    · intro j hj
      obtain ⟨query, haccept, hmem⟩ :=
        (Finset.mem_filter.mp hj).2
      exact ⟨query, haccept.1, hmem⟩
    · exact hk
    · exact hne
  have hden : 0 < SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
      (Fintype.card F) g := by
    dsimp [SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator]
    exact Nat.mul_pos Fintype.card_pos
      (Nat.sub_pos_of_lt conditions.outer.punctured.field_large)
  have htail (a : ℕ) (ha : a ≤ n) :
      ((AgreementProfile.tailSet maximum a).card : ℚ) /
        Fintype.card (Challenge F nw nq 1 Equations) ≤
      PolicyDoublyProfiledSoundnessClassifier.gradedTail
        (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
          (Fintype.card F) n e g d outerBound localBound)
        (maskAgreementProfile (Fintype.card F) n L threshold bound)
        (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
          (Fintype.card F) g)
        (Fintype.card F) e g a := by
    exact maxResponseAgreement_tail_le (policy := policy) (oracle := oracle)
      (statement := statement)
      (fun respond => scalarGap_profiled_classifier_of_card C oracle statement
        hmin conditions hcard hrows mask respond)
      hden Fintype.card_pos a ha
  exact ResponseMass.mean_curve_le_of_overlap good maximum hmax
    hoverlap ψ packing _ hlambda hpacking htail

end Ligero.V1
