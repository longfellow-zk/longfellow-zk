import Lfzk.LigeroPayloadOverlap
import Ligero.V1.ResponseMass

/-!
# Response mass over transmitted Ligero V1 payloads

This is the payload-restricted version of the V1 response-mass argument.
Its agreement tail still comes from the response-uniform extraction
classifier, while its packing premise uses the sharper payload overlap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.V1PayloadResponseMass

open Finset LigeroFamily LigeroFamily.ResponseMass CodingTheory
open scoped Classical

variable {F : Type} {Equations : Type*} [Field F] [Fintype F]
variable [DecidableEq F] [Fintype Equations]
variable {r w n nw nq block dblock cutoff : ℕ}

/-- The payload family may be packed with overlap `dblock-1`, provided the
response-uniform agreement tail and the corresponding family-packing bound
are supplied.  In the deployed V1 layout `dblock = 2*k-1`. -/
theorem mean_payload_curve_le
    (D : ReedSolomon.Domain F r w n)
    (baseNodes : Fin block ↪ Position r w n)
    (responseNodes : Fin dblock ↪ Position r w n)
    (hrb : r ≤ block) (hbd : block ≤ dblock)
    (C : MultiplicativeCode F r w n)
    (oracle : Ligero.V1.Oracle F nw nq n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (e g : ℕ)
    (ψ : PotentialProfile.Curve n)
    (packing : ℕ → ℕ) (tail : ℕ → ℚ)
    (hlambda : dblock - 1 ≤ cutoff)
    (hpacking : ∀ a, cutoff < a → a ≤ n →
      CodingTheory.UniformFamilyBound n a (dblock - 1) (packing a))
    (htail : ∀ a ≤ n,
      ((AgreementProfile.tailSet
        (policyMaxResponseAgreement
          (Ligero.V1.potentialFailedPolicy (e := e) (g := g) C oracle)
          oracle statement) a).card : ℚ) /
          Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤ tail a) :
    let policy := Ligero.V1.potentialFailedPolicy
      (e := e) (g := g) C oracle
    let decode := Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes hrb hbd
    (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
      ∑ payload : Lfzk.LigeroTranscriptInputs.ResponsePayload F block dblock r,
        ψ.value (policyAcceptingCoordinates policy oracle statement
          challenge (decode payload)).card) /
        Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤
      ∑ a ∈ range (n + 1), ψ.increment a *
        (if a ≤ cutoff then
          Fintype.card (Lfzk.LigeroTranscriptInputs.ResponsePayload
            F block dblock r) else packing a : ℕ) * tail a := by
  classical
  let policy := Ligero.V1.potentialFailedPolicy (Equations := Equations)
    (e := e) (g := g) C oracle
  let decode := Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes hrb hbd
  let good (challenge : Ligero.V1.Challenge F nw nq 1 Equations)
      (payload : Lfzk.LigeroTranscriptInputs.ResponsePayload F block dblock r) :=
    policyAcceptingCoordinates policy oracle statement challenge (decode payload)
  let maximum := policyMaxResponseAgreement policy oracle statement
  have hmax (challenge : Ligero.V1.Challenge F nw nq 1 Equations)
      (payload : Lfzk.LigeroTranscriptInputs.ResponsePayload F block dblock r) :
      (good challenge payload).card ≤ maximum challenge := by
    exact Finset.le_sup (f := fun response : Response F r w n 1 =>
      (policyAcceptingCoordinates policy oracle statement challenge response).card)
      (Finset.mem_univ (decode payload))
  have hoverlap (challenge : Ligero.V1.Challenge F nw nq 1 Equations)
      (first second : Lfzk.LigeroTranscriptInputs.ResponsePayload F block dblock r)
      (hne : first ≠ second) :
      ((good challenge first) ∩ (good challenge second)).card ≤ dblock - 1 := by
    apply Lfzk.LigeroPayloadOverlap.complete_payload_overlap D baseNodes
      responseNodes hrb hbd C Ligero.V1.scheme oracle statement challenge
      first second (good challenge first) (good challenge second)
    · intro j hj
      obtain ⟨query, haccept, hmem⟩ := (Finset.mem_filter.mp hj).2
      exact ⟨query, haccept.1, hmem⟩
    · intro j hj
      obtain ⟨query, haccept, hmem⟩ := (Finset.mem_filter.mp hj).2
      exact ⟨query, haccept.1, hmem⟩
    · exact hne
  exact ResponseMass.mean_curve_le_of_overlap good maximum hmax hoverlap
    ψ packing tail hlambda hpacking htail

/-- The V1 extraction classifier supplies the tail premise for the sharper
payload-family packing theorem.  This keeps the unchecked-mask and decoder
allowances exactly as in the existing extraction-first IOP analysis. -/
theorem scalarGap_payload_response_mass_le
    {d outerBound threshold : ℕ} {localBound bound : ℕ → ℕ}
    (D : ReedSolomon.Domain F r w n)
    (baseNodes : Fin block ↪ Position r w n)
    (responseNodes : Fin dblock ↪ Position r w n)
    (hrb : r ≤ block) (hbd : block ≤ dblock)
    (C : MultiplicativeCode F r w n)
    (oracle : Ligero.V1.Oracle F nw nq n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (e g : ℕ)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    {L : ℕ}
    (hcard : (univ : Finset (SchemeLiftCandidate C oracle (e + g))).card ≤ L)
    (hrows : CoreRowsNonempty nw nq)
    (mask : Ligero.V1.V1MaskRange C threshold bound)
    (ψ : PotentialProfile.Curve n)
    (packing : ℕ → ℕ)
    (hlambda : dblock - 1 ≤ cutoff)
    (hpacking : ∀ a, cutoff < a → a ≤ n →
      CodingTheory.UniformFamilyBound n a (dblock - 1) (packing a)) :
    let policy := Ligero.V1.potentialFailedPolicy
      (e := e) (g := g) C oracle
    let decode := Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes hrb hbd
    (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
      ∑ payload : Lfzk.LigeroTranscriptInputs.ResponsePayload F block dblock r,
        ψ.value (policyAcceptingCoordinates policy oracle statement
          challenge (decode payload)).card) /
        Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤
      ∑ a ∈ range (n + 1), ψ.increment a *
        (if a ≤ cutoff then
          Fintype.card (Lfzk.LigeroTranscriptInputs.ResponsePayload
            F block dblock r) else packing a : ℕ) *
        PolicyDoublyProfiledSoundnessClassifier.gradedTail
          (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
            (Fintype.card F) n e g d outerBound localBound)
          (maskAgreementProfile (Fintype.card F) n L threshold bound)
          (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
            (Fintype.card F) g)
          (Fintype.card F) e g a := by
  classical
  have hden : 0 < SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
      (Fintype.card F) g := by
    dsimp [SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator]
    exact Nat.mul_pos Fintype.card_pos
      (Nat.sub_pos_of_lt conditions.outer.punctured.field_large)
  letI : Nonempty (Response F r w n 1) :=
    ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩⟩
  have htail (a : ℕ) (ha : a ≤ n) :
      ((AgreementProfile.tailSet
        (policyMaxResponseAgreement
          (Ligero.V1.potentialFailedPolicy (Equations := Equations)
            (e := e) (g := g) C oracle)
          oracle statement) a).card : ℚ) /
          Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤
        PolicyDoublyProfiledSoundnessClassifier.gradedTail
          (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
            (Fintype.card F) n e g d outerBound localBound)
          (maskAgreementProfile (Fintype.card F) n L threshold bound)
          (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
            (Fintype.card F) g)
          (Fintype.card F) e g a := by
    exact maxResponseAgreement_tail_le
      (policy := Ligero.V1.potentialFailedPolicy (Equations := Equations)
        (e := e) (g := g) C oracle)
      (oracle := oracle) (statement := statement)
      (fun respond => Ligero.V1.scalarGap_profiled_classifier_of_card
        C oracle statement hmin conditions hcard hrows mask respond)
      hden Fintype.card_pos a ha
  exact mean_payload_curve_le D baseNodes responseNodes hrb hbd C oracle
    statement e g ψ packing _ hlambda hpacking htail

end Lfzk.V1PayloadResponseMass
