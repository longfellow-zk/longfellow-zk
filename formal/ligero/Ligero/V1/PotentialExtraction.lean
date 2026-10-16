import Ligero.V1.ScalarGapProfiled
import LigeroFamily.Soundness.PolicyPotentialUniform
import LigeroFamily.Soundness.PotentialPairs

/-!
# Extraction-first graded potential for Ligero V1

The charged event is acceptance with the existing response-assisted extractor
returning `none`.  The arithmetic and proximity classifiers are the same as
those used in the IOP extraction theorem.  The new interface retains their
entire agreement tail for an adaptive Fiat–Shamir challenge/query analysis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace Ligero.V1

open LigeroFamily CodingTheory MultiplicativeCode Finset SchemeLiftCandidate
open scoped Classical

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq e g d outerBound threshold : ℕ} {localBound bound : ℕ → ℕ}
variable (C : MultiplicativeCode F r w n) (oracle : Oracle F nw nq n 1)
variable (statement : ConstraintSystem F nw nq w Equations)

local notation "gapPolicy" => SchemeVerifier.policy (Equations := Equations)
  (nw := nw) (nq := nq) (repetitions := 1) C scheme
noncomputable def potentialFailedPolicy :
    SchemeProtocolPolicy (Equations := Equations) C (ConstraintLayout.identity w)
      (Challenge F nw nq 1 Equations) (Response F r w n 1) NoMask Mask nw nq 1 :=
  ScalarGapExtraction.failingPolicy (oracle := oracle) (e := e) (g := g)
    gapPolicy (fun candidate => candidate.decodedMessages)
local notation "proximityProfile" =>
  SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
    (Fintype.card F) n e g d outerBound localBound
local notation "proximityDenominator" =>
  SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator (Fintype.card F) g

/-- Expose the classifier already implicit in the V1 IOP extraction proof.
This is uniform over the response strategy, including a strategy selecting a
maximizer separately at each combination challenge. -/
theorem scalarGap_profiled_classifier_of_card
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound) {L : ℕ}
    (hcard : (univ : Finset (SchemeLiftCandidate C oracle (e + g))).card ≤ L)
    (hrows : CoreRowsNonempty nw nq)
    (mask : V1MaskRange C threshold bound)
    (respond : Challenge F nw nq 1 Equations → Response F r w n 1) :
    Nonempty (PolicyDoublyProfiledSoundnessClassifier
      (potentialFailedPolicy (e := e) (g := g) C oracle) oracle statement
      respond proximityProfile
      (maskAgreementProfile (Fintype.card F) n L threshold bound)
      (Fintype.card F) proximityDenominator e g) := by
  classical
  letI : Nonempty (SchemeTestedRow NoMask nw nq 1) :=
    schemeTestedRowNonemptyOfCoreRows hrows
  obtain ⟨certificate, hdensity⟩ :=
    (ScalarGapExtraction.failingExtractor gapPolicy
      (fun (candidate : SchemeLiftCandidate C oracle (e + g)) =>
        candidate.decodedMessages)
      (schemeExtractorPolicy (Equations := Equations) (nw := nw)
        (nq := nq) C scheme)).exists_profiledPolicyLiftList_of_endpointOptimizedIntegratedLine_of_card
        (oracle := oracle) (respond := respond) hmin conditions hcard
  obtain ⟨arithmetic⟩ := scalarGap_profiled_arithmetic_certificate
    C oracle statement hmin conditions mask respond certificate
  exact arithmetic.doublyProfiledClassifier_nonempty certificate hdensity

/-- Challenge-stage positive-increase cost for every rational monotone
potential, with no selected challenge/query threshold. -/
theorem scalarGap_challenge_potential_le
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound) {L : ℕ}
    (hcard : (univ : Finset (SchemeLiftCandidate C oracle (e + g))).card ≤ L)
    (hrows : CoreRowsNonempty nw nq)
    (mask : V1MaskRange C threshold bound)
    (ψ : PotentialProfile.Curve n) :
    (∑ challenge : Challenge F nw nq 1 Equations,
      ψ.value (policyMaxResponseAgreement
        (potentialFailedPolicy (e := e) (g := g) C oracle) oracle statement challenge)) /
        Fintype.card (Challenge F nw nq 1 Equations) ≤
      ∑ a ∈ range (n + 1), ψ.increment a *
        PolicyDoublyProfiledSoundnessClassifier.gradedTail proximityProfile
          (maskAgreementProfile (Fintype.card F) n L threshold bound)
          proximityDenominator (Fintype.card F) e g a := by
  have hden : 0 < proximityDenominator := by
    dsimp [SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator]
    exact Nat.mul_pos Fintype.card_pos
      (Nat.sub_pos_of_lt conditions.outer.punctured.field_large)
  letI : Nonempty (Response F r w n 1) :=
    ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩⟩
  exact maxResponseAgreement_mean_le_graded
    (policy := potentialFailedPolicy (e := e) (g := g) C oracle)
    (oracle := oracle) (statement := statement)
    ψ (fun respond => scalarGap_profiled_classifier_of_card C oracle statement
      hmin conditions hcard hrows mask respond) hden Fintype.card_pos

/-- The second fresh hash answer is the column query.  Its charge is the
unassigned part of extraction-failure acceptance, uniformly over the
response selected after the combination challenge. -/
theorem scalarGap_query_potential_le
    (ψ : PotentialProfile.Curve n)
    (challenge : Challenge F nw nq 1 Equations)
    (response : Response F r w n 1) :
    let X := policyMaxResponseAgreement
      (potentialFailedPolicy (e := e) (g := g) C oracle) oracle statement challenge
    (1 - ψ.value X) *
      (((univ.filter fun query : QuerySet n r =>
        (gapPolicy).accepts statement challenge response query
          (openSchemeOracle oracle query) ∧
        ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g)
          gapPolicy (fun candidate => candidate.decodedMessages)
            statement challenge response = none).card : ℚ) / n.choose r) ≤
      ψ.queryCost (fun a => hypergeometricRatio a n r) := by
  letI : Nonempty (Response F r w n 1) :=
    ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩⟩
  simpa only [potentialFailedPolicy, ScalarGapExtraction.failingPolicy] using
    (query_positive_increase_le
      (policy := potentialFailedPolicy (e := e) (g := g) C oracle)
      (oracle := oracle) (statement := statement) ψ challenge response)

/-- Full graded IOP extraction-failure bound for V1.  The response can be
selected after seeing the combination challenge.  The event includes the
actual response-assisted decoder returning `none`, so soundness follows by
the existing extraction-validity theorem. -/
theorem scalarGap_profiled_potential_extraction_failure_le
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound) {L : ℕ}
    (hcard : (univ : Finset (SchemeLiftCandidate C oracle (e + g))).card ≤ L)
    (hrows : CoreRowsNonempty nw nq)
    (mask : V1MaskRange C threshold bound)
    (ψ : PotentialProfile.Curve n)
    (respond : Challenge F nw nq 1 Equations → Response F r w n 1) :
    ((univ.filter fun p : Challenge F nw nq 1 Equations × QuerySet n r =>
      (gapPolicy).accepts statement p.1 (respond p.1) p.2
        (openSchemeOracle oracle p.2) ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g)
        gapPolicy (fun candidate => candidate.decodedMessages)
          statement p.1 (respond p.1) = none).card : ℚ) /
      (Fintype.card (Challenge F nw nq 1 Equations) *
        Fintype.card (QuerySet n r)) ≤
      (∑ a ∈ range (n + 1), ψ.increment a *
        PolicyDoublyProfiledSoundnessClassifier.gradedTail proximityProfile
          (maskAgreementProfile (Fintype.card F) n L threshold bound)
          proximityDenominator (Fintype.card F) e g a) +
      ψ.queryCost (fun a => hypergeometricRatio a n r) := by
  letI : Nonempty (Response F r w n 1) :=
    ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩⟩
  letI : Nonempty (QuerySet n r) := QuerySet.nonempty C.query_le_length
  let X := policyMaxResponseAgreement
    (potentialFailedPolicy (e := e) (g := g) C oracle) oracle statement
  have hX : ∀ c, X c ≤ n := by
    intro c
    exact policyMaxResponseAgreement_le (policy := potentialFailedPolicy
      (e := e) (g := g) C oracle) (oracle := oracle) (statement := statement) c
  apply PotentialProfile.pair_ratio_le ψ X hX
    (fun c q => (gapPolicy).accepts statement c (respond c) q
      (openSchemeOracle oracle q) ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g)
        gapPolicy (fun candidate => candidate.decodedMessages)
          statement c (respond c) = none)
  · exact scalarGap_challenge_potential_le C oracle statement hmin conditions hcard
      hrows mask ψ
  · intro c
    simpa only [X, QuerySet.fintype_card] using
      (scalarGap_query_potential_le (e := e) (g := g) C oracle statement
        ψ c (respond c))

/-- At a built system with no satisfying decoded lift, the extraction-first
event is exactly verifier acceptance.  This is the boundary statement used
when Ligero follows sumcheck. -/
theorem scalarGap_profiled_potential_acceptance_of_noDecoded
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound) {L : ℕ}
    (hcard : (univ : Finset (SchemeLiftCandidate C oracle (e + g))).card ≤ L)
    (hrows : CoreRowsNonempty nw nq)
    (mask : V1MaskRange C threshold bound)
    (ψ : PotentialProfile.Curve n)
    (respond : Challenge F nw nq 1 Equations → Response F r w n 1)
    (hnd : NoDecodedSolution C oracle (e + g) statement) :
    ((univ.filter fun p : Challenge F nw nq 1 Equations × QuerySet n r =>
      (gapPolicy).accepts statement p.1 (respond p.1) p.2
        (openSchemeOracle oracle p.2)).card : ℚ) /
      (Fintype.card (Challenge F nw nq 1 Equations) *
        Fintype.card (QuerySet n r)) ≤
      (∑ a ∈ range (n + 1), ψ.increment a *
        PolicyDoublyProfiledSoundnessClassifier.gradedTail proximityProfile
          (maskAgreementProfile (Fintype.card F) n L threshold bound)
          proximityDenominator (Fintype.card F) e g a) +
      ψ.queryCost (fun a => hypergeometricRatio a n r) := by
  classical
  have heq : (univ.filter fun p : Challenge F nw nq 1 Equations × QuerySet n r =>
      (gapPolicy).accepts statement p.1 (respond p.1) p.2
        (openSchemeOracle oracle p.2)) =
      (univ.filter fun p : Challenge F nw nq 1 Equations × QuerySet n r =>
      (gapPolicy).accepts statement p.1 (respond p.1) p.2
        (openSchemeOracle oracle p.2) ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g)
        gapPolicy (fun candidate => candidate.decodedMessages)
          statement p.1 (respond p.1) = none) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [ScalarGapExtraction.extract_none_of_no_valid gapPolicy
      (fun candidate => candidate.decodedMessages) statement p.1 (respond p.1) hnd]
  rw [heq]
  exact scalarGap_profiled_potential_extraction_failure_le C oracle statement
    hmin conditions hcard hrows mask ψ respond

/-- The query-stage residual charge at a built system where every decoded
candidate fails.  This is the local form needed by a prefix-only hash point
whose message fixes the response after the combination challenge. -/
theorem scalarGap_query_potential_le_of_noDecoded
    (ψ : PotentialProfile.Curve n)
    (challenge : Challenge F nw nq 1 Equations)
    (response : Response F r w n 1)
    (hnd : NoDecodedSolution C oracle (e + g) statement) :
    let X := policyMaxResponseAgreement
      (potentialFailedPolicy (e := e) (g := g) C oracle) oracle statement challenge
    (1 - ψ.value X) *
      (((univ.filter fun query : QuerySet n r =>
        (gapPolicy).accepts statement challenge response query
          (openSchemeOracle oracle query)).card : ℚ) / n.choose r) ≤
      ψ.queryCost (fun a => hypergeometricRatio a n r) := by
  classical
  have heq : (univ.filter fun query : QuerySet n r =>
      (gapPolicy).accepts statement challenge response query
        (openSchemeOracle oracle query)) =
      (univ.filter fun query : QuerySet n r =>
      (gapPolicy).accepts statement challenge response query
        (openSchemeOracle oracle query) ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g)
        gapPolicy (fun candidate => candidate.decodedMessages)
          statement challenge response = none) := by
    ext query
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [ScalarGapExtraction.extract_none_of_no_valid gapPolicy
      (fun candidate => candidate.decodedMessages) statement challenge response hnd]
  rw [heq]
  exact scalarGap_query_potential_le (e := e) (g := g)
    C oracle statement ψ challenge response

end Ligero.V1
