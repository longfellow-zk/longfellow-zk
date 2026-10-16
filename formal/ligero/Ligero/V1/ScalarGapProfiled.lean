import LigeroFamily.Soundness.ScalarGapProfiled
import Ligero.V1.ScalarGapExtraction

/-! Profiled extraction with the original unchecked arithmetic masks. -/
namespace Ligero.V1
open LigeroFamily CodingTheory MultiplicativeCode Finset SchemeLiftCandidate
open scoped Classical
set_option linter.unusedSectionVars false
variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq e g d outerBound threshold : ℕ} {localBound bound : ℕ → ℕ}
variable (C : MultiplicativeCode F r w n) (oracle : Oracle F nw nq n 1)
variable (statement : ConstraintSystem F nw nq w Equations)
local notation "gapPolicy" => SchemeVerifier.policy (Equations := Equations)
  (nw := nw) (nq := nq) (repetitions := 1) C scheme

/-- V1's unchecked-mask arithmetic certificate, shared by the IOP
extraction theorem and the challenge/query potential. -/
theorem scalarGap_profiled_arithmetic_certificate
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound) {L : ℕ}
    (mask : V1MaskRange C threshold bound)
    (respond : Challenge F nw nq 1 Equations → Response F r w n 1)
    (certificate : PolicyLiftListCertificate
      (ScalarGapExtraction.failingPolicy (oracle := oracle) (e := e) (g := g)
        gapPolicy (fun (candidate : SchemeLiftCandidate C oracle (e + g)) =>
          candidate.decodedMessages)) oracle respond
        e g (e + g) L) :
    Nonempty (PolicyArithmeticCertificate
      (ScalarGapExtraction.failingPolicy (oracle := oracle) (e := e) (g := g)
        gapPolicy (fun (candidate : SchemeLiftCandidate C oracle (e + g)) =>
          candidate.decodedMessages)) oracle statement respond
        certificate (maskAgreementProfile (Fintype.card F) n L threshold bound)
        (Fintype.card F)) := by
  classical
  let violation := fun (candidate : SchemeLiftCandidate C oracle (e + g))
      (h : ¬statement.Satisfies candidate.decodedMessages) =>
    Classical.choice (V1Violation.nonempty_of_false candidate h)
  let agreement := fun (candidate : SchemeLiftCandidate C oracle (e + g)) challenge =>
    if h : ¬statement.Satisfies candidate.decodedMessages then
      v1Agreement candidate (violation candidate h) respond challenge else 0
  refine ScalarGapExtraction.profiledArithmeticCertificate gapPolicy
    (fun candidate => candidate.decodedMessages) certificate hmin
    (by have := conditions.outer.punctured.punctured_three_radius; omega)
    (threshold - 1) bound
    (maskAgreementProfile (Fintype.card F) n L threshold bound)
    ?_ ?_ agreement ?_ ?_ ?_
  · intro a ha hbelow
    simp [maskAgreementProfile, show ¬n < a by omega, show a < threshold by
      have := mask.threshold_pos; omega]
  · intro a ha habove
    simp [maskAgreementProfile, show ¬n < a by omega, show ¬a < threshold by omega]
  · intro candidate challenge
    dsimp only [agreement]
    split
    · exact v1Agreement_le _ _ _ _
    · omega
  · intro candidate a ha habove
    have hta : threshold ≤ a := by omega
    have hpositive : 0 < a := mask.threshold_pos.trans_le hta
    by_cases h : ¬statement.Satisfies candidate.decodedMessages
    · simp only [agreement, dif_pos h]
      cases hkind : (violation candidate h).kind with
      | linear =>
          exact v1Agreement_linear_density candidate (violation candidate h) hkind
            respond a hpositive mask.response_injective ha
            (mask.close a hta ha) (bound a) (mask.family a hta ha)
      | quadratic i =>
          exact v1Agreement_quadratic_density candidate (violation candidate h) i hkind
            respond a hpositive mask.response_injective ha
            (mask.close a hta ha) (bound a) (mask.family a hta ha)
    · have hempty : AgreementProfile.tailSet (agreement candidate) a = ∅ := by
        ext challenge
        simp only [AgreementProfile.tailSet, agreement, dif_neg h]
        simp [Nat.not_le_of_gt hpositive]
      simp [hempty]
  · intro candidate h challenge hc
    let remaining := candidate.remainingBadColumns (challenge 0).proximity
      ((respond challenge).proximity 0)
    have hbad : ∀ query : QuerySet n r, SchemeVerifier.Accepts C scheme statement
        challenge (respond challenge) query (openSchemeOracle oracle query) →
        query.coordinates ∩ candidate.badColumns ⊆ remaining := by
      intro query hacc
      exact candidate.query_bad_subset_remaining _ _ query (hacc 0).1
    have cover := v1_constraint_cover candidate (violation candidate h) respond challenge
      remaining hc.2 hbad
    simpa only [agreement, dif_pos h] using cover

/-- Arbitrary statements and every response strategy, including the original
unchecked-mask profile with any certified mask list bound (Johnson or
Hahn/Delsarte). The extractor itself is unchanged. -/
theorem scalarGap_profiled_extraction_failure_of_card
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound) {L : ℕ}
    (hcard : (univ : Finset (SchemeLiftCandidate C oracle (e + g))).card ≤ L)
    (hrows : CoreRowsNonempty nw nq)
    (mask : V1MaskRange C threshold bound) (ht : threshold ≤ n)
    (respond : Challenge F nw nq 1 Equations → Response F r w n 1) :
    ((univ.filter fun pair : (Challenge F nw nq 1 Equations) × QuerySet n r =>
      (gapPolicy).accepts statement pair.1 (respond pair.1) pair.2 (openSchemeOracle oracle pair.2) ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g) gapPolicy
        (fun candidate => candidate.decodedMessages) statement pair.1 (respond pair.1) = none).card : ℚ) /
      Fintype.card ((Challenge F nw nq 1 Equations) × QuerySet n r) ≤
      (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
        (Fintype.card F) n e g d outerBound localBound).excessContribution
          (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator (Fintype.card F) g)
          n n 0 r (max (n - e - 1) (min n (g + (threshold - 1)))) +
      (maskAgreementProfile (Fintype.card F) n
        L threshold bound).contribution
          (Fintype.card F) n e g r := by
  classical
  letI : Nonempty (SchemeTestedRow NoMask nw nq 1) := schemeTestedRowNonemptyOfCoreRows hrows
  refine ScalarGapExtraction.profiled_extraction_failure_of_card gapPolicy
    (fun candidate => candidate.decodedMessages)
    (schemeExtractorPolicy (Equations := Equations) (nw := nw) (nq := nq) C scheme)
    hmin conditions hcard (maskAgreementProfile (Fintype.card F) n
      L threshold bound) (threshold - 1) (by omega)
    ?_ respond ?_
  · intro a ha
    simp [maskAgreementProfile, show ¬n < a by omega, show a < threshold by
      have := mask.threshold_pos; omega]
  · intro certificate
    exact scalarGap_profiled_arithmetic_certificate C oracle statement hmin
      conditions mask respond certificate

/-- Arbitrary statements and every response strategy, including the original
unchecked-mask profile with any certified mask list bound (Johnson or
Hahn/Delsarte). The extractor itself is unchanged. -/
theorem scalarGap_profiled_extraction_failure
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    (hrows : CoreRowsNonempty nw nq)
    (mask : V1MaskRange C threshold bound) (ht : threshold ≤ n)
    (respond : Challenge F nw nq 1 Equations → Response F r w n 1) :
    ((univ.filter fun pair : (Challenge F nw nq 1 Equations) × QuerySet n r =>
      (gapPolicy).accepts statement pair.1 (respond pair.1) pair.2 (openSchemeOracle oracle pair.2) ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g) gapPolicy
        (fun candidate => candidate.decodedMessages) statement pair.1 (respond pair.1) = none).card : ℚ) /
      Fintype.card ((Challenge F nw nq 1 Equations) × QuerySet n r) ≤
      (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
        (Fintype.card F) n e g d outerBound localBound).excessContribution
          (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator (Fintype.card F) g)
          n n 0 r (max (n - e - 1) (min n (g + (threshold - 1)))) +
      (maskAgreementProfile (Fintype.card F) n
        (InterleavedJohnson.listBound n d (e + g)) threshold bound).contribution
          (Fintype.card F) n e g r := by
  have hradius : e + g < d := by
    have := conditions.outer.punctured.punctured_three_radius
    omega
  exact scalarGap_profiled_extraction_failure_of_card C oracle statement hmin conditions
    (SchemeLiftCandidate.univ_card_le_listBound C oracle hmin
      ((Nat.le_of_lt hradius).trans hmin.distance_le_length) hradius
      conditions.outer.johnson.list_denominator_positive) hrows mask ht respond

end Ligero.V1
