import LigeroFamily.Soundness.ScalarGapExtraction
import LigeroFamily.Soundness.SchemePolicyExtractor
import Ligero.V1.Soundness.V1Profile

/-! Scalar response-assisted extraction with the original unchecked masks.
The mask-label Johnson term is part of V1 arithmetic and is retained. It is
distinct from the full response-list penalty of the FS compiler. -/

set_option linter.unusedSectionVars false
namespace Ligero.V1
open LigeroFamily CodingTheory MultiplicativeCode Finset
open scoped Classical

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq e g d lineBound threshold : ℕ}
variable (C : MultiplicativeCode F r w n)
variable (oracle : Oracle F nw nq n 1)
variable (statement : ConstraintSystem F nw nq w Equations)

local notation "gapPolicy" => SchemeVerifier.policy (Equations := Equations)
  (nw := nw) (nq := nq) (repetitions := 1) C scheme

noncomputable def scalarGapExtract (challenge : Challenge F nw nq 1 Equations)
    (response : Response F r w n 1) :=
  ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g) gapPolicy
    (fun candidate => candidate.decodedMessages) statement challenge response

/-- A fixed unchecked-mask label exception, uniform over actual responses. -/
structure ScalarMaskBudget
    (candidate : SchemeLiftCandidate C oracle (e + g))
    (violation : V1Violation candidate statement) (threshold : ℕ) where
  special : Finset (Challenge F nw nq 1 Equations)
  density : Fintype.card F * special.card ≤
    uncheckedAgreementListBound n (2 * C.k - 1) threshold *
      Fintype.card (Challenge F nw nq 1 Equations)
  captures : ∀ challenge (response : Response F r w n 1),
    threshold ≤ Ligero.V1.SchemeLiftCandidate.v1Agreement candidate violation
      (fun _ => response) challenge → challenge ∈ special

theorem scalarMaskBudget_nonempty
    (candidate : SchemeLiftCandidate C oracle (e + g))
    (violation : V1Violation candidate statement)
    (johnson : V1JohnsonRange C threshold) (ht : threshold ≤ n) :
    Nonempty (ScalarMaskBudget C oracle statement candidate violation threshold) := by
  classical
  have hpositive := johnson.threshold_pos
  cases hkind : violation.kind with
  | linear =>
    let label : EvaluationRow F r w n → F :=
      fun row ↦ -(∑ i : Fin w, row (witnessPosition i))
    let labels := responseLabelsAgreeingAtLeast C
      (oracle.directMask 0 .linear) label threshold
    let special := finiteDotLabelPreimage
      (Ligero.V1.SchemeLiftCandidate.v1LinearResidual candidate statement) labels
    have hnonzero : Ligero.V1.SchemeLiftCandidate.v1LinearResidual candidate statement ≠ 0 := by
      simpa [hkind] using violation.nonzero
    have hspecial : Fintype.card F * special.card ≤
        labels.card * Fintype.card (Equations → F) := by
      simpa [special] using finiteDotLabelPreimage_density
        (Ligero.V1.SchemeLiftCandidate.v1LinearResidual candidate statement) labels hnonzero
    have hlabels : labels.card ≤
        uncheckedAgreementListBound n (2 * C.k - 1) threshold := by
      simpa [labels, label] using responseLabelsAgreeingAtLeast_card_le C
        (oracle.directMask 0 .linear) label threshold johnson.response_injective ht (johnson.close _ le_rfl ht) (johnson.denominator_pos _ le_rfl ht)
    have hspecialBound : Fintype.card F * special.card ≤
        uncheckedAgreementListBound n (2 * C.k - 1) threshold *
          Nat.card (Equations → F) := by
      rw [Nat.card_eq_fintype_card]
      exact hspecial.trans (Nat.mul_le_mul_right _ hlabels)
    refine ⟨{ special := SchemeInternal.liftLinear (CheckedMask := NoMask) (nw := nw) (nq := nq) special, density := ?_, captures := ?_ }⟩
    · rw [← Nat.card_eq_fintype_card (α := Challenge F nw nq 1 Equations)]
      exact SchemeInternal.liftLinear_density (CheckedMask := NoMask) (nw := nw) (nq := nq) (Fintype.card F)
        (uncheckedAgreementListBound n (2 * C.k - 1) threshold) special hspecialBound
    · intro challenge response hagreement
      simp only [Ligero.V1.SchemeLiftCandidate.v1Agreement, hkind] at hagreement
      split at hagreement
      next hvalid =>
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact Ligero.V1.SchemeLiftCandidate.v1_linear_label_mem candidate statement
          (challenge 0).linear (response.linear 0) hvalid threshold
          hagreement
      next hvalid => omega
  | quadratic i =>
    let label : EvaluationRow F r w n → F :=
      fun row ↦ -row (witnessPosition i)
    let labels := responseLabelsAgreeingAtLeast C
      (oracle.directMask 0 .quadratic) label threshold
    let residual := fun row ↦ Ligero.V1.SchemeLiftCandidate.v1QuadraticResidual candidate row i
    let special := finiteDotLabelPreimage residual labels
    have hnonzero : residual ≠ 0 := by
      simpa [hkind, residual] using violation.nonzero
    have hspecial : Fintype.card F * special.card ≤
        labels.card * Fintype.card (Fin nq → F) := by
      simpa [special, residual] using finiteDotLabelPreimage_density
        residual labels hnonzero
    have hlabels : labels.card ≤
        uncheckedAgreementListBound n (2 * C.k - 1) threshold := by
      simpa [labels, label] using responseLabelsAgreeingAtLeast_card_le C
        (oracle.directMask 0 .quadratic) label threshold johnson.response_injective ht (johnson.close _ le_rfl ht) (johnson.denominator_pos _ le_rfl ht)
    have hspecialBound : Fintype.card F * special.card ≤
        uncheckedAgreementListBound n (2 * C.k - 1) threshold *
          Nat.card (Fin nq → F) := by
      rw [Nat.card_eq_fintype_card]
      exact hspecial.trans (Nat.mul_le_mul_right _ hlabels)
    refine ⟨{ special := SchemeInternal.liftQuadratic (CheckedMask := NoMask) (Equations := Equations) (nw := nw) special, density := ?_, captures := ?_ }⟩
    · rw [← Nat.card_eq_fintype_card (α := Challenge F nw nq 1 Equations)]
      exact SchemeInternal.liftQuadratic_density (CheckedMask := NoMask) (Equations := Equations) (nw := nw) (Fintype.card F)
        (uncheckedAgreementListBound n (2 * C.k - 1) threshold) special hspecialBound
    · intro challenge response hagreement
      simp only [Ligero.V1.SchemeLiftCandidate.v1Agreement, hkind] at hagreement
      split at hagreement
      next hvalid =>
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact Ligero.V1.SchemeLiftCandidate.v1_quadratic_label_mem candidate
          (challenge 0).quadratic i (response.quadratic 0) hvalid threshold
          hagreement
      next hvalid => omega

theorem scalarGap_extraction_certificate
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : SelectedMCALineConditions C.baseCode (Fintype.card F) e g d lineBound)
    (hrows : CoreRowsNonempty nw nq)
    (johnson : V1JohnsonRange C threshold) (ht : threshold ≤ n) (hk : 0 < C.k) :
    Nonempty (ScalarGapExtraction.Certificate (oracle := oracle) (e := e) (g := g) gapPolicy
      (fun candidate => candidate.decodedMessages) statement
      (max (n - e - 1) (min n (g + (threshold - 1))))
      ((lineBound : ℚ) / (Fintype.card F - (g + 1) : ℕ) +
        ((InterleavedJohnson.listBound n d (e + g) *
          uncheckedAgreementListBound n (2 * C.k - 1) threshold : ℕ) : ℚ) / Fintype.card F)) := by
  classical
  letI : Nonempty (SchemeTestedRow NoMask nw nq 1) := schemeTestedRowNonemptyOfCoreRows hrows
  let violation := fun (candidate : SchemeLiftCandidate C oracle (e + g))
      (hns : ¬statement.Satisfies candidate.decodedMessages) =>
    Classical.choice (V1Violation.nonempty_of_false candidate hns)
  let special := fun candidate : SchemeLiftCandidate C oracle (e + g) =>
    if hns : ¬statement.Satisfies candidate.decodedMessages then
      (Classical.choice (scalarMaskBudget_nonempty C oracle statement candidate
        (violation candidate hns) johnson ht)).special else ∅
  have hradius : e + g < d := by have := conditions.punctured.punctured_three_radius; omega
  apply ScalarGapExtraction.certificate_of_gap_with_labels gapPolicy
    (schemeExtractorPolicy (Equations := Equations) (nw := nw) (nq := nq) C scheme)
    (fun candidate => candidate.decodedMessages) statement hmin conditions hk (threshold - 1)
    (InterleavedJohnson.listBound n d (e + g))
    (uncheckedAgreementListBound n (2 * C.k - 1) threshold)
    (SchemeLiftCandidate.univ_card_le_listBound C oracle hmin
      ((Nat.le_of_lt hradius).trans hmin.distance_le_length) hradius
      conditions.johnson.list_denominator_positive) special
  · intro candidate
    by_cases hns : ¬statement.Satisfies candidate.decodedMessages
    · dsimp only [special]
      rw [dif_pos hns]
      exact (Classical.choice (scalarMaskBudget_nonempty C oracle statement candidate
        (violation candidate hns) johnson ht)).density
    · dsimp only [special]
      rw [dif_neg hns]
      simp
  · intro candidate hns challenge hnot response hcompatible
    dsimp only [special] at hnot
    rw [dif_pos hns] at hnot
    have ha : Ligero.V1.SchemeLiftCandidate.v1Agreement candidate (violation candidate hns) (fun _ => response) challenge < threshold := by
      by_contra hn
      exact hnot ((Classical.choice (scalarMaskBudget_nonempty C oracle statement candidate
        (violation candidate hns) johnson ht)).captures challenge response (Nat.le_of_not_gt hn))
    let remaining := candidate.remainingBadColumns (challenge 0).proximity (response.proximity 0)
    obtain ⟨cover⟩ := Ligero.V1.SchemeLiftCandidate.v1_constraint_cover candidate (violation candidate hns) (fun _ => response)
      challenge remaining hcompatible.2 (by
        intro query hacc
        exact candidate.query_bad_subset_remaining _ _ query (hacc 0).1)
    exact ⟨{
      allowed := cover.allowed
      allowed_card := cover.allowed_card.trans (min_le_min_left n (by omega))
      covers := cover.covers }⟩

theorem scalarGap_extraction_failure
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : SelectedMCALineConditions C.baseCode (Fintype.card F) e g d lineBound)
    (hrows : CoreRowsNonempty nw nq)
    (johnson : V1JohnsonRange C threshold) (ht : threshold ≤ n) (hk : 0 < C.k)
    (respond : Challenge F nw nq 1 Equations → Response F r w n 1) :
    ((univ.filter fun pair : Challenge F nw nq 1 Equations × QuerySet n r =>
      (gapPolicy).accepts statement pair.1 (respond pair.1) pair.2 (openSchemeOracle oracle pair.2) ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g) gapPolicy
        (fun candidate => candidate.decodedMessages) statement pair.1 (respond pair.1) = none).card : ℚ) /
      Fintype.card (Challenge F nw nq 1 Equations × QuerySet n r) ≤
    let delta := hypergeometricRatio (max (n - e - 1) (min n (g + (threshold - 1)))) n r
    delta + (1 - delta) * ((lineBound : ℚ) / (Fintype.card F - (g + 1) : ℕ) +
      ((InterleavedJohnson.listBound n d (e + g) *
        uncheckedAgreementListBound n (2 * C.k - 1) threshold : ℕ) : ℚ) / Fintype.card F) := by
  obtain ⟨cert⟩ := scalarGap_extraction_certificate C oracle statement hmin conditions hrows johnson ht hk
  exact cert.extraction_failure (by omega) respond


/-- The same bound on the concrete IOP run, for every prover. -/
theorem scalarGap_iop_extraction_failure
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : SelectedMCALineConditions C.baseCode (Fintype.card F) e g d lineBound)
    (hrows : CoreRowsNonempty nw nq)
    (johnson : V1JohnsonRange C threshold) (ht : threshold ≤ n) (hk : 0 < C.k)
    (prover : IPCPProver (ConstraintSystem F nw nq w Equations)
      (SchemeOracle F NoMask Ligero.V1.Mask nw nq n 1) (Challenge F nw nq 1 Equations) (Response F r w n 1))
    (hcommit : prover.commit statement = oracle) :
    ((univ.filter fun pair : Challenge F nw nq 1 Equations × QuerySet n r =>
      (gapPolicy).protocol.accepts prover statement pair = true ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g) gapPolicy
        (fun candidate => candidate.decodedMessages) statement pair.1 (prover.respond statement oracle pair.1) = none).card : ℚ) /
      Fintype.card (Challenge F nw nq 1 Equations × QuerySet n r) ≤
    let delta := hypergeometricRatio (max (n - e - 1) (min n (g + (threshold - 1)))) n r
    delta + (1 - delta) * ((lineBound : ℚ) / (Fintype.card F - (g + 1) : ℕ) +
      ((InterleavedJohnson.listBound n d (e + g) *
        uncheckedAgreementListBound n (2 * C.k - 1) threshold : ℕ) : ℚ) / Fintype.card F) := by
  obtain ⟨cert⟩ := scalarGap_extraction_certificate C oracle statement hmin conditions hrows johnson ht hk
  exact cert.iop_extraction_failure (by omega) prover hcommit

end Ligero.V1
