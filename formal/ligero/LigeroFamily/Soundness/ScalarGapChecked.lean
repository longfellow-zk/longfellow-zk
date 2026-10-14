import LigeroFamily.Soundness.ScalarGapProfiled

/-! Shared checked-arithmetic extraction assembly. V2 and V3 supply only their
candidate-local residual test; proximity, witness lists, exceptional sets,
profiles and extraction failure counting are shared. -/
namespace LigeroFamily.ScalarGapExtraction
open Finset CodingTheory MultiplicativeCode
open scoped Classical
set_option linter.unusedSectionVars false
variable {F CheckedMask DirectMask Equations Challenge Response Tail : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype CheckedMask] [DecidableEq CheckedMask]
variable [Fintype Equations] [DecidableEq Equations]
variable [Fintype Challenge] [DecidableEq Challenge] [Nonempty Challenge]
variable [Fintype Tail] [DecidableEq Tail]
variable {q r w n nw nq e g d lineBound : ℕ}
variable {C : MultiplicativeCode F r w n}
variable {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}
variable {layout : ConstraintLayout F q w}
variable (policy : SchemeProtocolPolicy (Equations := Equations) C layout
  Challenge Response CheckedMask DirectMask nw nq 1)

/-- The common arithmetic contract for a single invalid decoded candidate. -/
structure CheckedArithmeticBudget (candidate : SchemeLiftCandidate C oracle (e + g))
    (statement : ConstraintSystem F nw nq q Equations) (cutoff : ℕ) where
  special : Finset Challenge
  density : Fintype.card F * special.card ≤ Fintype.card Challenge
  cover : ∀ challenge response, challenge ∉ special →
    Compatible policy candidate challenge response →
    Nonempty (PolicyAcceptingQueryCover policy oracle statement challenge response
      (min n (g + cutoff)))

variable (messages : SchemeLiftCandidate C oracle (e + g) → CoreMessages F nw nq q)
variable (statement : ConstraintSystem F nw nq q Equations) (cutoff : ℕ)
variable (budget : ∀ candidate, ¬statement.Satisfies (messages candidate) →
  Nonempty (CheckedArithmeticBudget policy candidate statement cutoff))

noncomputable def checkedSpecial (candidate : SchemeLiftCandidate C oracle (e + g)) : Finset Challenge :=
  if h : ¬statement.Satisfies (messages candidate) then (Classical.choice (budget candidate h)).special else ∅

theorem checkedSpecial_density (candidate : SchemeLiftCandidate C oracle (e + g)) :
    Fintype.card F * (checkedSpecial policy messages statement cutoff budget candidate).card ≤
      Fintype.card Challenge := by
  classical
  by_cases h : ¬statement.Satisfies (messages candidate)
  · simp only [checkedSpecial, dif_pos h]; exact (Classical.choice (budget candidate h)).density
  · simp only [checkedSpecial, dif_neg h, Finset.card_empty, Nat.mul_zero]; omega

theorem checkedSpecial_cover (candidate : SchemeLiftCandidate C oracle (e + g))
    (hns : ¬statement.Satisfies (messages candidate)) (challenge : Challenge) (response : Response)
    (hnot : challenge ∉ checkedSpecial policy messages statement cutoff budget candidate)
    (hc : Compatible policy candidate challenge response) :
    Nonempty (PolicyAcceptingQueryCover policy oracle statement challenge response (min n (g + cutoff))) := by
  simp only [checkedSpecial, dif_pos hns] at hnot
  exact (Classical.choice (budget candidate hns)).cover challenge response hnot hc

include budget

/-- All checked variants use one common coarse proximity-gap certificate. -/
theorem checked_gap_certificate [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    (extractor : SchemeExtractorPolicy policy Tail)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : SelectedMCALineConditions C.baseCode (Fintype.card F) e g d lineBound)
    (hk : 0 < C.k) :
    Nonempty (Certificate policy messages statement
      (max (n - e - 1) (min n (g + cutoff)))
      ((lineBound : ℚ) / (Fintype.card F - (g + 1) : ℕ) +
        (InterleavedJohnson.listBound n d (e + g) : ℚ) / Fintype.card F)) := by
  have hradius : e + g < d := by have := conditions.punctured.punctured_three_radius; omega
  exact certificate_of_gap policy extractor messages statement hmin conditions hk cutoff
    (InterleavedJohnson.listBound n d (e + g))
    (SchemeLiftCandidate.univ_card_le_listBound C oracle hmin
      ((Nat.le_of_lt hradius).trans hmin.distance_le_length) hradius
      conditions.johnson.list_denominator_positive)
    (checkedSpecial policy messages statement cutoff budget)
    (checkedSpecial_density policy messages statement cutoff budget)
    (fun candidate hns challenge hnot response hc =>
      checkedSpecial_cover policy messages statement cutoff budget candidate hns challenge response hnot hc)

/-- All checked variants share the complete agreement-dependent extraction proof. -/
theorem checked_profiled_extraction_failure_of_card [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (extractor : SchemeExtractorPolicy policy Tail)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound) {L : ℕ}
    (hcard : (univ : Finset (SchemeLiftCandidate C oracle (e + g))).card ≤ L)
    (hcutoff : cutoff ≤ n) (respond : Challenge → Response) :
    ((univ.filter fun pair : Challenge × QuerySet n r =>
      policy.accepts statement pair.1 (respond pair.1) pair.2 (openSchemeOracle oracle pair.2) ∧
      extract policy messages statement pair.1 (respond pair.1) = none).card : ℚ) /
      Fintype.card (Challenge × QuerySet n r) ≤
      (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
        (Fintype.card F) n e g d outerBound localBound).excessContribution
          (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator (Fintype.card F) g)
          n n 0 r (max (n - e - 1) (min n (g + cutoff))) +
      (checkedAgreementProfile (Fintype.card F)
        L n cutoff).contribution
          (Fintype.card F) n e g r := by
  refine profiled_extraction_failure_of_card policy messages extractor hmin conditions hcard
    (checkedAgreementProfile (Fintype.card F) L n cutoff)
    cutoff hcutoff ?_ respond ?_
  · intro a ha; simp [checkedAgreementProfile, show ¬n < a by omega, ha]
  · intro certificate
    exact checkedProfiledArithmeticCertificate policy messages certificate hmin
      (by have := conditions.outer.punctured.punctured_three_radius; omega) cutoff
      (checkedSpecial policy messages statement cutoff budget)
      (checkedSpecial_density policy messages statement cutoff budget)
      (fun candidate hns challenge hnot hc =>
        checkedSpecial_cover policy messages statement cutoff budget candidate hns challenge (respond challenge) hnot hc)

/-- All checked variants share the complete agreement-dependent extraction proof. -/
theorem checked_profiled_extraction_failure [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (extractor : SchemeExtractorPolicy policy Tail)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    (hcutoff : cutoff ≤ n) (respond : Challenge → Response) :
    ((univ.filter fun pair : Challenge × QuerySet n r =>
      policy.accepts statement pair.1 (respond pair.1) pair.2 (openSchemeOracle oracle pair.2) ∧
      extract policy messages statement pair.1 (respond pair.1) = none).card : ℚ) /
      Fintype.card (Challenge × QuerySet n r) ≤
      (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
        (Fintype.card F) n e g d outerBound localBound).excessContribution
          (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator (Fintype.card F) g)
          n n 0 r (max (n - e - 1) (min n (g + cutoff))) +
      (checkedAgreementProfile (Fintype.card F)
        (InterleavedJohnson.listBound n d (e + g)) n cutoff).contribution
          (Fintype.card F) n e g r := by
  have hradius : e + g < d := by
    have := conditions.outer.punctured.punctured_three_radius
    omega
  exact checked_profiled_extraction_failure_of_card policy messages statement cutoff budget
    extractor hmin conditions
    (SchemeLiftCandidate.univ_card_le_listBound C oracle hmin
      ((Nat.le_of_lt hradius).trans hmin.distance_le_length) hradius
      conditions.outer.johnson.list_denominator_positive) hcutoff respond

end LigeroFamily.ScalarGapExtraction
