import LigeroFamily.Soundness.ScalarGapChecked
import Ligero.V3.ScalarGapExtraction

/-! Agreement-dependent extraction, retaining scalar challenges and all checked masks. -/
namespace Ligero.V3
open LigeroFamily CodingTheory MultiplicativeCode Finset
open scoped Classical
set_option linter.unusedSectionVars false
variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq e g d outerBound : ℕ} {localBound : ℕ → ℕ}
variable (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
variable {q : ℕ}
variable (layout : ConstraintLayout F q w)
variable (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq n 1)
variable (statement : ConstraintSystem F nw nq q Equations)
local notation "gapPolicy" => DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
  (repetitions := 1) C M layout

/-- The full interactive profile bounds extraction failure for arbitrary
statements and every response strategy. No false-statement premise is used. -/
theorem scalarGap_profiled_extraction_failure
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    (hk : 0 < C.k) (h2k : 2 * C.k ≤ n)
    (respond : DirectChallenge F Equations nw nq 1 → DirectResponse F r w n 1) :
    ((univ.filter fun pair : (DirectChallenge F Equations nw nq 1) × QuerySet n r =>
      (gapPolicy).accepts statement pair.1 (respond pair.1) pair.2 (openSchemeOracle oracle pair.2) ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g) gapPolicy
        (fun candidate => candidate.directMessages (layout := layout)) statement pair.1 (respond pair.1) = none).card : ℚ) /
      Fintype.card ((DirectChallenge F Equations nw nq 1) × QuerySet n r) ≤
      (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
        (Fintype.card F) n e g d outerBound localBound).excessContribution
          (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator (Fintype.card F) g)
          n n 0 r (max (n - e - 1) (min n (g + (2 * C.k - 1)))) +
      (checkedAgreementProfile (Fintype.card F)
        (InterleavedJohnson.listBound n d (e + g)) n
        (2 * C.k - 1)).contribution (Fintype.card F) n e g r := by
  letI : Nonempty (SchemeTestedRow LinearConstraintMask nw nq 1) := ⟨Sum.inr (0, LinearConstraintMask.zRCoefficient)⟩
  exact ScalarGapExtraction.checked_profiled_extraction_failure gapPolicy (fun candidate => candidate.directMessages (layout := layout)) statement
    (2 * C.k - 1) (fun candidate hns => scalarGap_arithmeticBudget C M layout oracle statement candidate hns hk)
    (directExtractorPolicy (Equations := Equations) (nw := nw) (nq := nq) C M layout) hmin conditions (by omega) respond

end Ligero.V3
