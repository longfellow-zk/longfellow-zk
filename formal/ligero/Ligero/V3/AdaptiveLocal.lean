import LigeroFamily.Soundness.CheckedAdaptiveLocal
import Ligero.V3.ScalarGapExtraction

/-! Response-uniform local FS classifier for Ligero V3. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Ligero.V3

open Finset LigeroFamily CodingTheory MultiplicativeCode
open scoped Classical

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {q r w n nw nq e g d outerBound : ℕ} {localBound : ℕ → ℕ}

theorem local_card_bounds
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (layout : ConstraintLayout F q w)
    (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq n 1)
    (statement : ConstraintSystem F nw nq q Equations)
    (hfalse : ∀ candidate : SchemeLiftCandidate C oracle (e + g),
      ¬statement.Satisfies (candidate.directMessages (layout := layout)))
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    {L : ℕ} (hcard : (univ : Finset (SchemeLiftCandidate C oracle (e + g))).card ≤ L)
    (hk : 0 < C.k) (failureThreshold arithmeticThreshold : ℕ)
    (hfailureThreshold : failureThreshold + 1 ≤ n)
    (harithmeticThreshold : arithmeticThreshold + 1 ≤ n)
    (hr : r ≤ n) (escapeCount coverCount : ℕ)
    (hescapeBudget :
      (((SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
          (Fintype.card F) n e g d outerBound localBound).labelsAtLeast
            (failureThreshold + 1) : ℚ) /
          SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
            (Fintype.card F) g +
        ((checkedAgreementProfile (Fintype.card F) L n (2 * C.k - 1)).labelsAtLeast
          (arithmeticThreshold + 1) : ℚ) / Fintype.card F) *
        Fintype.card (DirectChallenge F Equations nw nq 1) ≤ escapeCount)
    (hcoverBudget : hypergeometricRatio
        (max failureThreshold
          (max (n - e - 1) (min n (g + arithmeticThreshold)))) n r *
        (n.choose r) ≤ coverCount) :
    ∃ Doom : DirectChallenge F Equations nw nq 1 → Prop,
      (univ.filter fun a : DirectChallenge F Equations nw nq 1 => ¬Doom a).card ≤
        escapeCount ∧
      ∀ a (response : DirectResponse F r w n 1), Doom a →
        (univ.filter fun query : QuerySet n r =>
          (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
            (repetitions := 1) C M layout).accepts statement a response query
              (openSchemeOracle oracle query)).card ≤ coverCount := by
  letI : Nonempty (SchemeTestedRow LinearConstraintMask nw nq 1) :=
    ⟨Sum.inr (0, LinearConstraintMask.zRCoefficient)⟩
  letI : Nonempty (DirectResponse F r w n 1) :=
    ⟨⟨fun _ _ => 0, fun _ _ => 0⟩⟩
  exact LigeroFamily.checked_local_card_bounds C layout
    (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
      (repetitions := 1) C M layout) oracle
    (fun candidate => candidate.directMessages (layout := layout)) statement hfalse
    (fun candidate hns => scalarGap_arithmeticBudget C M layout oracle statement candidate hns hk)
    (directExtractorPolicy (Equations := Equations) (nw := nw) (nq := nq) C M layout)
    hmin conditions hcard failureThreshold arithmeticThreshold
    hfailureThreshold harithmeticThreshold hr escapeCount coverCount
    hescapeBudget hcoverBudget

end Ligero.V3
