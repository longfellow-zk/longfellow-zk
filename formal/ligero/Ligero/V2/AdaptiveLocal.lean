import LigeroFamily.Soundness.CheckedAdaptiveLocal
import Ligero.V2.ScalarGapExtraction

/-! Response-uniform local FS classifier for Ligero V2. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Ligero.V2

open Finset LigeroFamily CodingTheory MultiplicativeCode
open scoped Classical

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq e g d outerBound : ℕ} {localBound : ℕ → ℕ}

theorem local_card_bounds
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (oracle : Oracle F nw nq n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (hfalse : NoDecodedSolution C oracle (e + g) statement)
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
        Fintype.card (Challenge F nw nq 1 Equations) ≤ escapeCount)
    (hcoverBudget : hypergeometricRatio
        (max failureThreshold
          (max (n - e - 1) (min n (g + arithmeticThreshold)))) n r *
        (n.choose r) ≤ coverCount) :
    ∃ Doom : Challenge F nw nq 1 Equations → Prop,
      (univ.filter fun a : Challenge F nw nq 1 Equations => ¬Doom a).card ≤ escapeCount ∧
      ∀ a (response : Response F r w n 1), Doom a →
        (univ.filter fun query : QuerySet n r =>
          (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
            (repetitions := 1) C (scheme C M)).accepts statement a response query
              (openSchemeOracle oracle query)).card ≤ coverCount := by
  letI : Nonempty (SchemeTestedRow Ligero.V2.Mask nw nq 1) :=
    ⟨Sum.inr (0, Ligero.V2.Mask.linearZRCoefficient)⟩
  letI : Nonempty (Response F r w n 1) :=
    ⟨⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩⟩
  exact LigeroFamily.checked_local_card_bounds C (ConstraintLayout.identity w)
    (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
      (repetitions := 1) C (scheme C M)) oracle
    (fun candidate => candidate.decodedMessages) statement hfalse
    (fun candidate hns => scalarGap_arithmeticBudget C M oracle statement candidate hns hk)
    (schemeExtractorPolicy (Equations := Equations) (nw := nw) (nq := nq) C (scheme C M))
    hmin conditions hcard failureThreshold arithmeticThreshold
    hfailureThreshold harithmeticThreshold hr escapeCount coverCount
    hescapeBudget hcoverBudget

end Ligero.V2
