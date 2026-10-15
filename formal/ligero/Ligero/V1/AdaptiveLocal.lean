import Lfzk.LigeroV1Rbr
import LigeroFamily.Protocol.FiniteResponse

/-!
# V1 local challenge and query budgets for adaptive Fiat–Shamir

This packages the existing profiled V1 classifier into cardinality bounds
uniform over the response fixed before the query coin is drawn.  The response
strategy used to construct the classifier maximizes the accepting query count
at each challenge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Ligero.V1

open Finset LigeroFamily CodingTheory
open scoped Classical

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq e g d outerBound threshold : ℕ} {localBound : ℕ → ℕ}

/-- The two local budgets needed by the adaptive-root compiler, derived from
the profiled V1 theorem. `escapeCount` and `coverCount` are exact natural
ceilings certified by the caller's rational inequalities. -/
theorem local_card_bounds
    (hrows : CoreRowsNonempty nw nq)
    (C : MultiplicativeCode F r w n)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : Oracle F nw nq n 1)
    (hfalse : NoDecodedSolution C oracle (e + g) statement)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    {L : ℕ} (hcard : (univ : Finset (SchemeLiftCandidate C oracle (e + g))).card ≤ L)
    {bound : ℕ → ℕ} (mask : V1MaskRange C threshold bound)
    (failureThreshold arithmeticThreshold : ℕ)
    (hfailureThreshold : failureThreshold + 1 ≤ n)
    (harithmeticThreshold : arithmeticThreshold + 1 ≤ n)
    (hr : r ≤ n) (escapeCount coverCount : ℕ)
    (hescapeBudget :
      (((SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
          (Fintype.card F) n e g d outerBound localBound).labelsAtLeast
            (failureThreshold + 1) : ℚ) /
          SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
            (Fintype.card F) g +
        ((maskAgreementProfile (Fintype.card F) n L threshold bound).labelsAtLeast
          (arithmeticThreshold + 1) : ℚ) / Fintype.card F) *
        Fintype.card (Challenge F nw nq 1 Equations) ≤ escapeCount)
    (hcoverBudget : hypergeometricRatio
        (max failureThreshold
          (max (n - e - 1) (min n (g + arithmeticThreshold)))) n r *
        (n.choose r) ≤ coverCount) :
    ∃ Doom : Challenge F nw nq 1 Equations → Prop,
      (univ.filter fun a : Challenge F nw nq 1 Equations => ¬Doom a).card ≤ escapeCount ∧
      ∀ a (response : Response F r w n 1), Doom a →
        (univ.filter fun q : QuerySet n r =>
          (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
            (repetitions := 1) C scheme).accepts statement a response q
            (openSchemeOracle oracle q)).card ≤ coverCount := by
  classical
  let policy := SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
    (repetitions := 1) C scheme
  let accepting (a : Challenge F nw nq 1 Equations) (ρ : Response F r w n 1) :=
    (univ.filter fun q : QuerySet n r =>
      policy.accepts statement a ρ q (openSchemeOracle oracle q))
  haveI : Nonempty (Response F r w n 1) :=
    ⟨⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩⟩
  let maxResponse (a : Challenge F nw nq 1 Equations) : Response F r w n 1 :=
    Classical.choose (Finset.exists_max_image (univ : Finset (Response F r w n 1))
      (fun ρ => (accepting a ρ).card) univ_nonempty)
  have hmax (a : Challenge F nw nq 1 Equations) (ρ : Response F r w n 1) :
      (accepting a ρ).card ≤ (accepting a (maxResponse a)).card :=
    (Classical.choose_spec (Finset.exists_max_image
      (univ : Finset (Response F r w n 1))
      (fun ρ => (accepting a ρ).card) univ_nonempty)).2 ρ (mem_univ _)
  let prover : IPCPProver
      (ConstraintSystem F nw nq w Equations) (Oracle F nw nq n 1)
      (Challenge F nw nq 1 Equations) (Response F r w n 1) :=
    { commit := fun _ => oracle, respond := fun _ _ a => maxResponse a }
  obtain ⟨classifier, hquery, hescape, hcover⟩ :=
    ligerov1_roundByRound_mask_profiled hrows C statement prover hfalse hmin conditions
      hcard mask failureThreshold arithmeticThreshold hfailureThreshold harithmeticThreshold
  let Doom := classifier.ProfiledDoomedAfter failureThreshold arithmeticThreshold
  refine ⟨Doom, ?_, ?_⟩
  · have hsubset : (univ.filter fun a : Challenge F nw nq 1 Equations => ¬Doom a) ⊆
        classifier.profiledEscaping failureThreshold arithmeticThreshold := by
      intro a ha
      exact hcover a (mem_filter.mp ha).2
    have hpositive : (0 : ℚ) < Fintype.card (Challenge F nw nq 1 Equations) := by
      exact_mod_cast Fintype.card_pos
    have hq : ((classifier.profiledEscaping failureThreshold arithmeticThreshold).card : ℚ)
        ≤ escapeCount := (div_le_iff₀ hpositive).mp hescape |>.trans hescapeBudget
    exact (card_le_card hsubset).trans (by exact_mod_cast hq)
  · intro a response hd
    have hpositive : (0 : ℚ) < n.choose r := by
      exact_mod_cast Nat.choose_pos hr
    have hq : ((classifier.acceptingQueries a).card : ℚ) ≤ coverCount :=
      ((div_le_iff₀ hpositive).mp (hquery a hd)).trans hcoverBudget
    have hmaxcard : (accepting a (maxResponse a)).card ≤ coverCount := by
      change (classifier.acceptingQueries a).card ≤ coverCount
      exact_mod_cast hq
    exact (hmax a response).trans hmaxcard

end Ligero.V1
