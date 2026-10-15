import LigeroFamily.Soundness.ScalarGapChecked
import LigeroFamily.Protocol.FiniteResponse
import Lfzk.LigeroRbr

/-! Response-uniform local challenge/query bounds for checked-mask Ligero policies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace LigeroFamily

open Finset CodingTheory ScalarGapExtraction
open scoped Classical

variable {F Equations CheckedMask DirectMask Challenge Response Tail : Type*}
variable {q r w n nw nq e g d outerBound cutoff : ℕ}
variable {localBound : ℕ → ℕ}
variable [Field F] [Fintype F] [DecidableEq F]
  [Fintype Equations] [DecidableEq Equations]
  [Fintype CheckedMask] [DecidableEq CheckedMask]
  [Fintype Challenge] [DecidableEq Challenge] [Nonempty Challenge]
  [Fintype Response] [Nonempty Response]
  [Fintype Tail] [DecidableEq Tail]
  [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]

/-- Checked-mask round-by-round bounds, with the response at each challenge
chosen to maximize its accepting-query count.  This covers the V2 and V3
arithmetic certificates without changing either protocol. -/
theorem checked_local_card_bounds
    (C : MultiplicativeCode F r w n)
    (layout : ConstraintLayout F q w)
    (policy : SchemeProtocolPolicy (Equations := Equations) C layout
      Challenge Response CheckedMask DirectMask nw nq 1)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (messages : SchemeLiftCandidate C oracle (e + g) → CoreMessages F nw nq q)
    (statement : ConstraintSystem F nw nq q Equations)
    (hfalse : ∀ candidate, ¬statement.Satisfies (messages candidate))
    (budget : ∀ candidate, ¬statement.Satisfies (messages candidate) →
      Nonempty (CheckedArithmeticBudget policy candidate statement cutoff))
    (extractor : SchemeExtractorPolicy policy Tail)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    {L : ℕ} (hcard : (univ : Finset (SchemeLiftCandidate C oracle (e + g))).card ≤ L)
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
        ((checkedAgreementProfile (Fintype.card F) L n cutoff).labelsAtLeast
          (arithmeticThreshold + 1) : ℚ) / Fintype.card F) *
        Fintype.card Challenge ≤ escapeCount)
    (hcoverBudget : hypergeometricRatio
        (max failureThreshold
          (max (n - e - 1) (min n (g + arithmeticThreshold)))) n r *
        (n.choose r) ≤ coverCount) :
    ∃ Doom : Challenge → Prop,
      (univ.filter fun a : Challenge => ¬Doom a).card ≤ escapeCount ∧
      ∀ a (response : Response), Doom a →
        (univ.filter fun query : QuerySet n r =>
          policy.accepts statement a response query
            (openSchemeOracle oracle query)).card ≤ coverCount := by
  classical
  let accepting (a : Challenge) (ρ : Response) :=
    (univ.filter fun query : QuerySet n r =>
      policy.accepts statement a ρ query (openSchemeOracle oracle query))
  let maxResponse (a : Challenge) : Response :=
    Classical.choose (Finset.exists_max_image (univ : Finset Response)
      (fun ρ => (accepting a ρ).card) univ_nonempty)
  have hmax (a : Challenge) (ρ : Response) :
      (accepting a ρ).card ≤ (accepting a (maxResponse a)).card :=
    (Classical.choose_spec (Finset.exists_max_image (univ : Finset Response)
      (fun ρ => (accepting a ρ).card) univ_nonempty)).2 ρ (mem_univ _)
  obtain ⟨certificate, hdensity⟩ :=
    (failingExtractor policy messages extractor)
      |>.exists_profiledPolicyLiftList_of_endpointOptimizedIntegratedLine_of_card
      (oracle := oracle) (respond := maxResponse) hmin conditions hcard
  obtain ⟨arithmetic⟩ :=
    checkedProfiledArithmeticCertificate policy messages certificate hmin
      (by have := conditions.outer.punctured.punctured_three_radius; omega) cutoff
      (checkedSpecial policy messages statement cutoff budget)
      (checkedSpecial_density policy messages statement cutoff budget)
      (fun candidate hns challenge hnot hc =>
        checkedSpecial_cover policy messages statement cutoff budget candidate hns
          challenge (maxResponse challenge) hnot hc)
  obtain ⟨classifier⟩ := arithmetic.doublyProfiledClassifier_nonempty
    (failureProfile := SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
      (Fintype.card F) n e g d outerBound localBound)
    (failureDenominator := SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
      (Fintype.card F) g)
    certificate hdensity
  let Doom := classifier.ProfiledDoomedAfter failureThreshold arithmeticThreshold
  refine ⟨Doom, ?_, ?_⟩
  · have hsubset : (univ.filter fun a : Challenge => ¬Doom a) ⊆
        classifier.profiledEscaping failureThreshold arithmeticThreshold := by
      intro a ha
      exact classifier.not_profiledDoomedAfter_mem_profiledEscaping (mem_filter.mp ha).2
    have hesc := classifier.profiledEscaping_density_le
      failureThreshold arithmeticThreshold hfailureThreshold harithmeticThreshold
      (Nat.mul_pos Fintype.card_pos
        (Nat.sub_pos_of_lt conditions.outer.punctured.field_large))
      Fintype.card_pos
    have hpositive : (0 : ℚ) < Fintype.card Challenge := by
      exact_mod_cast Fintype.card_pos
    have hq : ((classifier.profiledEscaping failureThreshold arithmeticThreshold).card : ℚ)
        ≤ escapeCount := (div_le_iff₀ hpositive).mp hesc |>.trans hescapeBudget
    exact (card_le_card hsubset).trans (by exact_mod_cast hq)
  · intro a response hd
    have hquery := classifier.query_density_le_of_profiledDoomedAfter
      failureThreshold arithmeticThreshold a hd
    have hpositive : (0 : ℚ) < n.choose r := by
      exact_mod_cast Nat.choose_pos hr
    have hq : ((classifier.acceptingQueries a).card : ℚ) ≤ coverCount :=
      ((div_le_iff₀ hpositive).mp hquery).trans hcoverBudget
    have hmaxcard : (accepting a (maxResponse a)).card ≤ coverCount := by
      have hnone := ScalarGapExtraction.extract_none_of_no_valid policy messages statement
        a (maxResponse a) hfalse
      have hsets : accepting a (maxResponse a) = classifier.acceptingQueries a := by
        ext query
        simp [accepting, PolicyDoublyProfiledSoundnessClassifier.acceptingQueries,
          failingPolicy, hnone]
      rw [hsets]
      exact_mod_cast hq
    exact (hmax a response).trans hmaxcard

end LigeroFamily
