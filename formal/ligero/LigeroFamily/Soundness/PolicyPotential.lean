import LigeroFamily.Soundness.PolicyProfiledMaster
import LigeroFamily.Soundness.PotentialProfile

/-!
# Agreement tails for extraction-failing responses

The existing doubly profiled classifier already carries two full tails:
selected-MCA proximity failures and arithmetic-label agreement.  Here they
bound the actual maximum accepting-coordinate count, level by level, before
any hard cutoff between the combination challenge and the query is chosen.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace LigeroFamily

open Finset LigeroFamily.AgreementProfile
open scoped Classical

variable {F Equations CheckedMask DirectMask Challenge Response : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable [Fintype CheckedMask] [DecidableEq CheckedMask]
variable [Fintype Challenge] [DecidableEq Challenge] [Nonempty Challenge]
variable {logicalWidth r w n nw nq e g profileDenominator failureDenominator : ℕ}
variable {C : MultiplicativeCode F r w n}
variable {layout : ConstraintLayout F logicalWidth w}
variable {policy : SchemeProtocolPolicy (Equations := Equations) C layout
  Challenge Response CheckedMask DirectMask nw nq 1}
variable {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}
variable {statement : ConstraintSystem F nw nq logicalWidth Equations}
variable {respond : Challenge → Response}
variable {failureProfile arithmeticProfile : AgreementProfile n}

namespace PolicyDoublyProfiledSoundnessClassifier

variable (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
  respond failureProfile arithmeticProfile profileDenominator failureDenominator e g)

/-- The full extraction-failure tail offered to a potential optimizer.  The
far-proximity baseline is the only level at which the profile is trivial. -/
def gradedTail (failureProfile arithmeticProfile : AgreementProfile n)
    (failureDenominator profileDenominator e g a : ℕ) : ℚ :=
  if a ≤ n - e - 1 then 1
  else min 1
    ((failureProfile.labelsAtLeast a : ℚ) / failureDenominator +
      (arithmeticProfile.labelsAtLeast (a - g) : ℚ) / profileDenominator)

/-- Above the common far-proximity cover, a failing response's available
coordinates come either from a selected-MCA exception or from an unchecked
arithmetic-mask label.  The latter retains its actual agreement level. -/
theorem responseAgreement_tail_subset (a : ℕ) (hbase : n - e - 1 < a) :
    tailSet classifier.responseAgreement a ⊆
      restrictedTailSet classifier.failure classifier.failureAgreement a ∪
        tailSet classifier.agreement (a - g) := by
  classical
  intro challenge hc
  have hca : a ≤ classifier.responseAgreement challenge :=
    (Finset.mem_filter.mp hc).2
  by_cases hf : challenge ∈ classifier.failure
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr
      ⟨hf, hca.trans (classifier.responseAgreement_le_failureAgreement challenge hf)⟩
  · apply Finset.mem_union_right
    have hcap := classifier.responseAgreement_le_goodCap challenge hf
    have hagr : a - g ≤ classifier.agreement challenge := by
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagr⟩

/-- A single full tail bound, with no chosen challenge/query threshold. -/
theorem responseAgreement_tail_le (a : ℕ)
    (ha : a ≤ n) (hbase : n - e - 1 < a)
    (hfailure : 0 < failureDenominator)
    (hprofile : 0 < profileDenominator) :
    ((tailSet classifier.responseAgreement a).card : ℚ) /
        Fintype.card Challenge ≤
      (failureProfile.labelsAtLeast a : ℚ) / failureDenominator +
        (arithmeticProfile.labelsAtLeast (a - g) : ℚ) / profileDenominator := by
  classical
  let bad := restrictedTailSet classifier.failure classifier.failureAgreement a
  let arith := tailSet classifier.agreement (a - g)
  have hcard : (tailSet classifier.responseAgreement a).card ≤ bad.card + arith.card :=
    (Finset.card_le_card (classifier.responseAgreement_tail_subset a hbase)).trans
      (by simpa only [bad, arith] using
        (Finset.card_union_le
          (restrictedTailSet classifier.failure classifier.failureAgreement a)
          (tailSet classifier.agreement (a - g))))
  have hbad := classifier.failureAgreement_density a ha
  have harith := classifier.agreement_density (a - g) (by omega)
  have hX : (0 : ℚ) < Fintype.card Challenge := by exact_mod_cast Fintype.card_pos
  have hB : (0 : ℚ) < failureDenominator := by exact_mod_cast hfailure
  have hA : (0 : ℚ) < profileDenominator := by exact_mod_cast hprofile
  have hbadQ : (bad.card : ℚ) / Fintype.card Challenge ≤
      (failureProfile.labelsAtLeast a : ℚ) / failureDenominator := by
    rw [div_le_div_iff₀ hX hB]
    exact_mod_cast (by simpa only [Nat.mul_comm] using hbad)
  have harithQ : (arith.card : ℚ) / Fintype.card Challenge ≤
      (arithmeticProfile.labelsAtLeast (a - g) : ℚ) / profileDenominator := by
    rw [div_le_div_iff₀ hX hA]
    exact_mod_cast (by simpa only [Nat.mul_comm] using harith)
  have hcardQ : ((tailSet classifier.responseAgreement a).card : ℚ) /
      Fintype.card Challenge ≤ (bad.card + arith.card : ℚ) / Fintype.card Challenge := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt hX)
  calc
    _ ≤ (bad.card + arith.card : ℚ) / Fintype.card Challenge := hcardQ
    _ = (bad.card : ℚ) / Fintype.card Challenge +
        (arith.card : ℚ) / Fintype.card Challenge := by
          rw [add_div]
    _ ≤ _ := add_le_add hbadQ harithQ

theorem responseAgreement_tail_le_graded (a : ℕ) (ha : a ≤ n)
    (hfailure : 0 < failureDenominator)
    (hprofile : 0 < profileDenominator) :
    ((tailSet classifier.responseAgreement a).card : ℚ) /
        Fintype.card Challenge ≤
      gradedTail failureProfile arithmeticProfile failureDenominator
        profileDenominator e g a := by
  classical
  by_cases hbase : a ≤ n - e - 1
  · simp only [gradedTail, hbase, ↓reduceIte]
    apply (div_le_one (by exact_mod_cast Fintype.card_pos)).mpr
    exact_mod_cast Finset.card_le_card (Finset.subset_univ _)
  · simp only [gradedTail, hbase, ↓reduceIte]
    apply le_min
    · apply (div_le_one (by exact_mod_cast Fintype.card_pos)).mpr
      exact_mod_cast Finset.card_le_card (Finset.subset_univ _)
    · exact classifier.responseAgreement_tail_le a ha (Nat.lt_of_not_ge hbase)
        hfailure hprofile

theorem mean_curve_le_graded
    (ψ : PotentialProfile.Curve n)
    (hfailure : 0 < failureDenominator)
    (hprofile : 0 < profileDenominator) :
    (∑ challenge : Challenge, ψ.value (classifier.responseAgreement challenge)) /
        Fintype.card Challenge ≤
      ∑ a ∈ range (n + 1), ψ.increment a *
        gradedTail failureProfile arithmeticProfile failureDenominator
          profileDenominator e g a := by
  apply ψ.mean_le_tail_sum classifier.responseAgreement
    classifier.responseAgreement_le
    (gradedTail failureProfile arithmeticProfile failureDenominator
      profileDenominator e g)
  intro a ha
  exact classifier.responseAgreement_tail_le_graded a ha hfailure hprofile

end PolicyDoublyProfiledSoundnessClassifier

end LigeroFamily
