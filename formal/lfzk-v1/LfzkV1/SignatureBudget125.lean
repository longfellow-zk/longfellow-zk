import LfzkV1.GradedSignature
import LfzkV1.RbrZkPotentialSide
import LfzkV1.NizkDeployedHashTwoField

/-!
# V7 signature budget in the 125-bit analysis

The signature side keeps its Hahn/Delsarte cutoff and uses the existing
extraction-first point charge. The replay and query comparisons are uniform
over the combined challenge alphabet.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

namespace LfzkV1.SignatureBudget125

open Finset LfzkV1.CertifiedV1 LfzkV1.NizkZk LfzkV1.RbrZkFlat
open scoped Classical
open LfzkV1.NizkDeployedHash LfzkV1.NizkDeployedHashTwoField

private theorem maskTail_eq :
    v7SigHahn.params.row.arith = (1176083737554874 : ℚ) / LigeroV1Rows.p256Order := by
  let cert := v7SigHahn.params.row.certificate
  have hthreshold : 1665 < cert.v1Threshold := by
    change 1665 < Nat.sqrt (3187 * (2 * 455 - 1)) + 1
    have h : 1665 ≤ Nat.sqrt (3187 * (2 * 455 - 1)) := Nat.le_sqrt.mpr (by decide)
    omega
  have hbound : cert.maskBound 1665 = 588041868777437 := by
    unfold Ligero.Examples.Grid.Certificate.maskBound
    rw [if_neg (Nat.not_le.mpr hthreshold)]
    exact RuntimeHahn.LigeroV7Sig.count_eq
  have hlabels : v7SigHahn.params.row.arithProfile.labelsAtLeast 1665 = 1176083737554874 := by
    unfold LigeroV1Rows.Row.arithProfile LigeroFamily.maskAgreementProfile
    change (if 3187 < 1665 then 0 else if 1665 < 1665 then LigeroV1Rows.p256Order
      else 2 * cert.maskBound 1665) = _
    rw [if_neg (by decide), if_neg (by decide), hbound]
  unfold LigeroV1Rows.Row.arith
  change ((v7SigHahn.params.row.arithProfile.labelsAtLeast 1665 : ℕ) : ℚ) /
    LigeroV1Rows.p256Order = _
  rw [hlabels]
  rfl

private theorem failureTail_le :
    v7SigHahn.params.row.fail ≤ (8726581 : ℚ) / ((LigeroV1Rows.p256Order : ℚ) - 1) := by
  let p := LigeroV1Rows.p256Order
  have hlabels : (v7SigHahn.params.row.failureProfileAt p).labelsAtLeast 1665 ≤ p * 8726581 := by
    unfold LigeroV1Rows.Row.failureProfileAt
      LigeroFamily.SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
      LigeroFamily.SchemeSelectedMCA.endpointOptimizedProfile
      LigeroFamily.SchemeSelectedMCA.selectedMCAIntegratedFailureProfile
    have hn : (1665 : ℕ) ≠ v7SigHahn.params.row.n := by decide
    have hi : v7SigHahn.params.row.n - v7SigHahn.params.row.e ≤ 1665 ∧
        1665 ≤ v7SigHahn.params.row.n := by decide
    dsimp only
    rw [if_neg hn, if_pos hi]
    apply Nat.mul_le_mul_left
    apply min_le_of_left_le
    unfold LigeroFamily.SchemeSelectedMCA.selectedMCAFailureProfile
    dsimp only
    rw [if_neg (show ¬v7SigHahn.params.row.n < 1665 by decide),
      if_neg (show ¬3 * (v7SigHahn.params.row.n - 1665) < v7SigHahn.params.row.d by decide)]
    decide
  have hp : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by decide)
  have hmul : (0 : ℚ) < (p : ℚ) * ((p : ℚ) - 1) := by positivity
  unfold LigeroV1Rows.Row.fail
  change (((v7SigHahn.params.row.failureProfileAt p).labelsAtLeast 1665 : ℕ) : ℚ) /
    ((p * (p - 1) : ℕ) : ℚ) ≤ _
  rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ p by decide), Nat.cast_one]
  have hcast : (((v7SigHahn.params.row.failureProfileAt p).labelsAtLeast 1665 : ℕ) : ℚ) ≤
      (p : ℚ) * 8726581 := by exact_mod_cast hlabels
  calc
    _ ≤ ((p : ℚ) * 8726581) / ((p : ℚ) * ((p : ℚ) - 1)) :=
      div_le_div_of_nonneg_right hcast hmul.le
    _ = _ := by
      change ((p : ℚ) * 8726581) / ((p : ℚ) * ((p : ℚ) - 1)) =
        8726581 / ((p : ℚ) - 1)
      field_simp [ne_of_gt (sub_pos.mpr hp), ne_of_gt (show 0 < (p : ℚ) from zero_lt_one.trans hp)]

private theorem cover_eq : v7SigHahn.params.row.cover =
    ((Nat.descFactorial 1664 132 / Nat.factorial 132 : ℕ) : ℚ) /
    ((Nat.descFactorial 3187 132 / Nat.factorial 132 : ℕ) : ℚ) := by
  change ((Nat.choose 1664 132 : ℕ) : ℚ) / ((Nat.choose 3187 132 : ℕ) : ℚ) = _
  rw [Nat.choose_eq_descFactorial_div_factorial, Nat.choose_eq_descFactorial_div_factorial]

set_option maxHeartbeats 2000000 in
/-- The registered Hahn signature core covers all its appended replay slots. -/
theorem replayDensity_le :
    zkCoreAt v7SigHahn 8 v7SigHahn.cardCand ≤ (1426 : ℚ) / (1000 * 2^128) := by
  have hcount : v7SigHahn.params.totalRounds = 542 := by decide
  unfold zkCoreAt LfzkV1.CostV1.Params.ligeroDensity zkFieldDensity
  rw [hcount, maskTail_eq, cover_eq]
  refine le_trans (add_le_add_right (add_le_add_left (add_le_add_left failureTail_le _) _) _) ?_
  change (2 : ℚ) * (1295 / LigeroV1Rows.p256Order) +
    (8726581 / ((LigeroV1Rows.p256Order : ℚ) - 1) +
    1176083737554874 / LigeroV1Rows.p256Order + _) ≤ _
  decide +kernel

theorem searchDensity_le :
    v7SigHahn.zkCoefficient 8 ≤ (1426 : ℚ) / (1000 * 2^128) := by
  apply le_trans _ replayDensity_le
  unfold Row.zkCoefficient zkMaxDensityAt zkCoreAt zkFieldDensity
  have hf : (0 : ℚ) ≤ v7SigHahn.params.row.fieldSize := Nat.cast_nonneg _
  have hl : (1 : ℚ) ≤ v7SigHahn.params.nl := by decide
  have hrounds : (0 : ℚ) ≤ v7SigHahn.params.totalRounds := Nat.cast_nonneg _
  have hc : (0 : ℚ) ≤ v7SigHahn.cardCand := Nat.cast_nonneg _
  have hfail := LigeroV1LayerStep.fail_nonneg v7SigHahn.params.row
  have harith := LigeroV1LayerStep.arith_nonneg v7SigHahn.params.row
  have hcover := LigeroV1LayerStep.cover_nonneg v7SigHahn.params.row
  have hfield : (↑v7SigHahn.cardCand : ℚ) * (↑(8 + 2 : ℕ) / ↑v7SigHahn.params.row.fieldSize)
      ≤ (v7SigHahn.cardCand : ℚ) *
        (↑(v7SigHahn.params.nl * (8 + 2) + 2 * v7SigHahn.params.totalRounds + 1 : ℕ) /
          (v7SigHahn.params.row.fieldSize : ℚ)) := by
    apply mul_le_mul_of_nonneg_left _ hc
    apply div_le_div_of_nonneg_right _ hf
    have hn : 1 ≤ v7SigHahn.params.nl := by exact_mod_cast hl
    exact_mod_cast (show 8 + 2 ≤ v7SigHahn.params.nl * (8 + 2) +
      2 * v7SigHahn.params.totalRounds + 1 by omega)
  have hfield0 : 0 ≤ (v7SigHahn.cardCand : ℚ) * (↑(8 + 2 : ℕ) /
      ↑v7SigHahn.params.row.fieldSize) := mul_nonneg hc (div_nonneg (Nat.cast_nonneg _) hf)
  rw [show 2 * v7SigHahn.params.totalRounds = v7SigHahn.params.totalRounds * 2 by omega] at hfield
  refine max_le (max_le ?_ ?_) ?_
  all_goals change _ ≤ _ + ((v7SigHahn.params.row.fail + v7SigHahn.params.row.arith) +
      v7SigHahn.params.row.cover)
  all_goals linarith


/-- Context-independent local weights for the signature side, in number of
combined oracle answers. Each terminal slot uses its registered bound. -/
noncomputable def roleBudget (C : Type) [Fintype C]
    (rl : Rounds.Role v7SigHahn.params.nl v7SigHahn.params.rounds) : ℚ :=
  sideUniformRoleBudget (R := v7SigHahn) (logv := 8) (C := C)
    ((Fintype.card C : ℚ) * (v7SigHahn.params.row.fail + v7SigHahn.params.row.arith))
    ((Fintype.card C : ℚ) * v7SigHahn.params.row.cover) rl

theorem roleBudget_nonneg (C : Type) [Fintype C]
    (rl : Rounds.Role v7SigHahn.params.nl v7SigHahn.params.rounds) :
    0 ≤ roleBudget C rl := by
  have hf := LigeroV1LayerStep.fail_nonneg v7SigHahn.params.row
  have ha := LigeroV1LayerStep.arith_nonneg v7SigHahn.params.row
  have hq := LigeroV1LayerStep.cover_nonneg v7SigHahn.params.row
  unfold roleBudget sideUniformRoleBudget
  split_ifs
  · exact Nat.cast_nonneg _
  · exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg hf ha)
  · exact mul_nonneg (Nat.cast_nonneg _) hq

/-- An adversarial signature query pays at most (1.426/2^{128}), well
inside the shared original-query cap. -/
theorem roleBudget_le (C : Type) [Fintype C] [Nonempty C]
    (rl : Rounds.Role v7SigHahn.params.nl v7SigHahn.params.rounds) :
    roleBudget C rl ≤ (Fintype.card C : ℚ) * ((1426 : ℚ) / (1000 * 2^128)) := by
  unfold roleBudget
  apply (sideUniformRoleBudget_le_max _ _ rl).trans
  have hfield : 0 < v7SigHahn.params.row.fieldSize := by decide
  have hb := mul_le_mul_of_nonneg_left searchDensity_le
    (Nat.cast_nonneg (Fintype.card C) : (0 : ℚ) ≤ Fintype.card C)
  refine max_le ?_ (max_le ?_ ?_)
  · exact (sideFieldMaxBudget_le_density v7SigHahn 8 _ Fintype.card_pos hfield).trans hb
  · apply le_trans _ hb
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact (le_max_right _ _).trans (le_max_left _ _)
  · apply le_trans _ hb
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact le_max_right _ _

/-- The entire signature verifier's appended replay pays at most
(1.426/2^{128}), independently of the adversary's reveal order. -/
theorem roleBudget_sum_le (C : Type) [Fintype C] :
    (∑ i : Fin (Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds),
      roleBudget C (Rounds.Role.indexEquiv.symm i))
      ≤ (Fintype.card C : ℚ) * ((1426 : ℚ) / (1000 * 2^128)) := by
  unfold roleBudget
  rw [sideUniformRoleBudget_sum]
  apply le_trans _ (mul_le_mul_of_nonneg_left replayDensity_le (Nat.cast_nonneg _))
  have hf : 0 < v7SigHahn.params.row.fieldSize := by decide
  have hfield := sideFieldSlotBudget_le_density v7SigHahn 8 (Fintype.card C) hf
  unfold zkCoreAt LfzkV1.CostV1.Params.ligeroDensity
  nlinarith


private theorem curve_value (a : ℕ) :
    LfzkV1.GradedSignature.curve.value a = if 1665 ≤ a then 1 else 0 := by
  unfold LfzkV1.GradedSignature.curve LigeroFamily.PotentialProfile.stepCurve
    LigeroFamily.PotentialProfile.weightedStepCurve
  change (∑ _j ∈ ({1665} : Finset ℕ), if 1665 ≤ a then (1 : ℚ) else 0) = _
  simp only [sum_singleton]

private theorem curve_increment (a : ℕ) :
    LfzkV1.GradedSignature.curve.increment a = if a = 1665 then 1 else 0 := by
  unfold LigeroFamily.PotentialProfile.Curve.increment
  rw [curve_value, curve_value]
  split_ifs <;> first | omega | apply sub_self | apply sub_zero

theorem curve_challenge_le :
    LfzkV1.GradedCost.challenge v7SigHahn LfzkV1.GradedSignature.curve ≤
      v7SigHahn.params.row.fail + v7SigHahn.params.row.arith := by
  change LfzkV1.GradedCost.challenge LfzkV1.GradedSignature.row LfzkV1.GradedSignature.curve ≤ _
  unfold LfzkV1.GradedCost.challenge
  simp only [curve_increment, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_range, if_pos (show (1665 : ℕ) < LfzkV1.GradedSignature.row.params.row.n + 1 by decide)]
  unfold LigeroFamily.PolicyDoublyProfiledSoundnessClassifier.gradedTail
  rw [if_neg (show ¬(1665 : ℕ) ≤ LfzkV1.GradedSignature.row.params.row.n - LfzkV1.GradedSignature.row.params.row.e - 1 by decide)]
  have hcut₁ : LfzkV1.GradedSignature.row.params.row.failureThreshold + 1 = 1665 := rfl
  have hcut₂ : LfzkV1.GradedSignature.row.params.row.arithmeticThreshold + 1 = 1665 := rfl
  have hg : 1665 - LfzkV1.GradedSignature.row.params.row.g = 1665 := rfl
  change _ ≤ LfzkV1.GradedSignature.row.params.row.fail + LfzkV1.GradedSignature.row.params.row.arith
  unfold LigeroV1Rows.Row.fail LigeroV1Rows.Row.arith
    Ligero.Examples.Grid.Certificate.optimizedFailureDenominator
  rw [hcut₁, hcut₂, hg]
  apply min_le_right

theorem curve_query_le :
    LfzkV1.GradedCost.query v7SigHahn LfzkV1.GradedSignature.curve ≤ v7SigHahn.params.row.cover := by
  unfold LfzkV1.GradedCost.query LigeroFamily.PotentialProfile.Curve.queryCost
  apply Finset.sup'_le
  intro a _
  rw [curve_value]
  by_cases ha : 1665 ≤ a
  · rw [if_pos ha, sub_self, zero_mul]
    exact LigeroV1LayerStep.cover_nonneg _
  · rw [if_neg ha, sub_zero, one_mul]
    unfold LigeroV1Rows.Row.cover LigeroFamily.hypergeometricRatio
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (Nat.choose_le_choose _ (show a ≤ v7SigHahn.params.row.queryCover from
      show a ≤ 1664 by omega))

open Merkle.MH LfzkV1.CompiledZk
open LfzkV1.CompiledLongfellow (Col)
open LfzkV1.CompiledLongfellowAdaptive (Sig)
open LfzkV1.NizkZkDeployedHash LfzkV1.RbrZkSplit RbrLongfellow

abbrev PairPoint (D C X Msg₁ Msg : Type) (R₁ : Row) :=
  Pt2 D C X Msg₁ Msg R₁.params.nl v7SigHahn.params.nl
    R₁.params.rounds v7SigHahn.params.rounds

end LfzkV1.SignatureBudget125
