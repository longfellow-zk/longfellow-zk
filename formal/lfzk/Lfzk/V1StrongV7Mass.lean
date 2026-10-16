import Lfzk.V1StrongHahnPacking
import Lfzk.V1PayloadResponseMass

/-! Certified graded extraction mass for transmitted v7 Ligero V1 payloads. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7Mass

open Finset LigeroFamily LigeroFamily.PolicyDoublyProfiledSoundnessClassifier
  Lfzk.V1StrongV7Numeric

theorem row_valid (i : Fin 4) : (row i).Valid := by
  fin_cases i
  · exact Lfzk.V1StrongV7Rows.hash1_valid
  · exact Lfzk.V1StrongV7Rows.hash2_valid
  · exact Lfzk.V1StrongV7Rows.hash3_valid
  · exact Lfzk.V1StrongV7Rows.hash4_valid

private theorem highCurve_increment_zero (i : Fin 4) (a : ℕ)
    (ha : a ≤ cutoff (row i)) : (highCurve i).increment a = 0 := by
  unfold PotentialProfile.Curve.increment
  by_cases hzero : a = 0
  · subst a
    simp [highCurve]
  · have hprev : a - 1 ≤ cutoff (row i) := by omega
    simp [highCurve, ha, hprev, hzero]

theorem v7_v1_payload_high_mass_le (i : Fin 4)
    {F : Type} {Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    {w nw nq : ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).fieldSize)
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (oracle : Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : ConstraintSystem F nw nq w Equations) :
    let R := row i
    let C := R.code (row_valid i) D hkrow
    let policy := Ligero.V1.potentialFailedPolicy
      (e := R.e) (g := R.g) C oracle
    let decode := Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes
      (by fin_cases i <;> native_decide : R.openings ≤ R.k)
      (by fin_cases i <;> native_decide : R.k ≤ 2 * R.k - 1)
    (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
      ∑ payload : Lfzk.LigeroTranscriptInputs.ResponsePayload F
          R.k (2 * R.k - 1) R.openings,
        (highCurve i).value
          (policyAcceptingCoordinates policy oracle statement
            challenge (decode payload)).card) /
        Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤
      highMass i := by
  let R := row i
  have hvalid : R.Valid := row_valid i
  have hrb : R.openings ≤ R.k := by fin_cases i <;> native_decide
  have hbd : R.k ≤ 2 * R.k - 1 := by fin_cases i <;> native_decide
  let C := R.code hvalid D hkrow
  obtain ⟨hk, hmin, ⟨presentation⟩⟩ := R.rsFacts hvalid D hkrow
  have hcond := R.result.lineConditions (R.parametersValid hvalid)
    hfield hmin presentation
  have mask := Ligero.Examples.Grid.V1Certificate.v1MaskRange
    R.certificate (R.kpos hvalid) (R.response_le hvalid)
    (R.maskValid hvalid) C hk
  have hlambda : (2 * R.k - 1) - 1 ≤ cutoff R := by
    fin_cases i <;> native_decide
  have hpack (a : ℕ) (hcut : cutoff R < a) (ha : a ≤ R.n) :
      CodingTheory.UniformFamilyBound R.n a ((2 * R.k - 1) - 1)
        (responsePacking i a) := by
    have h := Lfzk.V1StrongHahnPacking.response_packing i a hcut ha
    simpa only [R, Nat.sub_sub] using h
  have hraw := Lfzk.V1PayloadResponseMass.scalarGap_payload_response_mass_le
    (cutoff := cutoff R)
    D baseNodes responseNodes hrb hbd C oracle statement R.e R.g
    hmin hcond (R.liftList_card_le hvalid D hkrow oracle)
    hrows mask (highCurve i) (responsePacking i) hlambda hpack
  have hmean :
      (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
        ∑ payload : Lfzk.LigeroTranscriptInputs.ResponsePayload F
            R.k (2 * R.k - 1) R.openings,
          (highCurve i).value
            (policyAcceptingCoordinates
              (Ligero.V1.potentialFailedPolicy
                (e := R.e) (g := R.g) C oracle)
              oracle statement challenge
              (Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes
                hrb hbd payload)).card) /
          Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤
        highMass i := by
    calc
      _ ≤ ∑ a ∈ range (R.n + 1),
          (highCurve i).increment a *
            (if a ≤ cutoff R then
              Fintype.card (Lfzk.LigeroTranscriptInputs.ResponsePayload
                F R.k (2 * R.k - 1) R.openings)
            else responsePacking i a : ℕ) * tail R a := by
              simpa only [R, C, tail, hfield,
                Lfzk.LigeroV1Rows.Row.failureProfileAt,
                Lfzk.LigeroV1Rows.Row.arithProfile,
                Lfzk.LigeroV1Rows.Row.result,
                Ligero.Examples.Grid.LongfellowProfiledExtraction.Result.localBound] using hraw
      _ = highMass i := by
          unfold highMass
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hcut : a ≤ cutoff R
          · have hzero : (highCurve i).increment a = 0 :=
              highCurve_increment_zero i a (by simpa only [R] using hcut)
            simp [hcut, hzero]
          · simp only [hcut, ↓reduceIte, R]
  exact hmean

theorem v7_v1_payload_density_lt_six (i : Fin 4)
    {F : Type} {Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    {w nw nq : ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).fieldSize)
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (oracle : Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : ConstraintSystem F nw nq w Equations) :
    let R := row i
    let C := R.code (row_valid i) D hkrow
    let policy := Ligero.V1.potentialFailedPolicy
      (e := R.e) (g := R.g) C oracle
    let decode := Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes
      (by fin_cases i <;> native_decide : R.openings ≤ R.k)
      (by fin_cases i <;> native_decide : R.k ≤ 2 * R.k - 1)
    cover R (cutoff R) +
      (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
        ∑ payload : Lfzk.LigeroTranscriptInputs.ResponsePayload F
            R.k (2 * R.k - 1) R.openings,
          (highCurve i).value
            (policyAcceptingCoordinates policy oracle statement
              challenge (decode payload)).card) /
          Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) <
      (6 : ℚ) / 2 ^ 128 := by
  have hm := v7_v1_payload_high_mass_le i hrows hfield D hkrow
    baseNodes responseNodes oracle statement
  have hd := Lfzk.V1StrongV7Numeric.density_lt_six i
  unfold density at hd
  dsimp at hm ⊢
  linarith

end Lfzk.V1StrongV7Mass
