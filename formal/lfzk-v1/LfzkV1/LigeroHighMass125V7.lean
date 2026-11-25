import LfzkV1.LigeroHighMass125Numeric
import LfzkV1.OpeningGeometry125

/-!
# High-response charges for the four v7 hash rows

The only changes from the deployed geometry are the analysis parameters
of the selected-MCA certificate. The high cutoff reuses the lower
agreement boundary of the existing Hahn certificate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LfzkV1.LigeroHighMass125

open Finset LigeroFamily LigeroFamily.AgreementProfile
open CodingTheory MultiplicativeCode
open Ligero.Examples.Grid (Certificate)
open Ligero.Examples.Grid.LongfellowProfiledExtraction

private abbrev cert (i : Fin 4) : Certificate := (OpeningGeometry125.result i).certificate

def highCutoff (i : Fin 4) : ℕ := (cert i).maskStart + (cert i).g

private def listLimit (i : Fin 4) : ℕ := (cert i).maskBound (cert i).maskStart

private theorem listLimit_eq (i : Fin 4) :
    listLimit i = match i.val with
      | 0 => 373060227302109379
      | 1 => 630186550899334576
      | 2 => 1217672935453862521
      | _ => 11617883720936895477 := by
  simp only [listLimit, Certificate.maskBound, uncheckedAgreementListBound,
    HahnDelsarte.certifiedBound, HahnDelsarte.certificatePolynomial, HahnDelsarte.hahnKernel,
    HahnDelsarte.hahnWeight, Nat.choose_eq_fast_choose]
  fin_cases i <;> decide +kernel

private theorem exact_numerator_check (i : Fin 4) :
    let c := cert i
    100 * highMassNumerator c.fieldSize c.n c.k c.d c.g c.openings (highCutoff i)
      (listLimit i) c.lineBound (OpeningGeometry125.result i).failureProfile ≤
      319 * c.n.choose c.openings * (c.fieldSize - (c.g + 1)) := by
  have hroute : (OpeningGeometry125.result i).route = .triples := by fin_cases i <;> rfl
  simp only [highMassNumerator, noLiftPeakNumerator, Result.failureProfile, Result.localBound,
    hroute, OpeningGeometry125.integratedLocalLineBound_eq, listLimit_eq,
    SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile,
    SchemeSelectedMCA.endpointOptimizedProfile,
    SchemeSelectedMCA.selectedMCAIntegratedFailureProfile,
    SchemeSelectedMCA.selectedMCAFailureProfile, Nat.choose_eq_fast_choose]
  fin_cases i <;> decide +kernel

theorem v7_highMassBound_le (i : Fin 4) :
    let c := cert i
    highMassBound c.fieldSize c.n c.k c.d c.g c.openings (highCutoff i)
      (listLimit i) c.optimizedFailureDenominator (OpeningGeometry125.result i).failureProfile ≤
      (319 : ℚ) / (100 * (2 ^ 128)) := by
  have hq := (OpeningGeometry125.deployedGeometry i).2.2.2
  rw [← show ((2 ^ 128 : ℕ) : ℚ) = (2 ^ 128 : ℚ) by norm_cast, ← hq]
  apply highMass_le_of_numerator_bound
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel
  · exact exact_numerator_check i

/-- Every agreement size below the Hahn-based cutoff has opening rate at
most 3.186 divided by the binary field size. -/
theorem v7_lowOpening_le (i : Fin 4) {b : ℕ} (hb : b < highCutoff i) :
    hypergeometricRatio b (cert i).n (cert i).openings ≤ (1593 : ℚ) / (500 * (2 ^ 128)) := by
  apply (opening_mono (show b ≤ highCutoff i - 1 by omega)).trans
  simp only [hypergeometricRatio, Nat.choose_eq_fast_choose]
  fin_cases i <;> decide +kernel

section V7

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {w nw nq : ℕ}
variable [Nonempty (SchemeTestedRow NoMask nw nq 1)]

/-- Actual average opening mass of every bad high response in the deployed
hash geometry, uniformly even when the same commitment admits a satisfying
lift for the statement. -/
theorem v7_badHigh_opening_mass_le (i : Fin 4)
    (C : MultiplicativeCode F (cert i).openings w (cert i).n)
    (oracle : Ligero.V1.Oracle F nw nq (cert i).n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (hfield : Fintype.card F = (cert i).fieldSize) (hk : C.k = (cert i).k)
    (hmin : HasMinimumDistanceAtLeast C.baseCode (cert i).d)
    (hRS : JBAgreement.RSPresentation (cert i).n (cert i).k C.baseCode) :
    let c := cert i
    let Challenge := SchemeChallenge F NoMask nw nq 1 Equations
    (∑ ch : Challenge,
      ∑ u ∈ badHighResponses (C := C) oracle statement (highCutoff i) c.e c.g ch,
        openingRate (C := C) oracle statement ch u) / Fintype.card Challenge ≤
      (319 : ℚ) / (100 * (2 ^ 128)) := by
  dsimp only
  classical
  let s := OpeningGeometry125.result i
  let c := cert i
  have hp : s.ParametersValid := OpeningGeometry125.parameters i
  have hconds := s.lineConditions hp hfield hmin hRS
  have hkpos : 0 < c.k := hp.1
  have hresponse : 2 * c.k ≤ c.n := hp.2.2.2.1
  have hmask : c.maskValid = true := by
    have hvar : s.variant = .v1 := OpeningGeometry125.variant i
    simpa only [hvar, if_true] using hp.2.2.2.2.1
  have hlarge : 2 * C.k - 1 < highCutoff i - c.g := by
    rw [hk]
    fin_cases i <;> decide +kernel
  have ha : c.n - c.e ≤ highCutoff i := by fin_cases i <;> decide +kernel
  have hfamily : UniformFamilyBound c.n (highCutoff i - c.g) (2 * C.k - 1) (listLimit i) := by
    rw [show highCutoff i - c.g = c.maskStart from Nat.add_sub_cancel _ _]
    exact (Ligero.Examples.Grid.V1Certificate.v1MaskRange c hkpos hresponse hmask C hk).family
      c.maskStart le_rfl (by fin_cases i <;> decide +kernel)
  have hlifts : Fintype.card (SchemeLiftCandidate C oracle (c.e + c.g)) ≤ 2 := by
    have hr : c.e + c.g < c.d := by fin_cases i <;> decide +kernel
    have hden : 0 < InterleavedJohnson.denominator c.n c.d (c.e + c.g) := by
      fin_cases i <;> decide +kernel
    have h := SchemeLiftCandidate.univ_card_le_uniformFamilyBound C oracle hmin hr
      (c.listFamily hr hmin.distance_le_length hden)
    rw [card_univ] at h
    exact h.trans (OpeningGeometry125.liftCount i)
  have hh := badHigh_average_mass_le oracle statement hmin hconds ha hlarge hfamily hlifts
  have hh' := hh.trans (by
    simpa only [hfield, hk, Result.failureProfile, Certificate.optimizedFailureDenominator]
      using v7_highMassBound_le i)
  exact (opening_average_le_agreement_average (C := C) oracle statement _).trans hh'

/-- When an opening query fixes the response before batching, low agreement
and bad high agreement together cost at most 6.376 divided by the field size. -/
theorem v7_fixed_bad_or_low_opening_le (i : Fin 4)
    (C : MultiplicativeCode F (cert i).openings w (cert i).n)
    (oracle : Ligero.V1.Oracle F nw nq (cert i).n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (hfield : Fintype.card F = (cert i).fieldSize) (hk : C.k = (cert i).k)
    (hmin : HasMinimumDistanceAtLeast C.baseCode (cert i).d)
    (hRS : JBAgreement.RSPresentation (cert i).n (cert i).k C.baseCode)
    (u : Response F (cert i).openings w (cert i).n 1) :
    let c := cert i
    let Challenge := SchemeChallenge F NoMask nw nq 1 Equations
    (∑ ch : Challenge,
      if (columns (C := C) oracle statement ch u).card < highCutoff i ∨
          u ∈ badHighResponses (C := C) oracle statement (highCutoff i) c.e c.g ch then
        openingRate (C := C) oracle statement ch u
      else 0) / Fintype.card Challenge ≤
      (3188 : ℚ) / (500 * (2 ^ 128)) := by
  dsimp only
  classical
  let Challenge := SchemeChallenge F NoMask nw nq 1 Equations
  let c := cert i
  let replies := badHighResponses (C := C) oracle statement (highCutoff i) c.e c.g
  let low : ℚ := (1593 : ℚ) / (500 * (2 ^ 128))
  have hlow : 0 ≤ low := by dsimp [low]; positivity
  letI : Nonempty Challenge := ⟨fun _ => ⟨0, 0, 0⟩⟩
  have hcount : (Fintype.card Challenge : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hlocal (ch : Challenge) :
      (if (columns (C := C) oracle statement ch u).card < highCutoff i ∨ u ∈ replies ch then
        openingRate (C := C) oracle statement ch u else 0) ≤
      low + (if u ∈ replies ch then openingRate (C := C) oracle statement ch u else 0) := by
    by_cases hbad : u ∈ replies ch
    · simp only [hbad, or_true, if_true]
      exact le_add_of_nonneg_left hlow
    · simp only [hbad, or_false, if_false, add_zero]
      split_ifs with h
      · exact (fixed_response_opening_density (C := C) oracle statement ch u).trans
          (v7_lowOpening_le i h)
      · exact hlow
  calc
    _ ≤ (∑ ch : Challenge,
        (low + (if u ∈ replies ch then openingRate (C := C) oracle statement ch u else 0))) /
        Fintype.card Challenge :=
      div_le_div_of_nonneg_right (sum_le_sum fun ch _ => hlocal ch) (by positivity)
    _ = low + (∑ ch : Challenge,
        (if u ∈ replies ch then openingRate (C := C) oracle statement ch u else 0)) /
        Fintype.card Challenge := by
      rw [sum_add_distrib, add_div]
      simp [hcount]
    _ ≤ low + (319 : ℚ) / (100 * (2 ^ 128)) := by
      apply add_le_add le_rfl
      exact (fixed_opening_average_le (C := C) oracle statement (replies := replies) u).trans
        (v7_badHigh_opening_mass_le i C oracle statement hfield hk hmin hRS)
    _ = _ := by norm_num [low]

end V7

end LfzkV1.LigeroHighMass125
