import Lfzk.GradedCost
import Lfzk.SoundnessAudit
import Lfzk.ZkLigeroV1
import Ligero.V1.ResponseMass
import LigeroFamily.Soundness.ResponseMass
import Lfzk.LigeroPayloadDecode
import Lfzk.ResponsePairMass

/-!
# Exact response-mass arithmetic for the four v7 hash geometries

This file checks the arithmetic side of a grouped-response FS analysis. It
does not itself assert an FS theorem: that requires a compiler which charges
all distinct final-response hash inputs when their parent challenge is first
exposed. The analytic response-mass theorem is in
`LigeroFamily.Soundness.ResponseMass`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1ResponseMassV7

open Finset LigeroFamily LigeroFamily.PolicyDoublyProfiledSoundnessClassifier
  Lfzk.CertifiedV1

def row (i : Fin 4) : Row := Lfzk.SoundnessAudit.v7HashRow i

theorem row_valid (i : Fin 4) : (row i).Valid := by
  fin_cases i
  · exact v7Hash1_valid
  · exact v7Hash2_valid
  · exact v7Hash3_valid
  · exact v7Hash4_valid

def cutoff (R : Row) : ℕ := R.params.row.n - R.params.row.e - 1

def cover (R : Row) (a : ℕ) : ℚ :=
  hypergeometricRatio a R.params.row.n R.params.row.openings

def tail (R : Row) (a : ℕ) : ℚ :=
  gradedTail
    (R.params.row.failureProfileAt R.params.row.fieldSize)
    R.params.row.arithProfile
    (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
      R.params.row.fieldSize R.params.row.g)
    R.params.row.fieldSize R.params.row.e R.params.row.g a

/-- The exact query-cover mass above the far-proximity cutoff. -/
def highCurve (i : Fin 4) :
    LigeroFamily.PotentialProfile.Curve (row i).params.row.n where
  value a := if a ≤ cutoff (row i) then 0 else cover (row i) a
  zero := by simp
  nonneg := by
    intro a ha
    split_ifs
    · exact le_refl _
    · unfold cover hypergeometricRatio
      exact div_nonneg (by positivity) (by positivity)
  le_one := by
    intro a ha
    split_ifs
    · norm_num
    · unfold cover hypergeometricRatio
      have hquery : (row i).params.row.openings ≤
          (row i).params.row.n := by fin_cases i <;> native_decide
      apply (div_le_one (by exact_mod_cast Nat.choose_pos hquery)).mpr
      exact_mod_cast Nat.choose_le_choose _ ha
  mono := by
    intro a b hab hbn
    by_cases hac : a ≤ cutoff (row i)
    · by_cases hbc : b ≤ cutoff (row i)
      · simp [hac, hbc]
      · simp only [hac, hbc, ↓reduceIte]
        unfold cover hypergeometricRatio
        exact div_nonneg (by positivity) (by positivity)
    · have hbc : ¬ b ≤ cutoff (row i) := by omega
      simp only [hac, hbc, ↓reduceIte]
      unfold cover hypergeometricRatio
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast Nat.choose_le_choose _ hab) (by positivity)

/-- The weighted tail of the high-response cover. The packing count 18 is
valid at every agreement at least `cutoff + 1` for these four rows. -/
def highCost (i : Fin 4) : ℚ :=
  ∑ a ∈ range ((row i).params.row.n + 1),
    (highCurve i).increment a * tail (row i) a

/-- Low-response query cover plus the Johnson-packed high-response mass. -/
def density (i : Fin 4) : ℚ :=
  cover (row i) (cutoff (row i)) + 18 * highCost i

theorem hash1_density_le_118 : density 0 ≤ (1 : ℚ) / 2 ^ 118 := by
  native_decide

theorem hash2_density_le_118 : density 1 ≤ (1 : ℚ) / 2 ^ 118 := by
  native_decide

theorem hash3_density_le_118 : density 2 ≤ (1 : ℚ) / 2 ^ 118 := by
  native_decide

theorem hash4_density_le_118 : density 3 ≤ (1 : ℚ) / 2 ^ 118 := by
  native_decide

theorem hash_density_le_118 (i : Fin 4) :
    density i ≤ (1 : ℚ) / 2 ^ 118 := by
  fin_cases i
  · exact hash1_density_le_118
  · exact hash2_density_le_118
  · exact hash3_density_le_118
  · exact hash4_density_le_118

/-- The actual response interpolation dimension is `2*k`, so distinct
responses can agree at most `2*k-1` committed columns. Johnson packing gives
at most 18 high responses for every radius needed by the four hash rows. -/
theorem high_uniform_family_bound (i : Fin 4) (a : ℕ)
    (ha : cutoff (row i) + 1 ≤ a)
    (han : a ≤ (row i).params.row.n) :
    CodingTheory.UniformFamilyBound
      (row i).params.row.n a (2 * (row i).params.row.k - 1) 18 := by
  let R := row i
  let n := R.params.row.n
  let lambda := 2 * R.params.row.k - 1
  let lower := cutoff R + 1
  have ha' : lower ≤ a := ha
  have han' : a ≤ n := han
  have hlambda : lambda ≤ lower := by fin_cases i <;> native_decide
  have hlambdaStrict : lambda < lower := by fin_cases i <;> native_decide
  have hpositive : n * lambda < lower * lower := by
    fin_cases i <;> native_decide
  have hslope : n ≤ 19 * (2 * lower) := by
    fin_cases i <;> native_decide
  have hcertificate :
      n * (lower - lambda) < 19 * (lower * lower - n * lambda) := by
    fin_cases i <;> native_decide
  have hden0 : 0 < CodingTheory.InterleavedJohnson.denominator
      n (n - lambda) (n - lower) := by
    fin_cases i <;> native_decide
  have hbound : LigeroFamily.uncheckedAgreementListBound
      n lambda a ≤ 18 :=
    LigeroFamily.uncheckedAgreementListBound_le_of_lower
      n lambda lower a 18 hlambda ha han hpositive hslope hcertificate
  have hpack : CodingTheory.UniformFamilyBound n a lambda
      (LigeroFamily.uncheckedAgreementListBound n lambda a) := by
    apply LigeroFamily.uncheckedAgreementListBound_uniformFamilyBound
    · exact han'
    · omega
    · apply CodingTheory.InterleavedJohnson.denominator_pos_of_le
        (E₀ := n - lower)
      · exact Nat.sub_le_sub_left ha' n
      · exact Nat.sub_le n lower
      · exact hden0
  exact hpack.mono hbound

private theorem highCurve_increment_zero (i : Fin 4) (a : ℕ)
    (ha : a ≤ cutoff (row i)) : (highCurve i).increment a = 0 := by
  unfold LigeroFamily.PotentialProfile.Curve.increment
  by_cases hzero : a = 0
  · subst a
    simp [highCurve]
  · have hprev : a - 1 ≤ cutoff (row i) := by omega
    simp [highCurve, ha, hprev, hzero]

/-- Conditional V1 response-mass envelope at every v7 hash geometry. The
overlap and tail premises are separated so they can be discharged from the
concrete V1 protocol; the conclusion refers to the *same* checked `density`
as `hash_density_le_118`. -/
theorem mean_high_mass_le (i : Fin 4)
    {Challenge Response : Type*} [Fintype Challenge] [Nonempty Challenge]
    [Fintype Response] [DecidableEq Response]
    (good : Challenge → Response → Finset (Fin (row i).params.row.n))
    (maximum : Challenge → ℕ)
    (hmax : ∀ challenge response,
      (good challenge response).card ≤ maximum challenge)
    (hoverlap : ∀ challenge response other, response ≠ other →
      ((good challenge response) ∩ (good challenge other)).card ≤
        2 * (row i).params.row.k - 1)
    (htail : ∀ a ≤ (row i).params.row.n,
      ((LigeroFamily.AgreementProfile.tailSet maximum a).card : ℚ) /
        Fintype.card Challenge ≤ tail (row i) a) :
    (∑ challenge : Challenge, ∑ response : Response,
        (highCurve i).value (good challenge response).card) /
        Fintype.card Challenge ≤ 18 * highCost i := by
  have hlambda : 2 * (row i).params.row.k - 1 ≤ cutoff (row i) := by
    fin_cases i <;> native_decide
  have h := LigeroFamily.ResponseMass.mean_curve_le_of_overlap
    good maximum hmax hoverlap (highCurve i) (fun _ => 18)
      (tail (row i)) hlambda
      (fun a hcut ha => high_uniform_family_bound i a (by omega) ha)
      htail
  refine h.trans (le_of_eq ?_)
  unfold highCost
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hcut : a ≤ cutoff (row i)
  · simp [hcut, highCurve_increment_zero]
  · simp only [hcut, ↓reduceIte]
    ring

/-- The concrete V1 classifier and Reed–Solomon code discharge the mass
theorem's overlap, packing, and response-uniform tail premises at the v7
hash geometries. This remains an IOP mass statement until a grouped FS
compiler is proved. -/
theorem v7_v1_high_mass_le (i : Fin 4)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    {w nw nq : ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).params.row.fieldSize)
    (D : ReedSolomon.Domain F (row i).params.row.openings w
      (row i).params.row.n)
    (hkrow : (row i).params.row.openings + w = (row i).params.row.k)
    (oracle : Ligero.V1.Oracle F nw nq (row i).params.row.n 1)
    (statement : ConstraintSystem F nw nq w Equations) :
    let R := (row i).params.row
    let C := R.code ((row i).rowValid (row_valid i)) D hkrow
    let policy := Ligero.V1.potentialFailedPolicy
      (e := R.e) (g := R.g) C oracle
    (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
      ∑ response : Response F R.openings w R.n 1,
        (highCurve i).value
          (policyAcceptingCoordinates policy oracle statement
            challenge response).card) /
        Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤
      18 * highCost i := by
  let R := (row i).params.row
  have hvalid : R.Valid := (row i).rowValid (row_valid i)
  let C := R.code hvalid D hkrow
  obtain ⟨hk, hmin, ⟨presentation⟩⟩ := R.rsFacts hvalid D hkrow
  have hcond := R.result.lineConditions (R.parametersValid hvalid)
    hfield hmin presentation
  have mask := Ligero.Examples.Grid.V1Certificate.v1MaskRange
    R.certificate (R.kpos hvalid) (R.response_le hvalid)
    (R.maskValid hvalid) C hk
  have hlambda : 2 * C.k - 1 ≤ cutoff (row i) := by
    rw [hk]
    fin_cases i <;> native_decide
  have hpack (a : ℕ) (hcut : cutoff (row i) < a) (ha : a ≤ R.n) :
      CodingTheory.UniformFamilyBound R.n a (2 * C.k - 1) 18 := by
    rw [hk]
    exact high_uniform_family_bound i a (by omega) ha
  have hraw := Ligero.V1.scalarGap_response_mass_le
    (e := R.e) (g := R.g) (d := R.d)
    (outerBound := R.certificate.lineBound)
    (localBound := R.certificate.integratedLocalLineBound)
    (threshold := R.certificate.maskStart)
    (bound := R.certificate.maskBound)
    (cutoff := cutoff (row i)) (packing := fun _ => 18)
    C oracle statement hmin hcond
    (R.liftList_card_le hvalid D hkrow oracle) hrows mask
    (by rw [hk]; exact R.kpos hvalid)
    (highCurve i) hlambda hpack
  have hmean :
      (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
        ∑ response : Response F R.openings w R.n 1,
          (highCurve i).value
            (policyAcceptingCoordinates
              (Ligero.V1.potentialFailedPolicy
                (e := R.e) (g := R.g) C oracle)
              oracle statement challenge response).card) /
          Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤
        18 * highCost i := by
    calc
      _ ≤ ∑ a ∈ range (R.n + 1),
          (highCurve i).increment a *
            (if a ≤ cutoff (row i) then
              Fintype.card (Response F R.openings w R.n 1) else 18 : ℕ) *
            tail (row i) a := by
              simpa only [R, C, tail, Lfzk.LigeroV1Rows.Row.failureProfileAt,
                Lfzk.LigeroV1Rows.Row.arithProfile, hfield] using hraw
      _ = 18 * highCost i := by
          unfold highCost
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hcut : a ≤ cutoff (row i)
          · simp [hcut, highCurve_increment_zero]
          · simp only [hcut, ↓reduceIte]
            ring
  exact hmean

/-- The certified 118-bit *response-mass* envelope for the four v7 V1 hash
rows. The first term is the low-agreement query cover; the second is the
total high-response cover mass averaged over the combination challenge. -/
theorem v7_v1_response_mass_density_le_118 (i : Fin 4)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    {w nw nq : ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).params.row.fieldSize)
    (D : ReedSolomon.Domain F (row i).params.row.openings w
      (row i).params.row.n)
    (hkrow : (row i).params.row.openings + w = (row i).params.row.k)
    (oracle : Ligero.V1.Oracle F nw nq (row i).params.row.n 1)
    (statement : ConstraintSystem F nw nq w Equations) :
    let R := (row i).params.row
    let C := R.code ((row i).rowValid (row_valid i)) D hkrow
    let policy := Ligero.V1.potentialFailedPolicy
      (e := R.e) (g := R.g) C oracle
    cover (row i) (cutoff (row i)) +
      (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
        ∑ response : Response F R.openings w R.n 1,
          (highCurve i).value
            (policyAcceptingCoordinates policy oracle statement
              challenge response).card) /
          Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤
      (1 : ℚ) / 2 ^ 118 := by
  have hm := v7_v1_high_mass_le i hrows hfield D hkrow oracle statement
  have hd := hash_density_le_118 i
  unfold density at hd
  dsimp at hm ⊢
  linarith

/-- The same checked envelope for the four actual transmitted response
slices.  The distinct-node interpolation decoder is injective, so summing
over its hash inputs cannot cost more than the formal response-mass sum.
The node embeddings identify the runtime interpolation order with the
Reed--Solomon domain used by the IOP theorem. -/
theorem v7_v1_payload_mass_density_le_118 (i : Fin 4)
    {F : Type} {Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    {w nw nq : ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).params.row.fieldSize)
    (D : ReedSolomon.Domain F (row i).params.row.openings w
      (row i).params.row.n)
    (hkrow : (row i).params.row.openings + w = (row i).params.row.k)
    (baseNodes : Fin (row i).params.row.k ↪
      Position (row i).params.row.openings w (row i).params.row.n)
    (responseNodes : Fin (2 * (row i).params.row.k - 1) ↪
      Position (row i).params.row.openings w (row i).params.row.n)
    (oracle : Ligero.V1.Oracle F nw nq (row i).params.row.n 1)
    (statement : ConstraintSystem F nw nq w Equations) :
    let R := (row i).params.row
    let C := R.code ((row i).rowValid (row_valid i)) D hkrow
    let policy := Ligero.V1.potentialFailedPolicy
      (e := R.e) (g := R.g) C oracle
    let decode := Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes
      (by fin_cases i <;> native_decide : R.openings ≤ R.k)
      (by fin_cases i <;> native_decide : R.k ≤ 2 * R.k - 1)
    cover (row i) (cutoff (row i)) +
      (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
        ∑ payload : Lfzk.LigeroTranscriptInputs.ResponsePayload F
            R.k (2 * R.k - 1) R.openings,
          (highCurve i).value
            (policyAcceptingCoordinates policy oracle statement
              challenge (decode payload)).card) /
          Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤
      (1 : ℚ) / 2 ^ 118 := by
  let R := (row i).params.row
  have hrb : R.openings ≤ R.k := by fin_cases i <;> native_decide
  have hbd : R.k ≤ 2 * R.k - 1 := by fin_cases i <;> native_decide
  let decode := Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes hrb hbd
  have hcost (challenge : Ligero.V1.Challenge F nw nq 1 Equations)
      (response : Response F R.openings w R.n 1) :
      0 ≤ (highCurve i).value
        (policyAcceptingCoordinates
          (Ligero.V1.potentialFailedPolicy
            (e := R.e) (g := R.g)
            (R.code ((row i).rowValid (row_valid i)) D hkrow) oracle)
          oracle statement challenge response).card := by
    apply (highCurve i).nonneg
    have hcard := Finset.card_le_univ
      (policyAcceptingCoordinates
        (Ligero.V1.potentialFailedPolicy
          (e := R.e) (g := R.g)
          (R.code ((row i).rowValid (row_valid i)) D hkrow) oracle)
        oracle statement challenge response)
    simpa [R] using hcard
  have hmass (challenge : Ligero.V1.Challenge F nw nq 1 Equations) :
      (∑ payload : Lfzk.LigeroTranscriptInputs.ResponsePayload F
          R.k (2 * R.k - 1) R.openings,
        (highCurve i).value
          (policyAcceptingCoordinates
            (Ligero.V1.potentialFailedPolicy
              (e := R.e) (g := R.g)
              (R.code ((row i).rowValid (row_valid i)) D hkrow) oracle)
            oracle statement challenge (decode payload)).card) ≤
      ∑ response : Response F R.openings w R.n 1,
        (highCurve i).value
          (policyAcceptingCoordinates
            (Ligero.V1.potentialFailedPolicy
              (e := R.e) (g := R.g)
              (R.code ((row i).rowValid (row_valid i)) D hkrow) oracle)
            oracle statement challenge response).card :=
    Lfzk.LigeroPayloadDecode.payload_mass_le D baseNodes responseNodes
      hrb hbd _ (hcost challenge)
  have hnum := Finset.sum_le_sum
    (s := (Finset.univ : Finset (Ligero.V1.Challenge F nw nq 1 Equations)))
    (fun challenge _ => hmass challenge)
  have hden : (0 : ℚ) ≤
      Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) := by positivity
  have hbase := v7_v1_response_mass_density_le_118 i
    hrows hfield D hkrow oracle statement
  dsimp at hbase ⊢
  have hdiv := div_le_div_of_nonneg_right hnum hden
  linarith

end Lfzk.V1ResponseMassV7
