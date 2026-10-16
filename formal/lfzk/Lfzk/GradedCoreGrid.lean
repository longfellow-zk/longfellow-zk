import Lfzk.GradedV7Hash
import Lfzk.GradedV8Hash
import Lfzk.GradedSignature
import Lfzk.RbrZkPotentialTwoField

/-!
# Graded two-field density certificates

The density bounds apply to any balanced combined challenge alphabet.  The
adaptive arithmetic retains the deployed transcript-query and Merkle terms.
The compiled extraction theorem and its generic density comparison are
separate from these closed row checks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.GradedCoreGrid

open Lfzk.CertifiedV1 Lfzk.NizkZk

def v7Core (i : Fin 4) : ℚ :=
  let H := Lfzk.GradedV7Hash.row i
  (H.cardCand : ℚ) * zkFieldDensity H (Lfzk.SoundnessAudit.v7HashLogv i) +
    Lfzk.GradedV7Hash.challengeCost i + Lfzk.GradedV7Hash.queryCost i +
    (v7SigHahn.cardCand : ℚ) * zkFieldDensity v7SigHahn 8 +
    Lfzk.GradedSignature.challengeCost false +
    Lfzk.GradedSignature.queryCost false + (4 : ℚ) / 2 ^ 128

def v8Core : ℚ :=
  (v8Hash.cardCand : ℚ) * zkFieldDensity v8Hash 5 +
    Lfzk.GradedV8Hash.challengeCost + Lfzk.GradedV8Hash.queryCost +
    (v8Sig.cardCand : ℚ) * zkFieldDensity v8Sig 3 +
    Lfzk.GradedSignature.challengeCost true +
    Lfzk.GradedSignature.queryCost true + (4 : ℚ) / 2 ^ 128

/-- The four v7 two-field constant cores fit within 115 bits. -/
theorem v7Core_le_115 (i : Fin 4) :
    v7Core i ≤ (1 : ℚ) / 2 ^ 115 := by
  have hh := Lfzk.GradedV7Hash.terminalCost_le i
  have hs := Lfzk.GradedSignature.terminalCost_le_registered false
  have hn :
      let H := Lfzk.GradedV7Hash.row i
      (H.cardCand : ℚ) * zkFieldDensity H (Lfzk.SoundnessAudit.v7HashLogv i) +
        (Lfzk.GradedV7Hash.terminalNumerator i : ℚ) / 2 ^ 128 +
        (v7SigHahn.cardCand : ℚ) * zkFieldDensity v7SigHahn 8 +
        v7SigHahn.params.ligeroDensity + (4 : ℚ) / 2 ^ 128 ≤
          (1 : ℚ) / 2 ^ 115 := by
    fin_cases i <;> native_decide
  change Lfzk.GradedSignature.challengeCost false +
      Lfzk.GradedSignature.queryCost false ≤
        v7SigHahn.params.ligeroDensity at hs
  dsimp only at hn
  dsimp only [v7Core]
  linarith

/-- The v8 two-field constant core also fits within 115 bits. -/
theorem v8Core_le_115 : v8Core ≤ (1 : ℚ) / 2 ^ 115 := by
  have hh := Lfzk.GradedV8Hash.terminalCost_le
  have hs := Lfzk.GradedSignature.terminalCost_le_registered true
  have hn :
      (v8Hash.cardCand : ℚ) * zkFieldDensity v8Hash 5 +
        (2938 : ℚ) / 2 ^ 128 +
        (v8Sig.cardCand : ℚ) * zkFieldDensity v8Sig 3 +
        v8Sig.params.ligeroDensity + (4 : ℚ) / 2 ^ 128 ≤
          (1 : ℚ) / 2 ^ 115 := by
    native_decide
  change Lfzk.GradedSignature.challengeCost true +
      Lfzk.GradedSignature.queryCost true ≤ v8Sig.params.ligeroDensity at hs
  dsimp only [v8Core]
  linarith

/-- Alphabet-independent density upper bound for the four v7 pairs. -/
def v7DensityUpper (i : Fin 4) : ℚ :=
  let H := Lfzk.GradedV7Hash.row i
  (4 : ℚ) / 2 ^ 128 +
    (H.cardCand : ℚ) * zkFieldDensity H
      (Lfzk.SoundnessAudit.v7HashLogv i) +
    (Lfzk.GradedV7Hash.challengeNumerator i : ℚ) / 2 ^ 128 +
    (Lfzk.GradedV7Hash.queryNumerator i : ℚ) / 2 ^ 128 +
    (v7SigHahn.cardCand : ℚ) * zkFieldDensity v7SigHahn 8 +
    v7SigHahn.params.row.fail + v7SigHahn.params.row.arith +
    v7SigHahn.params.row.cover

def v8DensityUpper : ℚ :=
  (4 : ℚ) / 2 ^ 128 +
    (v8Hash.cardCand : ℚ) * zkFieldDensity v8Hash 5 +
    (1804 : ℚ) / 2 ^ 128 + (1134 : ℚ) / 2 ^ 128 +
    (v8Sig.cardCand : ℚ) * zkFieldDensity v8Sig 3 +
    v8Sig.params.row.fail + v8Sig.params.row.arith +
    v8Sig.params.row.cover

theorem v7DensityUpper_le_115 (i : Fin 4) :
    v7DensityUpper i ≤ (1 : ℚ) / 2 ^ 115 := by
  fin_cases i <;> native_decide

theorem v8DensityUpper_le_115 :
    v8DensityUpper ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- The graded tails remain below the registered worst-slot coefficient,
which is the premise of the alphabet-independent maximum theorem. -/
theorem v7GradedCosts_le_coefficient (i : Fin 4) :
    let H := Lfzk.GradedV7Hash.row i
    (Lfzk.GradedV7Hash.challengeNumerator i : ℚ) / 2 ^ 128 ≤
      H.zkCoefficient (Lfzk.SoundnessAudit.v7HashLogv i) ∧
    (Lfzk.GradedV7Hash.queryNumerator i : ℚ) / 2 ^ 128 ≤
      H.zkCoefficient (Lfzk.SoundnessAudit.v7HashLogv i) ∧
    v7SigHahn.params.row.fail + v7SigHahn.params.row.arith ≤
      v7SigHahn.zkCoefficient 8 ∧
    v7SigHahn.params.row.cover ≤ v7SigHahn.zkCoefficient 8 := by
  fin_cases i <;> native_decide

theorem v8GradedCosts_le_coefficient :
    (1804 : ℚ) / 2 ^ 128 ≤ v8Hash.zkCoefficient 5 ∧
    (1134 : ℚ) / 2 ^ 128 ≤ v8Hash.zkCoefficient 5 ∧
    v8Sig.params.row.fail + v8Sig.params.row.arith ≤
      v8Sig.zkCoefficient 3 ∧
    v8Sig.params.row.cover ≤ v8Sig.zkCoefficient 3 := by
  native_decide

/-- The alphabet-independent v7 constant fits under the previously
certified adaptive-hash arithmetic envelope. -/
theorem v7DensityUpper_le_registered (i : Fin 4) :
    let H := Lfzk.GradedV7Hash.row i
    v7DensityUpper i ≤
      zkCoreAt H (Lfzk.SoundnessAudit.v7HashLogv i) H.cardCand +
      zkCoreAt v7SigHahn 8 v7SigHahn.cardCand + (4 : ℚ) / 2 ^ 128 := by
  fin_cases i <;> native_decide

/-- The alphabet-independent v8 constant and registered worst-slot
coefficient leave room for the adaptive Merkle term at 115 bits. -/
theorem v8DensityLinearSlack :
    let fc := 2 * v8Sig.params.row.n + 2 * v8Hash.params.row.n
    let L := Lfzk.NizkAdaptiveTwoField.len2 v8Hash v8Sig
    let K := max (max (v8Hash.zkCoefficient 5)
      (v8Sig.zkCoefficient 3)) ((4 : ℚ) / 2 ^ 128)
    v8DensityUpper +
        2 * ((fc * (1 + L) : ℕ) : ℚ) / 2 ^ 256 ≤
      (1 : ℚ) / 2 ^ 115 ∧
    K + 2 * ((fc + 2 ^ 115 : ℕ) : ℚ) / 2 ^ 256 ≤
      (1 : ℚ) / 2 ^ 115 ∧
    2 * ((3 * 2 ^ 115 + 2 * fc + 1 + L : ℕ) : ℚ) / 2 ^ 256 ≤
      (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- Full v7 density arithmetic with the deployed adaptive Merkle term. -/
theorem v7DensityRhs_le_115 (i : Fin 4) (N tA : ℕ)
    (htA : tA ≤ 2 ^ 115) :
    let H := Lfzk.GradedV7Hash.row i
    let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
    let L := Lfzk.NizkAdaptiveTwoField.len2 H v7SigHahn
    let K := max (max (H.zkCoefficient
      (Lfzk.SoundnessAudit.v7HashLogv i))
      (v7SigHahn.zkCoefficient 8)) ((4 : ℚ) / 2 ^ 128)
    v7DensityUpper i + N * K +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
        2 ^ 256 ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  dsimp only
  have hc := v7DensityUpper_le_registered i
  dsimp only at hc
  have hregistered := Lfzk.SoundnessAudit.hahn_twofield_linear_rhs i N tA htA
  dsimp only at hregistered
  calc
    v7DensityUpper i + N *
        max (max ((Lfzk.GradedV7Hash.row i).zkCoefficient
          (Lfzk.SoundnessAudit.v7HashLogv i))
          (v7SigHahn.zkCoefficient 8)) ((4 : ℚ) / 2 ^ 128) +
        2 * (Bcs.AdaptiveCommit.adaptiveNumerator
          (2 * (Lfzk.GradedV7Hash.row i).params.row.n +
            2 * v7SigHahn.params.row.n) tA
          (Lfzk.NizkAdaptiveTwoField.len2 (Lfzk.GradedV7Hash.row i)
            v7SigHahn + N) : ℚ) / 2 ^ 256
      ≤ zkCoreAt (Lfzk.GradedV7Hash.row i)
          (Lfzk.SoundnessAudit.v7HashLogv i)
          (Lfzk.GradedV7Hash.row i).cardCand +
          zkCoreAt v7SigHahn 8 v7SigHahn.cardCand + (4 : ℚ) / 2 ^ 128 +
          N * max (max ((Lfzk.GradedV7Hash.row i).zkCoefficient
            (Lfzk.SoundnessAudit.v7HashLogv i))
            (v7SigHahn.zkCoefficient 8)) ((4 : ℚ) / 2 ^ 128) +
          2 * (Bcs.AdaptiveCommit.adaptiveNumerator
            (2 * (Lfzk.GradedV7Hash.row i).params.row.n +
              2 * v7SigHahn.params.row.n) tA
            (Lfzk.NizkAdaptiveTwoField.len2 (Lfzk.GradedV7Hash.row i)
              v7SigHahn + N) : ℚ) / 2 ^ 256 := by linarith
    _ ≤ (651 : ℚ) / (1000 * 2 ^ 115) +
          N * ((1 : ℚ) / 2 ^ 117) + tA * ((1 : ℚ) / 2 ^ 138) :=
        hregistered
    _ ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
      have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
      have ht : (0 : ℚ) ≤ tA := Nat.cast_nonneg _
      nlinarith

/-- Full v8 density arithmetic at the same adaptive Merkle cutoff. -/
theorem v8DensityRhs_le_115 (N tA : ℕ) (htA : tA ≤ 2 ^ 115) :
    let fc := 2 * v8Sig.params.row.n + 2 * v8Hash.params.row.n
    let L := Lfzk.NizkAdaptiveTwoField.len2 v8Hash v8Sig
    let K := max (max (v8Hash.zkCoefficient 5)
      (v8Sig.zkCoefficient 3)) ((4 : ℚ) / 2 ^ 128)
    v8DensityUpper + N * K +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
        2 ^ 256 ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  dsimp only
  obtain ⟨hc, hm, ht⟩ := v8DensityLinearSlack
  let fc : ℕ := 2 * v8Sig.params.row.n + 2 * v8Hash.params.row.n
  let L : ℕ := Lfzk.NizkAdaptiveTwoField.len2 v8Hash v8Sig
  let K : ℚ := max (max (v8Hash.zkCoefficient 5)
    (v8Sig.zkCoefficient 3)) ((4 : ℚ) / 2 ^ 128)
  have hc' : v8DensityUpper + 2 * ((fc * (1 + L) : ℕ) : ℚ) / 2 ^ 256 ≤
      (1 : ℚ) / 2 ^ 115 := by simpa only [fc, L, K] using hc
  have hm' : K + 2 * ((fc + 2 ^ 115 : ℕ) : ℚ) / 2 ^ 256 ≤
      (1 : ℚ) / 2 ^ 115 := by simpa only [fc, L, K] using hm
  have ht' : 2 * ((3 * 2 ^ 115 + 2 * fc + 1 + L : ℕ) : ℚ) / 2 ^ 256 ≤
      (1 : ℚ) / 2 ^ 115 := by simpa only [fc, L, K] using ht
  have hnum := Lfzk.TSec.adaptiveNumerator_le_linear
    (fc := fc) (L := L) (N := N) (G := 2 ^ 115) htA
  have hbound :
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
        2 ^ 256 ≤
      2 * ((fc * (1 + L) + N * (fc + 2 ^ 115) +
        tA * (3 * 2 ^ 115 + 2 * fc + 1 + L) : ℕ) : ℚ) / 2 ^ 256 := by
    gcongr
  change v8DensityUpper + N * K +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
        2 ^ 256 ≤ (1 + N + tA : ℚ) / 2 ^ 115
  calc
    v8DensityUpper + N * K +
        2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
          2 ^ 256
      ≤ v8DensityUpper + N * K +
          2 * ((fc * (1 + L) + N * (fc + 2 ^ 115) +
            tA * (3 * 2 ^ 115 + 2 * fc + 1 + L) : ℕ) : ℚ) /
            2 ^ 256 := by gcongr
    _ = (v8DensityUpper + 2 * ((fc * (1 + L) : ℕ) : ℚ) / 2 ^ 256) +
          N * (K + 2 * ((fc + 2 ^ 115 : ℕ) : ℚ) / 2 ^ 256) +
          tA * (2 * ((3 * 2 ^ 115 + 2 * fc + 1 + L : ℕ) : ℚ) / 2 ^ 256) := by
            push_cast
            ring
    _ ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
          have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
          have htAq : (0 : ℚ) ≤ tA := Nat.cast_nonneg _
          nlinarith [mul_le_mul_of_nonneg_left hm' hN,
            mul_le_mul_of_nonneg_left ht' htAq]

/-- The exact compiled hash-answer budget for a v7 geometry, kept symbolic
in the combined challenge alphabet and MAC decoder multiplicity. -/
def v7GradedBudget (i : Fin 4) (cardC kmac N : ℕ) : ℚ :=
  Lfzk.NizkZkDeployedHash.gradedCombinedBudget
    (Lfzk.GradedV7Hash.row i) v7SigHahn
    (Lfzk.SoundnessAudit.v7HashLogv i) 8 cardC N
    (4 * kmac : ℚ)
    ((Lfzk.GradedV7Hash.challengeNumerator i : ℚ) / 2 ^ 128)
    ((Lfzk.GradedV7Hash.queryNumerator i : ℚ) / 2 ^ 128)
    (v7SigHahn.params.row.fail + v7SigHahn.params.row.arith)
    v7SigHahn.params.row.cover

theorem v7GradedBudget_le_density (i : Fin 4) (cardC kmac N : ℕ)
    (hC : 0 < cardC) (hmac : kmac * 2 ^ 128 ≤ cardC) :
    v7GradedBudget i cardC kmac N ≤
      v7DensityUpper i + N *
        max (max ((Lfzk.GradedV7Hash.row i).zkCoefficient
          (Lfzk.SoundnessAudit.v7HashLogv i))
          (v7SigHahn.zkCoefficient 8)) ((4 : ℚ) / 2 ^ 128) := by
  have hF₁ : 0 < (Lfzk.GradedV7Hash.row i).params.row.fieldSize := by
    fin_cases i <;> decide
  have hF₂ : 0 < v7SigHahn.params.row.fieldSize := by native_decide
  obtain ⟨h₁c, h₁q, h₂c, h₂q⟩ := v7GradedCosts_le_coefficient i
  have hb₂c : 0 ≤ v7SigHahn.params.row.fail +
      v7SigHahn.params.row.arith := by native_decide
  have hb₂q : 0 ≤ v7SigHahn.params.row.cover := by native_decide
  have hb₁c : 0 ≤
      (Lfzk.GradedV7Hash.challengeNumerator i : ℚ) / 2 ^ 128 := by
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hb₁q : 0 ≤
      (Lfzk.GradedV7Hash.queryNumerator i : ℚ) / 2 ^ 128 := by
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have h := Lfzk.NizkZkDeployedHash.gradedCombinedBudget_le_density
    (Lfzk.GradedV7Hash.row i) v7SigHahn
    (Lfzk.SoundnessAudit.v7HashLogv i) 8 cardC (2 ^ 128) 2 2 kmac N
    hC (by positivity) hF₁ hF₂ hmac
    ((Lfzk.GradedV7Hash.challengeNumerator i : ℚ) / 2 ^ 128)
    ((Lfzk.GradedV7Hash.queryNumerator i : ℚ) / 2 ^ 128)
    (v7SigHahn.params.row.fail + v7SigHahn.params.row.arith)
    v7SigHahn.params.row.cover
    hb₁c hb₁q hb₂c hb₂q h₁c h₁q h₂c h₂q
  unfold v7GradedBudget v7DensityUpper
  dsimp only
  convert h using 1 <;> push_cast <;> ring_nf

def v8GradedBudget (cardC kmac N : ℕ) : ℚ :=
  Lfzk.NizkZkDeployedHash.gradedCombinedBudget
    v8Hash v8Sig 5 3 cardC N (4 * kmac : ℚ)
    ((1804 : ℚ) / 2 ^ 128) ((1134 : ℚ) / 2 ^ 128)
    (v8Sig.params.row.fail + v8Sig.params.row.arith)
    v8Sig.params.row.cover

theorem v8GradedBudget_le_density (cardC kmac N : ℕ)
    (hC : 0 < cardC) (hmac : kmac * 2 ^ 128 ≤ cardC) :
    v8GradedBudget cardC kmac N ≤
      v8DensityUpper + N *
        max (max (v8Hash.zkCoefficient 5)
          (v8Sig.zkCoefficient 3)) ((4 : ℚ) / 2 ^ 128) := by
  obtain ⟨h₁c, h₁q, h₂c, h₂q⟩ := v8GradedCosts_le_coefficient
  have hF₁ : 0 < v8Hash.params.row.fieldSize := by native_decide
  have hF₂ : 0 < v8Sig.params.row.fieldSize := by native_decide
  have hb₂c : 0 ≤ v8Sig.params.row.fail +
      v8Sig.params.row.arith := by native_decide
  have hb₂q : 0 ≤ v8Sig.params.row.cover := by native_decide
  have h := Lfzk.NizkZkDeployedHash.gradedCombinedBudget_le_density
    v8Hash v8Sig 5 3 cardC (2 ^ 128) 2 2 kmac N
    hC (by positivity) hF₁ hF₂ hmac
    ((1804 : ℚ) / 2 ^ 128) ((1134 : ℚ) / 2 ^ 128)
    (v8Sig.params.row.fail + v8Sig.params.row.arith)
    v8Sig.params.row.cover
    (by norm_num) (by norm_num) hb₂c hb₂q h₁c h₁q h₂c h₂q
  unfold v8GradedBudget v8DensityUpper
  convert h using 1 <;> push_cast <;> ring_nf

/-- The exact v7 numerator of the compiled graded extraction theorem,
including adaptive Merkle accounting, has the 115-bit T-security envelope. -/
theorem v7GradedBudgetRhs_le_115 (i : Fin 4)
    (cardC kmac N tA : ℕ) (hC : 0 < cardC)
    (hmac : kmac * 2 ^ 128 ≤ cardC) (htA : tA ≤ 2 ^ 115) :
    let H := Lfzk.GradedV7Hash.row i
    let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
    let L := Lfzk.NizkAdaptiveTwoField.len2 H v7SigHahn
    v7GradedBudget i cardC kmac N +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
        2 ^ 256 ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  dsimp only
  have hb := v7GradedBudget_le_density i cardC kmac N hC hmac
  have hr := v7DensityRhs_le_115 i N tA htA
  dsimp only at hr
  linarith

/-- With a positive transcript-query budget, the graded v7 extraction
numerator fits the 116-bit T-security envelope.  The zero-query case needs
the flat terminal-pair argument rather than this separate-slot envelope. -/
theorem v7GradedBudgetRhs_le_116_of_pos_queries (i : Fin 4)
    (cardC kmac N tA : ℕ) (hC : 0 < cardC)
    (hmac : kmac * 2 ^ 128 ≤ cardC) (hN : 0 < N)
    (htA : tA ≤ 2 ^ 116) :
    let H := Lfzk.GradedV7Hash.row i
    let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
    let L := Lfzk.NizkAdaptiveTwoField.len2 H v7SigHahn
    v7GradedBudget i cardC kmac N +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
        2 ^ 256 ≤ (1 + N + tA : ℚ) / 2 ^ 116 := by
  dsimp only
  have hb := v7GradedBudget_le_density i cardC kmac N hC hmac
  have hc := v7DensityUpper_le_registered i
  have hp := Lfzk.SoundnessAudit.hahn_twofield_116_of_pos_queries_extended
    i N tA hN htA
  dsimp only at hc hp
  simp only [Lfzk.GradedV7Hash.row] at hb hc ⊢
  linarith

/-- The same exact compiled-numerator envelope for the v8 pair. -/
theorem v8GradedBudgetRhs_le_115
    (cardC kmac N tA : ℕ) (hC : 0 < cardC)
    (hmac : kmac * 2 ^ 128 ≤ cardC) (htA : tA ≤ 2 ^ 115) :
    let fc := 2 * v8Sig.params.row.n + 2 * v8Hash.params.row.n
    let L := Lfzk.NizkAdaptiveTwoField.len2 v8Hash v8Sig
    v8GradedBudget cardC kmac N +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
        2 ^ 256 ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  dsimp only
  have hb := v8GradedBudget_le_density cardC kmac N hC hmac
  have hr := v8DensityRhs_le_115 N tA htA
  dsimp only at hr
  linarith

end Lfzk.GradedCoreGrid
