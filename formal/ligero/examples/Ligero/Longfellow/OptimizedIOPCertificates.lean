import examples.Ligero.Longfellow.ProfiledExtraction
import examples.Ligero.Longfellow.HahnMaskCertificates

/-! Best-found scalar IOP certificates with per-agreement Johnson parameters.
All arithmetic and geometry checks are connected to actual RS verifiers. V2/V3
share parameter data and checks; their concrete verifier bridges stay distinct.
V1 records certify the unchecked-mask list below the Johnson threshold with
Hahn/Delsarte certificates (`HahnMaskCertificates`), checked in `_parameters`. -/
namespace Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized
open Ligero.Examples.Grid.LongfellowProfiledExtraction
set_option maxHeartbeats 20000000
set_option maxRecDepth 10000

def v7Sig_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 3187, k := 455, d := 2733, e := 1980, g := 0, m := 7199076871903652
        fieldBits := 256, fieldOrder := 115792089210356248762697446949407573530086143415290314195533631308867097853951
        openings := 132, targetBits := 191 } }

theorem v7Sig_v2_parameters : v7Sig_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by trivial, ?_⟩
  change v7Sig_v2.certificate.inverseJohnsonConditions
    (v7Sig_v2.etaDenominators (v7Sig_v2.certificate.n - v7Sig_v2.certificate.e))
    v7Sig_v2.etaDenominators = true
  native_decide

theorem v7Sig_v2_compressed_bound :
    v7Sig_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v7Sig_v2.certificate.targetBits := by native_decide

theorem v7Sig_v2_bound :
    v7Sig_v2.bound ≤ (1 : ℚ) / 2 ^ v7Sig_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Sig_v2_compressed_bound

def v7Sig_v2_certified : CertifiedResult :=
  ⟨v7Sig_v2, v7Sig_v2_parameters, v7Sig_v2_bound⟩

def v7Sig_v2_extraction := @CertifiedResult.v2_extraction v7Sig_v2_certified rfl

def v7Sig_v2_interactive := @CertifiedResult.v2_interactive v7Sig_v2_certified rfl

def v7Sig_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v7Sig_v2_certified rfl

def v7Sig_v3 : Result := { v7Sig_v2 with variant := .v3 }

theorem v7Sig_v3_parameters : v7Sig_v3.ParametersValid := v7Sig_v2_parameters

theorem v7Sig_v3_compressed_bound :
    v7Sig_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v7Sig_v3.certificate.targetBits := v7Sig_v2_compressed_bound

theorem v7Sig_v3_bound :
    v7Sig_v3.bound ≤ (1 : ℚ) / 2 ^ v7Sig_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Sig_v3_compressed_bound

def v7Sig_v3_certified : CertifiedResult :=
  ⟨v7Sig_v3, v7Sig_v3_parameters, v7Sig_v3_bound⟩

def v7Sig_v3_extraction := @CertifiedResult.v3_extraction v7Sig_v3_certified rfl

def v7Sig_v3_interactive := @CertifiedResult.v3_interactive v7Sig_v3_certified rfl

def v7Sig_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v7Sig_v3_certified rfl

def v7Sig_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 3187, k := 455, d := 2733, e := 1522, g := 0, m := 8726582
        fieldBits := 256, fieldOrder := 115792089210356248762697446949407573530086143415290314195533631308867097853951
        openings := 132, targetBits := 127
        maskThreshold := 1665, hahnMask := HahnMask.v7Sig } }

theorem v7Sig_v1_parameters : v7Sig_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
  exact v7Sig_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v7Sig_v1_compressed_bound :
    v7Sig_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v7Sig_v1.certificate.targetBits := by native_decide

theorem v7Sig_v1_bound :
    v7Sig_v1.bound ≤ (1 : ℚ) / 2 ^ v7Sig_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Sig_v1_compressed_bound

def v7Sig_v1_certified : CertifiedResult :=
  ⟨v7Sig_v1, v7Sig_v1_parameters, v7Sig_v1_bound⟩

def v7Sig_v1_extraction := @CertifiedResult.v1_extraction v7Sig_v1_certified rfl

def v7Sig_v1_interactive := @CertifiedResult.v1_interactive v7Sig_v1_certified rfl

def v7Sig_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v7Sig_v1_certified rfl

def v7Hash1_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 3230, k := 461, d := 2770, e := 1670, g := 23, m := 9433738746
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 126 } }

theorem v7Hash1_v2_parameters : v7Hash1_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by trivial, ?_⟩
  change v7Hash1_v2.certificate.inverseJohnsonConditions
    (v7Hash1_v2.etaDenominators (v7Hash1_v2.certificate.n - v7Hash1_v2.certificate.e))
    v7Hash1_v2.etaDenominators = true
  native_decide

theorem v7Hash1_v2_compressed_bound :
    v7Hash1_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash1_v2.certificate.targetBits := by native_decide

theorem v7Hash1_v2_bound :
    v7Hash1_v2.bound ≤ (1 : ℚ) / 2 ^ v7Hash1_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash1_v2_compressed_bound

def v7Hash1_v2_certified : CertifiedResult :=
  ⟨v7Hash1_v2, v7Hash1_v2_parameters, v7Hash1_v2_bound⟩

def v7Hash1_v2_extraction := @CertifiedResult.v2_extraction v7Hash1_v2_certified rfl

def v7Hash1_v2_interactive := @CertifiedResult.v2_interactive v7Hash1_v2_certified rfl

def v7Hash1_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v7Hash1_v2_certified rfl

def v7Hash1_v3 : Result := { v7Hash1_v2 with variant := .v3 }

theorem v7Hash1_v3_parameters : v7Hash1_v3.ParametersValid := v7Hash1_v2_parameters

theorem v7Hash1_v3_compressed_bound :
    v7Hash1_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash1_v3.certificate.targetBits := v7Hash1_v2_compressed_bound

theorem v7Hash1_v3_bound :
    v7Hash1_v3.bound ≤ (1 : ℚ) / 2 ^ v7Hash1_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash1_v3_compressed_bound

def v7Hash1_v3_certified : CertifiedResult :=
  ⟨v7Hash1_v3, v7Hash1_v3_parameters, v7Hash1_v3_bound⟩

def v7Hash1_v3_extraction := @CertifiedResult.v3_extraction v7Hash1_v3_certified rfl

def v7Hash1_v3_interactive := @CertifiedResult.v3_interactive v7Hash1_v3_certified rfl

def v7Hash1_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v7Hash1_v3_certified rfl

def v7Hash1_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 3230, k := 461, d := 2770, e := 1543, g := 16, m := 1200474
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125
        maskThreshold := 1681, hahnMask := HahnMask.v7Hash1 } }

theorem v7Hash1_v1_parameters : v7Hash1_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
  exact v7Hash1_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v7Hash1_v1_compressed_bound :
    v7Hash1_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash1_v1.certificate.targetBits := by native_decide

theorem v7Hash1_v1_bound :
    v7Hash1_v1.bound ≤ (1 : ℚ) / 2 ^ v7Hash1_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash1_v1_compressed_bound

def v7Hash1_v1_certified : CertifiedResult :=
  ⟨v7Hash1_v1, v7Hash1_v1_parameters, v7Hash1_v1_bound⟩

def v7Hash1_v1_extraction := @CertifiedResult.v1_extraction v7Hash1_v1_certified rfl

def v7Hash1_v1_interactive := @CertifiedResult.v1_interactive v7Hash1_v1_certified rfl

def v7Hash1_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v7Hash1_v1_certified rfl

def v7Hash2_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 3318, k := 474, d := 2845, e := 1715, g := 23, m := 9678434277
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 126 } }

theorem v7Hash2_v2_parameters : v7Hash2_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by trivial, ?_⟩
  change v7Hash2_v2.certificate.inverseJohnsonConditions
    (v7Hash2_v2.etaDenominators (v7Hash2_v2.certificate.n - v7Hash2_v2.certificate.e))
    v7Hash2_v2.etaDenominators = true
  native_decide

theorem v7Hash2_v2_compressed_bound :
    v7Hash2_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash2_v2.certificate.targetBits := by native_decide

theorem v7Hash2_v2_bound :
    v7Hash2_v2.bound ≤ (1 : ℚ) / 2 ^ v7Hash2_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash2_v2_compressed_bound

def v7Hash2_v2_certified : CertifiedResult :=
  ⟨v7Hash2_v2, v7Hash2_v2_parameters, v7Hash2_v2_bound⟩

def v7Hash2_v2_extraction := @CertifiedResult.v2_extraction v7Hash2_v2_certified rfl

def v7Hash2_v2_interactive := @CertifiedResult.v2_interactive v7Hash2_v2_certified rfl

def v7Hash2_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v7Hash2_v2_certified rfl

def v7Hash2_v3 : Result := { v7Hash2_v2 with variant := .v3 }

theorem v7Hash2_v3_parameters : v7Hash2_v3.ParametersValid := v7Hash2_v2_parameters

theorem v7Hash2_v3_compressed_bound :
    v7Hash2_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash2_v3.certificate.targetBits := v7Hash2_v2_compressed_bound

theorem v7Hash2_v3_bound :
    v7Hash2_v3.bound ≤ (1 : ℚ) / 2 ^ v7Hash2_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash2_v3_compressed_bound

def v7Hash2_v3_certified : CertifiedResult :=
  ⟨v7Hash2_v3, v7Hash2_v3_parameters, v7Hash2_v3_bound⟩

def v7Hash2_v3_extraction := @CertifiedResult.v3_extraction v7Hash2_v3_certified rfl

def v7Hash2_v3_interactive := @CertifiedResult.v3_interactive v7Hash2_v3_certified rfl

def v7Hash2_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v7Hash2_v3_certified rfl

def v7Hash2_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 3318, k := 474, d := 2845, e := 1584, g := 16, m := 420929
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125
        maskThreshold := 1728, hahnMask := HahnMask.v7Hash2 } }

theorem v7Hash2_v1_parameters : v7Hash2_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
  exact v7Hash2_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v7Hash2_v1_compressed_bound :
    v7Hash2_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash2_v1.certificate.targetBits := by native_decide

theorem v7Hash2_v1_bound :
    v7Hash2_v1.bound ≤ (1 : ℚ) / 2 ^ v7Hash2_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash2_v1_compressed_bound

def v7Hash2_v1_certified : CertifiedResult :=
  ⟨v7Hash2_v1, v7Hash2_v1_parameters, v7Hash2_v1_bound⟩

def v7Hash2_v1_extraction := @CertifiedResult.v1_extraction v7Hash2_v1_certified rfl

def v7Hash2_v1_interactive := @CertifiedResult.v1_interactive v7Hash2_v1_certified rfl

def v7Hash2_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v7Hash2_v1_certified rfl

def v7Hash3_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 3352, k := 478, d := 2875, e := 1733, g := 24, m := 9793967305
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 126 } }

theorem v7Hash3_v2_parameters : v7Hash3_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by trivial, ?_⟩
  change v7Hash3_v2.certificate.inverseJohnsonConditions
    (v7Hash3_v2.etaDenominators (v7Hash3_v2.certificate.n - v7Hash3_v2.certificate.e))
    v7Hash3_v2.etaDenominators = true
  native_decide

theorem v7Hash3_v2_compressed_bound :
    v7Hash3_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash3_v2.certificate.targetBits := by native_decide

theorem v7Hash3_v2_bound :
    v7Hash3_v2.bound ≤ (1 : ℚ) / 2 ^ v7Hash3_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash3_v2_compressed_bound

def v7Hash3_v2_certified : CertifiedResult :=
  ⟨v7Hash3_v2, v7Hash3_v2_parameters, v7Hash3_v2_bound⟩

def v7Hash3_v2_extraction := @CertifiedResult.v2_extraction v7Hash3_v2_certified rfl

def v7Hash3_v2_interactive := @CertifiedResult.v2_interactive v7Hash3_v2_certified rfl

def v7Hash3_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v7Hash3_v2_certified rfl

def v7Hash3_v3 : Result := { v7Hash3_v2 with variant := .v3 }

theorem v7Hash3_v3_parameters : v7Hash3_v3.ParametersValid := v7Hash3_v2_parameters

theorem v7Hash3_v3_compressed_bound :
    v7Hash3_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash3_v3.certificate.targetBits := v7Hash3_v2_compressed_bound

theorem v7Hash3_v3_bound :
    v7Hash3_v3.bound ≤ (1 : ℚ) / 2 ^ v7Hash3_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash3_v3_compressed_bound

def v7Hash3_v3_certified : CertifiedResult :=
  ⟨v7Hash3_v3, v7Hash3_v3_parameters, v7Hash3_v3_bound⟩

def v7Hash3_v3_extraction := @CertifiedResult.v3_extraction v7Hash3_v3_certified rfl

def v7Hash3_v3_interactive := @CertifiedResult.v3_interactive v7Hash3_v3_certified rfl

def v7Hash3_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v7Hash3_v3_certified rfl

def v7Hash3_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 3352, k := 478, d := 2875, e := 1601, g := 16, m := 310355
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125
        maskThreshold := 1744, hahnMask := HahnMask.v7Hash3 } }

theorem v7Hash3_v1_parameters : v7Hash3_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
  exact v7Hash3_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v7Hash3_v1_compressed_bound :
    v7Hash3_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash3_v1.certificate.targetBits := by native_decide

theorem v7Hash3_v1_bound :
    v7Hash3_v1.bound ≤ (1 : ℚ) / 2 ^ v7Hash3_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash3_v1_compressed_bound

def v7Hash3_v1_certified : CertifiedResult :=
  ⟨v7Hash3_v1, v7Hash3_v1_parameters, v7Hash3_v1_bound⟩

def v7Hash3_v1_extraction := @CertifiedResult.v1_extraction v7Hash3_v1_certified rfl

def v7Hash3_v1_interactive := @CertifiedResult.v1_interactive v7Hash3_v1_certified rfl

def v7Hash3_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v7Hash3_v1_certified rfl

def v7Hash4_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 3436, k := 490, d := 2947, e := 1777, g := 24, m := 10042792941
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 126 } }

theorem v7Hash4_v2_parameters : v7Hash4_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by trivial, ?_⟩
  change v7Hash4_v2.certificate.inverseJohnsonConditions
    (v7Hash4_v2.etaDenominators (v7Hash4_v2.certificate.n - v7Hash4_v2.certificate.e))
    v7Hash4_v2.etaDenominators = true
  native_decide

theorem v7Hash4_v2_compressed_bound :
    v7Hash4_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash4_v2.certificate.targetBits := by native_decide

theorem v7Hash4_v2_bound :
    v7Hash4_v2.bound ≤ (1 : ℚ) / 2 ^ v7Hash4_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash4_v2_compressed_bound

def v7Hash4_v2_certified : CertifiedResult :=
  ⟨v7Hash4_v2, v7Hash4_v2_parameters, v7Hash4_v2_bound⟩

def v7Hash4_v2_extraction := @CertifiedResult.v2_extraction v7Hash4_v2_certified rfl

def v7Hash4_v2_interactive := @CertifiedResult.v2_interactive v7Hash4_v2_certified rfl

def v7Hash4_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v7Hash4_v2_certified rfl

def v7Hash4_v3 : Result := { v7Hash4_v2 with variant := .v3 }

theorem v7Hash4_v3_parameters : v7Hash4_v3.ParametersValid := v7Hash4_v2_parameters

theorem v7Hash4_v3_compressed_bound :
    v7Hash4_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash4_v3.certificate.targetBits := v7Hash4_v2_compressed_bound

theorem v7Hash4_v3_bound :
    v7Hash4_v3.bound ≤ (1 : ℚ) / 2 ^ v7Hash4_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash4_v3_compressed_bound

def v7Hash4_v3_certified : CertifiedResult :=
  ⟨v7Hash4_v3, v7Hash4_v3_parameters, v7Hash4_v3_bound⟩

def v7Hash4_v3_extraction := @CertifiedResult.v3_extraction v7Hash4_v3_certified rfl

def v7Hash4_v3_interactive := @CertifiedResult.v3_interactive v7Hash4_v3_certified rfl

def v7Hash4_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v7Hash4_v3_certified rfl

def v7Hash4_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 3436, k := 490, d := 2947, e := 1642, g := 16, m := 4467784
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125
        maskThreshold := 1788, hahnMask := HahnMask.v7Hash4 } }

theorem v7Hash4_v1_parameters : v7Hash4_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
  exact v7Hash4_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v7Hash4_v1_compressed_bound :
    v7Hash4_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash4_v1.certificate.targetBits := by native_decide

theorem v7Hash4_v1_bound :
    v7Hash4_v1.bound ≤ (1 : ℚ) / 2 ^ v7Hash4_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash4_v1_compressed_bound

def v7Hash4_v1_certified : CertifiedResult :=
  ⟨v7Hash4_v1, v7Hash4_v1_parameters, v7Hash4_v1_bound⟩

def v7Hash4_v1_extraction := @CertifiedResult.v1_extraction v7Hash4_v1_certified rfl

def v7Hash4_v1_interactive := @CertifiedResult.v1_interactive v7Hash4_v1_certified rfl

def v7Hash4_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v7Hash4_v1_certified rfl

/-- The larger-radius V1 flat certificates still give at most two committed lifts
at each of the four deployed hash geometries. -/
theorem v7Hash_v1_flat_listSize_two :
    v7Hash1_v1.certificate.listSize ≤ 2 ∧
    v7Hash2_v1.certificate.listSize ≤ 2 ∧
    v7Hash3_v1.certificate.listSize ≤ 2 ∧
    v7Hash4_v1.certificate.listSize ≤ 2 := by
  native_decide

def v8Sig_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 3458, k := 494, d := 2965, e := 2148, g := 0, m := 8690222498718353
        fieldBits := 256, fieldOrder := 115792089210356248762697446949407573530086143415290314195533631308867097853951
        openings := 132, targetBits := 191 } }

theorem v8Sig_v2_parameters : v8Sig_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by trivial, ?_⟩
  change v8Sig_v2.certificate.inverseJohnsonConditions
    (v8Sig_v2.etaDenominators (v8Sig_v2.certificate.n - v8Sig_v2.certificate.e))
    v8Sig_v2.etaDenominators = true
  native_decide

theorem v8Sig_v2_compressed_bound :
    v8Sig_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v8Sig_v2.certificate.targetBits := by native_decide

theorem v8Sig_v2_bound :
    v8Sig_v2.bound ≤ (1 : ℚ) / 2 ^ v8Sig_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Sig_v2_compressed_bound

def v8Sig_v2_certified : CertifiedResult :=
  ⟨v8Sig_v2, v8Sig_v2_parameters, v8Sig_v2_bound⟩

def v8Sig_v2_extraction := @CertifiedResult.v2_extraction v8Sig_v2_certified rfl

def v8Sig_v2_interactive := @CertifiedResult.v2_interactive v8Sig_v2_certified rfl

def v8Sig_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v8Sig_v2_certified rfl

def v8Sig_v3 : Result := { v8Sig_v2 with variant := .v3 }

theorem v8Sig_v3_parameters : v8Sig_v3.ParametersValid := v8Sig_v2_parameters

theorem v8Sig_v3_compressed_bound :
    v8Sig_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v8Sig_v3.certificate.targetBits := v8Sig_v2_compressed_bound

theorem v8Sig_v3_bound :
    v8Sig_v3.bound ≤ (1 : ℚ) / 2 ^ v8Sig_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Sig_v3_compressed_bound

def v8Sig_v3_certified : CertifiedResult :=
  ⟨v8Sig_v3, v8Sig_v3_parameters, v8Sig_v3_bound⟩

def v8Sig_v3_extraction := @CertifiedResult.v3_extraction v8Sig_v3_certified rfl

def v8Sig_v3_interactive := @CertifiedResult.v3_interactive v8Sig_v3_certified rfl

def v8Sig_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v8Sig_v3_certified rfl

def v8Sig_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 3458, k := 494, d := 2965, e := 1651, g := 0, m := 10594014
        fieldBits := 256, fieldOrder := 115792089210356248762697446949407573530086143415290314195533631308867097853951
        openings := 132, targetBits := 127
        maskThreshold := 1808, hahnMask := HahnMask.v8Sig } }

theorem v8Sig_v1_parameters : v8Sig_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
  exact v8Sig_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v8Sig_v1_compressed_bound :
    v8Sig_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v8Sig_v1.certificate.targetBits := by native_decide

theorem v8Sig_v1_bound :
    v8Sig_v1.bound ≤ (1 : ℚ) / 2 ^ v8Sig_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Sig_v1_compressed_bound

def v8Sig_v1_certified : CertifiedResult :=
  ⟨v8Sig_v1, v8Sig_v1_parameters, v8Sig_v1_bound⟩

def v8Sig_v1_extraction := @CertifiedResult.v1_extraction v8Sig_v1_certified rfl

def v8Sig_v1_interactive := @CertifiedResult.v1_interactive v8Sig_v1_certified rfl

def v8Sig_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v8Sig_v1_certified rfl

def v8Hash1_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 4088, k := 584, d := 3505, e := 2113, g := 29, m := 11913618043
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 126 } }

theorem v8Hash1_v2_parameters : v8Hash1_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by trivial, ?_⟩
  change v8Hash1_v2.certificate.inverseJohnsonConditions
    (v8Hash1_v2.etaDenominators (v8Hash1_v2.certificate.n - v8Hash1_v2.certificate.e))
    v8Hash1_v2.etaDenominators = true
  native_decide

theorem v8Hash1_v2_compressed_bound :
    v8Hash1_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash1_v2.certificate.targetBits := by native_decide

theorem v8Hash1_v2_bound :
    v8Hash1_v2.bound ≤ (1 : ℚ) / 2 ^ v8Hash1_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Hash1_v2_compressed_bound

def v8Hash1_v2_certified : CertifiedResult :=
  ⟨v8Hash1_v2, v8Hash1_v2_parameters, v8Hash1_v2_bound⟩

def v8Hash1_v2_extraction := @CertifiedResult.v2_extraction v8Hash1_v2_certified rfl

def v8Hash1_v2_interactive := @CertifiedResult.v2_interactive v8Hash1_v2_certified rfl

def v8Hash1_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v8Hash1_v2_certified rfl

def v8Hash1_v3 : Result := { v8Hash1_v2 with variant := .v3 }

theorem v8Hash1_v3_parameters : v8Hash1_v3.ParametersValid := v8Hash1_v2_parameters

theorem v8Hash1_v3_compressed_bound :
    v8Hash1_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash1_v3.certificate.targetBits := v8Hash1_v2_compressed_bound

theorem v8Hash1_v3_bound :
    v8Hash1_v3.bound ≤ (1 : ℚ) / 2 ^ v8Hash1_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Hash1_v3_compressed_bound

def v8Hash1_v3_certified : CertifiedResult :=
  ⟨v8Hash1_v3, v8Hash1_v3_parameters, v8Hash1_v3_bound⟩

def v8Hash1_v3_extraction := @CertifiedResult.v3_extraction v8Hash1_v3_certified rfl

def v8Hash1_v3_interactive := @CertifiedResult.v3_interactive v8Hash1_v3_certified rfl

def v8Hash1_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v8Hash1_v3_certified rfl

def v8Hash1_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 4088, k := 584, d := 3505, e := 1952, g := 16, m := 2437855
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125
        maskThreshold := 2122, hahnMask := HahnMask.v8Hash1 } }

theorem v8Hash1_v1_parameters : v8Hash1_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
  exact v8Hash1_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v8Hash1_v1_compressed_bound :
    v8Hash1_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash1_v1.certificate.targetBits := by native_decide

theorem v8Hash1_v1_bound :
    v8Hash1_v1.bound ≤ (1 : ℚ) / 2 ^ v8Hash1_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Hash1_v1_compressed_bound

def v8Hash1_v1_certified : CertifiedResult :=
  ⟨v8Hash1_v1, v8Hash1_v1_parameters, v8Hash1_v1_bound⟩

def v8Hash1_v1_extraction := @CertifiedResult.v1_extraction v8Hash1_v1_certified rfl

def v8Hash1_v1_interactive := @CertifiedResult.v1_interactive v8Hash1_v1_certified rfl

def v8Hash1_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v8Hash1_v1_certified rfl

def v8Hash2_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 4081, k := 583, d := 3499, e := 2109, g := 29, m := 11890030538
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 126 } }

theorem v8Hash2_v2_parameters : v8Hash2_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by trivial, ?_⟩
  change v8Hash2_v2.certificate.inverseJohnsonConditions
    (v8Hash2_v2.etaDenominators (v8Hash2_v2.certificate.n - v8Hash2_v2.certificate.e))
    v8Hash2_v2.etaDenominators = true
  native_decide

theorem v8Hash2_v2_compressed_bound :
    v8Hash2_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash2_v2.certificate.targetBits := by native_decide

theorem v8Hash2_v2_bound :
    v8Hash2_v2.bound ≤ (1 : ℚ) / 2 ^ v8Hash2_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Hash2_v2_compressed_bound

def v8Hash2_v2_certified : CertifiedResult :=
  ⟨v8Hash2_v2, v8Hash2_v2_parameters, v8Hash2_v2_bound⟩

def v8Hash2_v2_extraction := @CertifiedResult.v2_extraction v8Hash2_v2_certified rfl

def v8Hash2_v2_interactive := @CertifiedResult.v2_interactive v8Hash2_v2_certified rfl

def v8Hash2_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v8Hash2_v2_certified rfl

def v8Hash2_v3 : Result := { v8Hash2_v2 with variant := .v3 }

theorem v8Hash2_v3_parameters : v8Hash2_v3.ParametersValid := v8Hash2_v2_parameters

theorem v8Hash2_v3_compressed_bound :
    v8Hash2_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash2_v3.certificate.targetBits := v8Hash2_v2_compressed_bound

theorem v8Hash2_v3_bound :
    v8Hash2_v3.bound ≤ (1 : ℚ) / 2 ^ v8Hash2_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Hash2_v3_compressed_bound

def v8Hash2_v3_certified : CertifiedResult :=
  ⟨v8Hash2_v3, v8Hash2_v3_parameters, v8Hash2_v3_bound⟩

def v8Hash2_v3_extraction := @CertifiedResult.v3_extraction v8Hash2_v3_certified rfl

def v8Hash2_v3_interactive := @CertifiedResult.v3_interactive v8Hash2_v3_certified rfl

def v8Hash2_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v8Hash2_v3_certified rfl

def v8Hash2_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 4081, k := 583, d := 3499, e := 1946, g := 24, m := 107858
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125
        maskThreshold := 2113, hahnMask := HahnMask.v8Hash2 } }

theorem v8Hash2_v1_parameters : v8Hash2_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
  exact v8Hash2_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v8Hash2_v1_compressed_bound :
    v8Hash2_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash2_v1.certificate.targetBits := by native_decide

theorem v8Hash2_v1_bound :
    v8Hash2_v1.bound ≤ (1 : ℚ) / 2 ^ v8Hash2_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Hash2_v1_compressed_bound

def v8Hash2_v1_certified : CertifiedResult :=
  ⟨v8Hash2_v1, v8Hash2_v1_parameters, v8Hash2_v1_bound⟩

def v8Hash2_v1_extraction := @CertifiedResult.v1_extraction v8Hash2_v1_certified rfl

def v8Hash2_v1_interactive := @CertifiedResult.v1_interactive v8Hash2_v1_certified rfl

def v8Hash2_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v8Hash2_v1_certified rfl

def v8Hash3_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 4081, k := 583, d := 3499, e := 2109, g := 29, m := 11890030538
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 126 } }

theorem v8Hash3_v2_parameters : v8Hash3_v2.ParametersValid := v8Hash2_v2_parameters

theorem v8Hash3_v2_compressed_bound :
    v8Hash3_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash3_v2.certificate.targetBits := v8Hash2_v2_compressed_bound

theorem v8Hash3_v2_bound :
    v8Hash3_v2.bound ≤ (1 : ℚ) / 2 ^ v8Hash3_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Hash3_v2_compressed_bound

def v8Hash3_v2_certified : CertifiedResult :=
  ⟨v8Hash3_v2, v8Hash3_v2_parameters, v8Hash3_v2_bound⟩

def v8Hash3_v2_extraction := @CertifiedResult.v2_extraction v8Hash3_v2_certified rfl

def v8Hash3_v2_interactive := @CertifiedResult.v2_interactive v8Hash3_v2_certified rfl

def v8Hash3_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v8Hash3_v2_certified rfl

def v8Hash3_v3 : Result := { v8Hash3_v2 with variant := .v3 }

theorem v8Hash3_v3_parameters : v8Hash3_v3.ParametersValid := v8Hash3_v2_parameters

theorem v8Hash3_v3_compressed_bound :
    v8Hash3_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash3_v3.certificate.targetBits := v8Hash3_v2_compressed_bound

theorem v8Hash3_v3_bound :
    v8Hash3_v3.bound ≤ (1 : ℚ) / 2 ^ v8Hash3_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Hash3_v3_compressed_bound

def v8Hash3_v3_certified : CertifiedResult :=
  ⟨v8Hash3_v3, v8Hash3_v3_parameters, v8Hash3_v3_bound⟩

def v8Hash3_v3_extraction := @CertifiedResult.v3_extraction v8Hash3_v3_certified rfl

def v8Hash3_v3_interactive := @CertifiedResult.v3_interactive v8Hash3_v3_certified rfl

def v8Hash3_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v8Hash3_v3_certified rfl

def v8Hash3_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 4081, k := 583, d := 3499, e := 1946, g := 24, m := 107858
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125
        maskThreshold := 2113, hahnMask := HahnMask.v8Hash2 } }

theorem v8Hash3_v1_parameters : v8Hash3_v1.ParametersValid := v8Hash2_v1_parameters

theorem v8Hash3_v1_compressed_bound :
    v8Hash3_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash3_v1.certificate.targetBits := v8Hash2_v1_compressed_bound

theorem v8Hash3_v1_bound :
    v8Hash3_v1.bound ≤ (1 : ℚ) / 2 ^ v8Hash3_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Hash3_v1_compressed_bound

def v8Hash3_v1_certified : CertifiedResult :=
  ⟨v8Hash3_v1, v8Hash3_v1_parameters, v8Hash3_v1_bound⟩

def v8Hash3_v1_extraction := @CertifiedResult.v1_extraction v8Hash3_v1_certified rfl

def v8Hash3_v1_interactive := @CertifiedResult.v1_interactive v8Hash3_v1_certified rfl

def v8Hash3_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v8Hash3_v1_certified rfl

def v8Hash4_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 4081, k := 583, d := 3499, e := 2109, g := 29, m := 11890030538
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 126 } }

theorem v8Hash4_v2_parameters : v8Hash4_v2.ParametersValid := v8Hash2_v2_parameters

theorem v8Hash4_v2_compressed_bound :
    v8Hash4_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash4_v2.certificate.targetBits := v8Hash2_v2_compressed_bound

theorem v8Hash4_v2_bound :
    v8Hash4_v2.bound ≤ (1 : ℚ) / 2 ^ v8Hash4_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Hash4_v2_compressed_bound

def v8Hash4_v2_certified : CertifiedResult :=
  ⟨v8Hash4_v2, v8Hash4_v2_parameters, v8Hash4_v2_bound⟩

def v8Hash4_v2_extraction := @CertifiedResult.v2_extraction v8Hash4_v2_certified rfl

def v8Hash4_v2_interactive := @CertifiedResult.v2_interactive v8Hash4_v2_certified rfl

def v8Hash4_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v8Hash4_v2_certified rfl

def v8Hash4_v3 : Result := { v8Hash4_v2 with variant := .v3 }

theorem v8Hash4_v3_parameters : v8Hash4_v3.ParametersValid := v8Hash4_v2_parameters

theorem v8Hash4_v3_compressed_bound :
    v8Hash4_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash4_v3.certificate.targetBits := v8Hash4_v2_compressed_bound

theorem v8Hash4_v3_bound :
    v8Hash4_v3.bound ≤ (1 : ℚ) / 2 ^ v8Hash4_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Hash4_v3_compressed_bound

def v8Hash4_v3_certified : CertifiedResult :=
  ⟨v8Hash4_v3, v8Hash4_v3_parameters, v8Hash4_v3_bound⟩

def v8Hash4_v3_extraction := @CertifiedResult.v3_extraction v8Hash4_v3_certified rfl

def v8Hash4_v3_interactive := @CertifiedResult.v3_interactive v8Hash4_v3_certified rfl

def v8Hash4_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v8Hash4_v3_certified rfl

def v8Hash4_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 4081, k := 583, d := 3499, e := 1946, g := 24, m := 107858
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125
        maskThreshold := 2113, hahnMask := HahnMask.v8Hash2 } }

theorem v8Hash4_v1_parameters : v8Hash4_v1.ParametersValid := v8Hash2_v1_parameters

theorem v8Hash4_v1_compressed_bound :
    v8Hash4_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash4_v1.certificate.targetBits := v8Hash2_v1_compressed_bound

theorem v8Hash4_v1_bound :
    v8Hash4_v1.bound ≤ (1 : ℚ) / 2 ^ v8Hash4_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Hash4_v1_compressed_bound

def v8Hash4_v1_certified : CertifiedResult :=
  ⟨v8Hash4_v1, v8Hash4_v1_parameters, v8Hash4_v1_bound⟩

def v8Hash4_v1_extraction := @CertifiedResult.v1_extraction v8Hash4_v1_certified rfl

def v8Hash4_v1_interactive := @CertifiedResult.v1_interactive v8Hash4_v1_certified rfl

def v8Hash4_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v8Hash4_v1_certified rfl

end Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized
