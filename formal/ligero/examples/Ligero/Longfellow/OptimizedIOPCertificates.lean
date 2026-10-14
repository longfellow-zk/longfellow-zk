import examples.Ligero.Longfellow.ProfiledExtraction

/-! Best-found scalar IOP certificates with per-agreement Johnson parameters.
All arithmetic and geometry checks are connected to actual RS verifiers. V2/V3
share parameter data and checks; their concrete verifier bridges stay distinct. -/
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
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 3187, k := 455, d := 2733, e := 1484, g := 0, m := 123306
        fieldBits := 256, fieldOrder := 115792089210356248762697446949407573530086143415290314195533631308867097853951
        openings := 132, targetBits := 123 } }

theorem v7Sig_v1_parameters : v7Sig_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 3230, k := 461, d := 2770, e := 1673, g := 23, m := 10226156656
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125 } }

theorem v7Hash1_v2_parameters : v7Hash1_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 3230, k := 461, d := 2770, e := 1503, g := 2, m := 40407
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 122 } }

theorem v7Hash1_v1_parameters : v7Hash1_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 3318, k := 474, d := 2845, e := 1718, g := 23, m := 10490644166
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125 } }

theorem v7Hash2_v2_parameters : v7Hash2_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 3318, k := 474, d := 2845, e := 1543, g := 2, m := 41139
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 122 } }

theorem v7Hash2_v1_parameters : v7Hash2_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 3352, k := 478, d := 2875, e := 1736, g := 24, m := 10615575551
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125 } }

theorem v7Hash3_v2_parameters : v7Hash3_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 3352, k := 478, d := 2875, e := 1560, g := 2, m := 41742
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 122 } }

theorem v7Hash3_v1_parameters : v7Hash3_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 3436, k := 490, d := 2947, e := 1780, g := 24, m := 10884588574
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125 } }

theorem v7Hash4_v2_parameters : v7Hash4_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 3436, k := 490, d := 2947, e := 1599, g := 2, m := 42751
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 122 } }

theorem v7Hash4_v1_parameters : v7Hash4_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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

def v8Sig_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 3458, k := 494, d := 2965, e := 2148, g := 0, m := 8690222498718353
        fieldBits := 256, fieldOrder := 115792089210356248762697446949407573530086143415290314195533631308867097853951
        openings := 132, targetBits := 191 } }

theorem v8Sig_v2_parameters : v8Sig_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 3458, k := 494, d := 2965, e := 1610, g := 0, m := 134671
        fieldBits := 256, fieldOrder := 115792089210356248762697446949407573530086143415290314195533631308867097853951
        openings := 132, targetBits := 122 } }

theorem v8Sig_v1_parameters : v8Sig_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 4088, k := 584, d := 3505, e := 2116, g := 29, m := 12906933964
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125 } }

theorem v8Hash1_v2_parameters : v8Hash1_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 4088, k := 584, d := 3505, e := 1901, g := 2, m := 50856
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 121 } }

theorem v8Hash1_v1_parameters : v8Hash1_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 4081, k := 583, d := 3499, e := 2113, g := 29, m := 12890715663
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125 } }

theorem v8Hash2_v2_parameters : v8Hash2_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 4081, k := 583, d := 3499, e := 1898, g := 2, m := 51032
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 121 } }

theorem v8Hash2_v1_parameters : v8Hash2_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
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
      { n := 4081, k := 583, d := 3499, e := 2113, g := 29, m := 12890715663
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125 } }

theorem v8Hash3_v2_parameters : v8Hash3_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
  change v8Hash3_v2.certificate.inverseJohnsonConditions
    (v8Hash3_v2.etaDenominators (v8Hash3_v2.certificate.n - v8Hash3_v2.certificate.e))
    v8Hash3_v2.etaDenominators = true
  native_decide

theorem v8Hash3_v2_compressed_bound :
    v8Hash3_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash3_v2.certificate.targetBits := by native_decide

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
      { n := 4081, k := 583, d := 3499, e := 1898, g := 2, m := 51032
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 121 } }

theorem v8Hash3_v1_parameters : v8Hash3_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
  exact v8Hash3_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v8Hash3_v1_compressed_bound :
    v8Hash3_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash3_v1.certificate.targetBits := by native_decide

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
      { n := 4081, k := 583, d := 3499, e := 2113, g := 29, m := 12890715663
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125 } }

theorem v8Hash4_v2_parameters : v8Hash4_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
  change v8Hash4_v2.certificate.inverseJohnsonConditions
    (v8Hash4_v2.etaDenominators (v8Hash4_v2.certificate.n - v8Hash4_v2.certificate.e))
    v8Hash4_v2.etaDenominators = true
  native_decide

theorem v8Hash4_v2_compressed_bound :
    v8Hash4_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash4_v2.certificate.targetBits := by native_decide

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
      { n := 4081, k := 583, d := 3499, e := 1898, g := 2, m := 51032
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 121 } }

theorem v8Hash4_v1_parameters : v8Hash4_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, ?_⟩
  exact v8Hash4_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v8Hash4_v1_compressed_bound :
    v8Hash4_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v8Hash4_v1.certificate.targetBits := by native_decide

theorem v8Hash4_v1_bound :
    v8Hash4_v1.bound ≤ (1 : ℚ) / 2 ^ v8Hash4_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v8Hash4_v1_compressed_bound

def v8Hash4_v1_certified : CertifiedResult :=
  ⟨v8Hash4_v1, v8Hash4_v1_parameters, v8Hash4_v1_bound⟩

def v8Hash4_v1_extraction := @CertifiedResult.v1_extraction v8Hash4_v1_certified rfl

def v8Hash4_v1_interactive := @CertifiedResult.v1_interactive v8Hash4_v1_certified rfl

def v8Hash4_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v8Hash4_v1_certified rfl

end Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized
