import Lfzk.V1StrongV7Numeric
import LigeroFamily.Soundness.AgreementProfile

/-! Checked sparse Hahn endpoints and Johnson bounds for V1 payload families. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.V1StrongHahnPacking

open CodingTheory LigeroFamily

private theorem endpoint_packing (n w lam L : ℕ) (coeffs : List ℕ)
    (hvalid : HahnDelsarte.certificateValid n w lam coeffs = true)
    (hbound : HahnDelsarte.certifiedBound n w coeffs = L)
    {a : ℕ} (hwa : w ≤ a) (hlam : lam < w) :
    UniformFamilyBound n a lam L := by
  simpa only [hbound] using
    (HahnDelsarte.uniformFamilyBound_of_certificate hvalid).of_le_size hwa hlam

private theorem johnson_packing (n lam a : ℕ)
    (hlam : lam < a) (han : a ≤ n) (hden : n * lam < a * a) :
    UniformFamilyBound n a lam (uncheckedAgreementListBound n lam a) := by
  apply uncheckedAgreementListBound_uniformFamilyBound n lam a han
  · omega
  · rw [unchecked_denominator_eq n lam a (by omega) han]
    omega

theorem hash1_response_packing (a : ℕ)
    (ha : 1687 ≤ a) (han : a ≤ 3230) :
    UniformFamilyBound 3230 a 920
      (Lfzk.V1StrongV7Numeric.responsePacking 0 a) := by
  change UniformFamilyBound 3230 a 920
    (if 3230 * 920 < a * a then
      min (if 1700 ≤ a then 28849652485 else 400966108258685)
        (uncheckedAgreementListBound 3230 920 a)
    else if 1700 ≤ a then 28849652485 else 400966108258685)
  have hfirst : UniformFamilyBound 3230 a 920 400966108258685 :=
    endpoint_packing 3230 1687 920 400966108258685
      Lfzk.V1StrongHahnData.Hash1Response
      Lfzk.V1StrongHahnHash1.responseValid
      Lfzk.V1StrongHahnHash1.responseBound ha (by omega)
  by_cases hsecond : 1700 ≤ a
  · have hsecondBound : UniformFamilyBound 3230 a 920 28849652485 :=
      endpoint_packing 3230 1700 920 28849652485
        Lfzk.V1StrongHahnExtraData.Hash1Response2
        Lfzk.V1StrongHahnExtras.hash1Response2Valid
        Lfzk.V1StrongHahnExtras.hash1Response2Bound hsecond (by omega)
    by_cases hJ : 3230 * 920 < a * a
    · have h := hsecondBound.min (johnson_packing 3230 920 a
        (by omega) han hJ)
      simpa [hsecond, hJ] using h
    · simpa [hsecond, hJ] using hsecondBound
  · by_cases hJ : 3230 * 920 < a * a
    · have h := hfirst.min (johnson_packing 3230 920 a
        (by omega) han hJ)
      simpa [hsecond, hJ] using h
    · simpa [hsecond, hJ] using hfirst

theorem hash2_response_packing (a : ℕ)
    (ha : 1735 ≤ a) (han : a ≤ 3318) :
    UniformFamilyBound 3318 a 946
      (Lfzk.V1StrongV7Numeric.responsePacking 1 a) := by
  change UniformFamilyBound 3318 a 946
    (if 3318 * 946 < a * a then
      min (if 1744 ≤ a then 198458899828 else 296750042811368)
        (uncheckedAgreementListBound 3318 946 a)
    else if 1744 ≤ a then 198458899828 else 296750042811368)
  have hend : UniformFamilyBound 3318 a 946
      (if 1744 ≤ a then 198458899828 else 296750042811368) := by
    split_ifs with hsecond
    · exact endpoint_packing 3318 1744 946 198458899828
        Lfzk.V1StrongHahnExtraData.Hash2Response2
        Lfzk.V1StrongHahnExtras.hash2Response2Valid
        Lfzk.V1StrongHahnExtras.hash2Response2Bound hsecond (by omega)
    · exact endpoint_packing 3318 1735 946 296750042811368
        Lfzk.V1StrongHahnData.Hash2Response
        Lfzk.V1StrongHahnHash2.responseValid
        Lfzk.V1StrongHahnHash2.responseBound ha (by omega)
  by_cases hJ : 3318 * 946 < a * a
  · simpa [hJ] using hend.min
      (johnson_packing 3318 946 a (by omega) han hJ)
  · simpa [hJ] using hend

theorem hash3_response_packing (a : ℕ)
    (ha : 1751 ≤ a) (han : a ≤ 3352) :
    UniformFamilyBound 3352 a 954
      (Lfzk.V1StrongV7Numeric.responsePacking 2 a) := by
  change UniformFamilyBound 3352 a 954
    (if 3352 * 954 < a * a then
      min (if 1764 ≤ a then 31273126198 else 385824707325065)
        (uncheckedAgreementListBound 3352 954 a)
    else if 1764 ≤ a then 31273126198 else 385824707325065)
  have hend : UniformFamilyBound 3352 a 954
      (if 1764 ≤ a then 31273126198 else 385824707325065) := by
    split_ifs with hsecond
    · exact endpoint_packing 3352 1764 954 31273126198
        Lfzk.V1StrongHahnExtraData.Hash3Response2
        Lfzk.V1StrongHahnExtras.hash3Response2Valid
        Lfzk.V1StrongHahnExtras.hash3Response2Bound hsecond (by omega)
    · exact endpoint_packing 3352 1751 954 385824707325065
        Lfzk.V1StrongHahnData.Hash3Response
        Lfzk.V1StrongHahnHash3.responseValid
        Lfzk.V1StrongHahnHash3.responseBound ha (by omega)
  by_cases hJ : 3352 * 954 < a * a
  · simpa [hJ] using hend.min
      (johnson_packing 3352 954 a (by omega) han hJ)
  · simpa [hJ] using hend

theorem hash4_response_packing (a : ℕ)
    (ha : 1796 ≤ a) (han : a ≤ 3436) :
    UniformFamilyBound 3436 a 978
      (Lfzk.V1StrongV7Numeric.responsePacking 3 a) := by
  suffices htarget : UniformFamilyBound 3436 a 978
    (if 3436 * 978 < a * a then
      min (if 1809 ≤ a then 21488178000
        else if 1805 ≤ a then 220138078851
        else if 1801 ≤ a then 10885581438852
        else 308529467083846)
        (uncheckedAgreementListBound 3436 978 a)
    else if 1809 ≤ a then 21488178000
      else if 1805 ≤ a then 220138078851
      else if 1801 ≤ a then 10885581438852
      else 308529467083846) by
    simpa [Lfzk.V1StrongV7Numeric.responsePacking,
      Lfzk.V1StrongV7Numeric.row,
      Lfzk.V1StrongV7Numeric.responseSecondRadius,
      Lfzk.V1StrongV7Numeric.responseSecondEndpoint,
      Lfzk.V1StrongV7Numeric.responseEndpoint,
      Lfzk.V1StrongV7Rows.hash4, Lfzk.LigeroV1Rows.v7Hash4,
      Lfzk.LigeroV1Rows.Row.n, Lfzk.LigeroV1Rows.Row.k] using htarget
  have hend : UniformFamilyBound 3436 a 978
      (if 1809 ≤ a then 21488178000
        else if 1805 ≤ a then 220138078851
        else if 1801 ≤ a then 10885581438852
        else 308529467083846) := by
    split_ifs with hlate hmid hearly
    · exact endpoint_packing 3436 1809 978 21488178000
        Lfzk.V1StrongHahnExtraData.Hash4ResponseLate
        Lfzk.V1StrongHahnExtras.hash4ResponseLateValid
        Lfzk.V1StrongHahnExtras.hash4ResponseLateBound hlate (by omega)
    · exact endpoint_packing 3436 1805 978 220138078851
        Lfzk.V1StrongHahnExtraData.Hash4Response2
        Lfzk.V1StrongHahnExtras.hash4Response2Valid
        Lfzk.V1StrongHahnExtras.hash4Response2Bound hmid (by omega)
    · exact endpoint_packing 3436 1801 978 10885581438852
        Lfzk.V1StrongHahnExtraData.Hash4ResponseEarly
        Lfzk.V1StrongHahnExtras.hash4ResponseEarlyValid
        Lfzk.V1StrongHahnExtras.hash4ResponseEarlyBound hearly (by omega)
    · exact endpoint_packing 3436 1796 978 308529467083846
        Lfzk.V1StrongHahnData.Hash4Response
        Lfzk.V1StrongHahnHash4.responseValid
        Lfzk.V1StrongHahnHash4.responseBound ha (by omega)
  by_cases hJ : 3436 * 978 < a * a
  · simpa [hJ] using hend.min
      (johnson_packing 3436 978 a (by omega) han hJ)
  · simpa [hJ] using hend

theorem response_packing (i : Fin 4) (a : ℕ)
    (ha : Lfzk.V1StrongV7Numeric.cutoff
      (Lfzk.V1StrongV7Numeric.row i) < a)
    (han : a ≤ (Lfzk.V1StrongV7Numeric.row i).n) :
    UniformFamilyBound (Lfzk.V1StrongV7Numeric.row i).n a
      (2 * (Lfzk.V1StrongV7Numeric.row i).k - 2)
      (Lfzk.V1StrongV7Numeric.responsePacking i a) := by
  fin_cases i
  · change 1686 < a at ha
    change a ≤ 3230 at han
    exact hash1_response_packing a (by omega) han
  · change 1734 < a at ha
    change a ≤ 3318 at han
    exact hash2_response_packing a (by omega) han
  · change 1750 < a at ha
    change a ≤ 3352 at han
    exact hash3_response_packing a (by omega) han
  · change 1795 < a at ha
    change a ≤ 3436 at han
    exact hash4_response_packing a (by omega) han

end Lfzk.V1StrongHahnPacking
