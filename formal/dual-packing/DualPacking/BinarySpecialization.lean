import DualPacking.ArtinSchreierBackend

/-! # The binary protocol is an exact specialization of the finite-field verifier

These identities recover the original trace, quadratic masks, native linear
coefficients, and optional square check when the base field is `ZMod 2`.
-/

namespace DualPacking.ArtinSchreier

open Finset Module
open scoped Classical

variable {F I J : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [Fintype I] [DecidableEq I] [Fintype J]

local instance : CharP F 2 := charP_of_injective_algebraMap' (ZMod 2) 2

theorem frobenius_binary (x : F) : frobenius (ZMod 2) F x = x ^ 2 := by
  rw [frobenius_apply]
  rfl

omit [Fintype F] in
theorem trace_bit (x : F) : traceF (ZMod 2) x = 0 ∨ traceF (ZMod 2) x = 1 := by
  unfold traceF
  generalize Algebra.trace (ZMod 2) F x = c
  fin_cases c
  · exact Or.inl (map_zero (algebraMap (ZMod 2) F))
  · exact Or.inr (map_one (algebraMap (ZMod 2) F))

theorem trace_sq (x : F) : traceF (ZMod 2) (x ^ 2) = traceF (ZMod 2) x := by
  simpa only [frobenius_binary] using trace_frobenius (K := ZMod 2) x

theorem trace_zero_iff_exists_binary (x : F) :
    traceF (ZMod 2) x = 0 ↔ ∃ t : F, t * (t + 1) = x := by
  have h (t : F) : frobenius (ZMod 2) F t - t = t * (t + 1) := by
    rw [frobenius_binary, CharTwo.sub_eq_add]
    ring
  simpa only [h] using trace_zero_iff_exists (K := ZMod 2) x

namespace Instance

variable (P : Instance (ZMod 2) F I J)

theorem honestU_binary (k : I) :
    P.honestU k = P.B k + P.basis.traceDual k * P.target + (P.mask k + P.mask k ^ 2) := by
  rw [honestU, frobenius_binary, CharTwo.sub_eq_add, CharTwo.sub_eq_add]
  ring

/-- Exact recovery of both original expanded linear equations, on the original
free-mask cells, with the actual coefficient transpose. -/
theorem nativeLinearVerify_binary (U delta : I → F) (A : F) :
    P.nativeLinearVerify U delta A ↔
      (∀ k, traceF (ZMod 2) (U k) = 0) ∧
      A = P.r + ∑ j : {k : I // k ≠ P.pivot},
        (delta j.1 + delta P.pivot * P.basis j.1) * P.masks j ∧
      (∑ k, delta k ^ 2 * U k) =
        (∑ i, (∑ k, delta k ^ 2 * coefficient P.basis P.coefficients i k) * P.words i) +
        (∑ k, delta k ^ 2 * P.basis.traceDual k) * P.target +
        (∑ j : {k : I // k ≠ P.pivot},
          (delta j.1 ^ 2 + delta P.pivot ^ 2 * P.basis j.1) * P.masks j) + (A ^ 2 + P.b) := by
  simp only [nativeLinearVerify, nativeOne, nativeTwo, wordCoeff, targetCoeff,
    frobenius_binary, CharTwo.sub_eq_add]

theorem nativeVerify_binary (U delta : I → F) (A : F) :
    P.nativeVerify U delta A ↔ P.nativeLinearVerify U delta A ∧ P.r * P.r = P.b := by
  simp only [nativeVerify, frobenius_binary, pow_two]

end Instance
end DualPacking.ArtinSchreier
