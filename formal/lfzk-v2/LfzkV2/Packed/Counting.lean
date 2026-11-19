import LfzkV2.Packed.Backend
import LfzkV2.ChallengeBlocks

/-! The packing escape is measured at its vector challenge, before the scalar
response and Polygero challenges. Eliminating the response is essential: the
bad event must be determined by the fixed prefix and this one oracle answer. -/

namespace LfzkV2.Packed.Statement

open Finset DualPacking DualPacking.ArtinSchreier
open scoped Classical

variable {K F I J Slot : Type} [Field K] [Fintype K] [Field F] [Fintype F]
  [DecidableEq F] [Algebra K F] [Fintype I] [DecidableEq I] [Fintype J]
variable (S : Packed.Statement K F I J Slot)

/-- A false source claim surviving the packing challenge. No later response,
backend challenge, queried column, or opening occurs in this predicate. -/
noncomputable def Bad (values : Slot → F) (U delta : I → F) : Prop :=
  let P := S.realize values
  P.target ≠ P.trueValue ∧ (∀ k, traceF K (U k) = 0) ∧
    (∑ k, P.error U k * frobenius K F (delta k)) = P.offset

theorem target_or_bad (values : Slot → F) (U delta : I → F) (A : F)
    (hverify : (S.realize values).nativeLinearVerify U delta A) :
    (S.realize values).target = (S.realize values).trueValue ∨ S.Bad values U delta := by
  by_cases h : (S.realize values).target = (S.realize values).trueValue
  · exact Or.inl h
  · exact Or.inr ⟨h, hverify.1,
      (S.realize values).linear_acceptance_forces_affine_dot U delta A
        (((S.realize values).linearVerify_iff_native U delta A).mpr hverify)⟩

theorem bad_card_le (values : Slot → F) (U : I → F) :
    (univ.filter (S.Bad values U)).card ≤ Fintype.card F ^ (Fintype.card I - 1) := by
  by_cases hf : (S.realize values).target ≠ (S.realize values).trueValue
  · by_cases ht : ∀ k, traceF K (U k) = 0
    · simpa [Bad, hf, ht] using
        frobenius_affine_card_le (K := K) ((S.realize values).error U)
          ((S.realize values).error_ne_zero U ht hf) (S.realize values).offset
    · simp [Bad, ht]
  · simp [Bad, hf]

end LfzkV2.Packed.Statement
