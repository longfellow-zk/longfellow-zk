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

/-- Union over the fixed committed-candidate list, not over possible scalar
responses. The latter can depend arbitrarily on the entire vector challenge. -/
theorem candidates_card_le {bound : ℕ} (values : Fin bound → Slot → F) (U : I → F) :
    (univ.filter fun delta => ∃ candidate, S.Bad (values candidate) U delta).card ≤
      bound * Fintype.card F ^ (Fintype.card I - 1) := by
  have he : (univ.filter fun delta => ∃ candidate, S.Bad (values candidate) U delta) =
      univ.biUnion (fun candidate : Fin bound => univ.filter (S.Bad (values candidate) U)) := by
    ext delta
    simp
  rw [he]
  exact card_biUnion_le.trans ((sum_le_sum fun candidate _ => S.bad_card_le (values candidate) U).trans_eq
    (by simp))

/-- Lift the native vector count to the common finite transcript alphabet.
Both balance equations are the same ideal-sampler assumptions used by the
existing graded frontend and Polygero theorems. -/
theorem sampled_candidates_card_le {C : Type} [Fintype C] {bound fiber unitFiber : ℕ}
    (decode : C → I → F)
    (hfiber : ∀ delta, (univ.filter fun c => decode c = delta).card ≤ fiber)
    (hbalanced : fiber * Fintype.card (I → F) = Fintype.card C)
    (hunit : unitFiber * Fintype.card F = Fintype.card C)
    (values : Fin bound → Slot → F) (U : I → F) :
    (univ.filter fun c => ∃ candidate, S.Bad (values candidate) U (decode c)).card ≤
      unitFiber * bound := by
  have hm : 1 ≤ Fintype.card I := Fintype.card_pos_iff.mpr ⟨S.pivot⟩
  have hfactor : fiber * Fintype.card F ^ (Fintype.card I - 1) = unitFiber := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < Fintype.card F from Fintype.card_pos)
    calc
      _ = fiber * Fintype.card (I → F) := by
        rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hm, Fintype.card_fun]
      _ = _ := hbalanced.trans hunit.symm
  have h := Bcs.card_decode_le decode fiber hfiber
    (fun delta => ∃ candidate, S.Bad (values candidate) U delta)
    (bound * Fintype.card F ^ (Fintype.card I - 1)) (by
      convert S.candidates_card_le values U using 1
      congr 1
      ext delta
      simp)
  convert h.trans_eq (show fiber * (bound * Fintype.card F ^ (Fintype.card I - 1)) =
    unitFiber * bound by
      calc
        _ = (fiber * Fintype.card F ^ (Fintype.card I - 1)) * bound := by ring
        _ = _ := by rw [hfactor]) using 1
  congr 1
  ext c
  simp

end LfzkV2.Packed.Statement
