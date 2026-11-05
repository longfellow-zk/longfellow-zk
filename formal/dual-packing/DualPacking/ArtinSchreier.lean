import DualPacking.ArtinSchreierAlgebra
import DualPacking.Counting

/-! # Trace-zero dual packing over arbitrary finite fields

The complete first response is fixed before an independent vector challenge.
The second scalar response may depend on that challenge. The native checks
are field-linear; the unchecked Frobenius cell contributes a fixed offset.
-/

namespace DualPacking.ArtinSchreier

open Finset Module
open scoped Classical

variable {K F I J : Type*} [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]
  [Fintype I] [DecidableEq I] [Fintype J]

/-- The actual committed cells and canonical base-field coordinates. -/
structure Instance (K F I J : Type*) [Field K] [Field F] [Algebra K F] where
  basis : Basis I K F
  pivot : I
  words : J → F
  coefficients : J → I → F
  target : F
  masks : {k : I // k ≠ pivot} → F
  r : F
  b : F

namespace Instance

variable (P : Instance K F I J)

noncomputable def mask (k : I) : F :=
  if h : k = P.pivot then
    ∑ j : {k : I // k ≠ P.pivot}, P.basis j.1 * P.masks j
  else P.masks ⟨k, h⟩

noncomputable def trueValue : F := value P.basis P.coefficients P.words

noncomputable def B (k : I) : F := forms P.basis P.coefficients P.words k

noncomputable def honestU (k : I) : F :=
  P.B k - P.basis.traceDual k * P.target + (frobenius K F (P.mask k) - P.mask k)

noncomputable def honestA (delta : I → F) : F := P.r + ∑ k, delta k * P.mask k

noncomputable def wordCoeff (delta : I → F) (i : J) : F :=
  ∑ k, frobenius K F (delta k) * coefficient P.basis P.coefficients i k

noncomputable def targetCoeff (delta : I → F) : F :=
  ∑ k, frobenius K F (delta k) * P.basis.traceDual k

noncomputable def linearOne (delta : I → F) (A : F) : Prop := A = P.honestA delta

/-- Frobenius is evaluated on the public response. Every committed cell is linear. -/
noncomputable def linearTwo (U delta : I → F) (A : F) : Prop :=
  (∑ k, frobenius K F (delta k) * U k) = (∑ i, P.wordCoeff delta i * P.words i) -
    P.targetCoeff delta * P.target - (∑ k, frobenius K F (delta k) * P.mask k) +
    (frobenius K F A - P.b)

noncomputable def linearVerify (U delta : I → F) (A : F) : Prop :=
  (∀ k, traceF K (U k) = 0) ∧ P.linearOne delta A ∧ P.linearTwo U delta A

/-- Optional stronger verifier; the main soundness theorem does not use this check. -/
noncomputable def verify (U delta : I → F) (A : F) : Prop :=
  P.linearVerify U delta A ∧ frobenius K F P.r = P.b

noncomputable def error (U : I → F) (k : I) : F := U k - P.honestU k

noncomputable def offset : F := frobenius K F P.r - P.b

theorem trace_honestU (k : I) :
    traceF K (P.honestU k) = digit P.basis P.trueValue k - digit P.basis P.target k := by
  rw [honestU, trace_add, trace_mask, add_zero, trace_sub, B, trace_forms, trace_dual]
  rfl

theorem trace_error (U : I → F) (k : I) :
    traceF K (P.error U k) = traceF K (U k) -
      (digit P.basis P.trueValue k - digit P.basis P.target k) := by
  rw [error, trace_sub, P.trace_honestU]

theorem error_ne_zero (U : I → F) (htrace : ∀ k, traceF K (U k) = 0)
    (hfalse : P.target ≠ P.trueValue) : ∃ k, P.error U k ≠ 0 := by
  by_contra! hz
  have hd : ∀ k, digit P.basis P.target k = digit P.basis P.trueValue k := by
    intro k
    have h := P.trace_error U k
    rw [hz k, htrace k, show traceF K (0 : F) = 0 by simp [traceF], zero_sub] at h
    exact (sub_eq_zero.mp (neg_eq_zero.mp h.symm)).symm
  apply hfalse
  apply P.basis.repr.injective
  ext k
  exact (algebraMap K F).injective (hd k)

theorem contract_words (delta : I → F) :
    (∑ i, P.wordCoeff delta i * P.words i) = ∑ k, frobenius K F (delta k) * P.B k := by
  simp only [wordCoeff, B, forms, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro i _
  ring

theorem contract_honestU (delta : I → F) :
    (∑ k, frobenius K F (delta k) * P.honestU k) =
      (∑ i, P.wordCoeff delta i * P.words i) - P.targetCoeff delta * P.target +
      (∑ k, frobenius K F (delta k) * frobenius K F (P.mask k)) -
      (∑ k, frobenius K F (delta k) * P.mask k) := by
  rw [P.contract_words]
  simp only [honestU, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib,
    targetCoeff, sum_mul, mul_assoc]
  ring

omit [Fintype J] in
/-- The public response authenticates the entire Frobenius contribution up to
an arbitrary fixed offset. No consistency of the committed cell is assumed. -/
theorem combined_frobenius_offset (delta : I → F) (A : F)
    (hA : P.linearOne delta A) :
    frobenius K F A - P.b =
      (∑ k, frobenius K F (delta k) * frobenius K F (P.mask k)) + P.offset := by
  rw [linearOne, honestA] at hA
  rw [hA, map_add, map_sum]
  simp only [map_mul, offset]
  ring

theorem linearTwo_iff_affine_dot (U delta : I → F) (A : F)
    (hA : P.linearOne delta A) :
    P.linearTwo U delta A ↔ ∑ k, P.error U k * frobenius K F (delta k) = P.offset := by
  have he : (∑ k, P.error U k * frobenius K F (delta k)) =
      (∑ k, frobenius K F (delta k) * U k) -
        ∑ k, frobenius K F (delta k) * P.honestU k := by
    simp only [error, sub_mul, sum_sub_distrib, mul_comm]
  rw [P.contract_honestU] at he
  rw [linearTwo, P.combined_frobenius_offset delta A hA]
  constructor <;> intro h
  · linear_combination he + h
  · linear_combination h - he

theorem linear_acceptance_forces_affine_dot (U delta : I → F) (A : F)
    (h : P.linearVerify U delta A) :
    ∑ k, P.error U k * frobenius K F (delta k) = P.offset :=
  (P.linearTwo_iff_affine_dot U delta A h.2.1).mp h.2.2

theorem acceptance_forces_dot (U delta : I → F) (A : F)
    (h : P.verify U delta A) : ∑ k, P.error U k * frobenius K F (delta k) = 0 := by
  have he := P.linear_acceptance_forces_affine_dot U delta A h.1
  simpa only [offset, h.2, sub_self] using he

theorem linear_completeness (htrue : P.target = P.trueValue)
    (hM : frobenius K F P.r = P.b) (delta : I → F) :
    P.linearVerify P.honestU delta (P.honestA delta) := by
  refine ⟨?_, rfl, (P.linearTwo_iff_affine_dot _ _ _ rfl).mpr ?_⟩
  · intro k
    rw [P.trace_honestU, htrue, sub_self]
  · simp only [error, offset, hM, sub_self, zero_mul, sum_const_zero]

theorem completeness (htrue : P.target = P.trueValue)
    (hM : frobenius K F P.r = P.b) (delta : I → F) :
    P.verify P.honestU delta (P.honestA delta) :=
  ⟨P.linear_completeness htrue hM delta, hM⟩

end Instance

/-- The actual relative Frobenius is a permutation of each challenge coordinate. -/
theorem frobenius_affine_card_le [DecidableEq F] (E : I → F)
    (hE : ∃ k, E k ≠ 0) (c : F) :
    (univ.filter fun delta : I → F => ∑ k, E k * frobenius K F (delta k) = c).card ≤
      Fintype.card F ^ (Fintype.card I - 1) := by
  have hinj : Function.Injective (fun delta : I → F => fun k => frobenius K F (delta k)) := by
    intro d e h
    funext k
    exact (frobenius K F).injective (congrFun h k)
  have hmap := card_le_card_of_injOn (fun delta : I → F => fun k => frobenius K F (delta k))
    (s := univ.filter fun delta => ∑ k, E k * frobenius K F (delta k) = c)
    (t := univ.filter fun gamma => ∑ k, E k * gamma k = c)
    (by intro delta hd; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hd).2⟩)
    hinj.injOn
  exact hmap.trans (DualPacking.affine_batch_card_le E hE c)

theorem frobenius_batch_card_le [DecidableEq F] (E : I → F) (hE : ∃ k, E k ≠ 0) :
    (univ.filter fun delta : I → F => ∑ k, E k * frobenius K F (delta k) = 0).card ≤
      Fintype.card F ^ (Fintype.card I - 1) := frobenius_affine_card_le E hE 0
namespace Instance

variable [DecidableEq F] (P : Instance K F I J)

/-- Only the second scalar response can depend on the random challenge. -/
noncomputable def linearAcceptingCoins (U : I → F) (respondA : (I → F) → F) : Finset (I → F) :=
  univ.filter fun delta => P.linearVerify U delta (respondA delta)

/-- Soundness without the Frobenius-consistency gate, allowing an arbitrary committed offset. -/
theorem linear_soundness_card (U : I → F) (respondA : (I → F) → F)
    (hfalse : P.target ≠ P.trueValue) :
    (P.linearAcceptingCoins U respondA).card ≤ Fintype.card F ^ (Fintype.card I - 1) := by
  by_cases htrace : ∀ k, traceF K (U k) = 0
  · have hsub : P.linearAcceptingCoins U respondA ⊆
        univ.filter fun delta => ∑ k, P.error U k * frobenius K F (delta k) = P.offset := by
      intro delta hd
      exact mem_filter.mpr ⟨mem_univ _,
        P.linear_acceptance_forces_affine_dot U delta _ (mem_filter.mp hd).2⟩
    exact (card_le_card hsub).trans
      (frobenius_affine_card_le (K := K) (P.error U) (P.error_ne_zero U htrace hfalse) P.offset)
  · have hempty : P.linearAcceptingCoins U respondA = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro delta hd
      exact htrace (mem_filter.mp hd).2.1
    simp [hempty]

theorem linear_soundness_scaled (U : I → F) (respondA : (I → F) → F)
    (hfalse : P.target ≠ P.trueValue) :
    Fintype.card F * (P.linearAcceptingCoins U respondA).card ≤ Fintype.card (I → F) := by
  have hm : 1 ≤ Fintype.card I := Fintype.card_pos_iff.mpr ⟨P.pivot⟩
  calc
    _ ≤ Fintype.card F * Fintype.card F ^ (Fintype.card I - 1) :=
      Nat.mul_le_mul_left _ (P.linear_soundness_card U respondA hfalse)
    _ = _ := by
      rw [Fintype.card_fun, mul_comm, ← pow_succ, Nat.sub_add_cancel hm]

noncomputable def linearAcceptanceProbability (U : I → F) (respondA : (I → F) → F) : ℚ :=
  (P.linearAcceptingCoins U respondA).card / Fintype.card (I → F)

/-- The simplified verifier has the same bound without enforcing `frobenius K F r = b`. -/
theorem linear_soundness_probability (U : I → F) (respondA : (I → F) → F)
    (hfalse : P.target ≠ P.trueValue) :
    P.linearAcceptanceProbability U respondA ≤ 1 / (Fintype.card F : ℚ) := by
  have h := P.linear_soundness_scaled U respondA hfalse
  have hq : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hc : (0 : ℚ) < Fintype.card (I → F) := by exact_mod_cast Fintype.card_pos
  rw [linearAcceptanceProbability, div_le_div_iff₀ hc hq]
  simpa only [mul_one, one_mul, mul_comm] using (show
    (Fintype.card F : ℚ) * (P.linearAcceptingCoins U respondA).card ≤
      Fintype.card (I → F) by exact_mod_cast h)

/-- Compatibility endpoints for the original, stronger checked-Frobenius verifier. -/
noncomputable def acceptingCoins (U : I → F) (respondA : (I → F) → F) : Finset (I → F) :=
  univ.filter fun delta => P.verify U delta (respondA delta)

omit [DecidableEq F] in
theorem acceptingCoins_subset (U : I → F) (respondA : (I → F) → F) :
    P.acceptingCoins U respondA ⊆ P.linearAcceptingCoins U respondA := by
  intro delta hd
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hd).2.1⟩

theorem soundness_card (U : I → F) (respondA : (I → F) → F)
    (hfalse : P.target ≠ P.trueValue) :
    (P.acceptingCoins U respondA).card ≤ Fintype.card F ^ (Fintype.card I - 1) :=
  (card_le_card (P.acceptingCoins_subset U respondA)).trans
    (P.linear_soundness_card U respondA hfalse)

noncomputable def acceptanceProbability (U : I → F) (respondA : (I → F) → F) : ℚ :=
  (P.acceptingCoins U respondA).card / Fintype.card (I → F)

theorem soundness_probability (U : I → F) (respondA : (I → F) → F)
    (hfalse : P.target ≠ P.trueValue) :
    P.acceptanceProbability U respondA ≤ 1 / (Fintype.card F : ℚ) := by
  apply le_trans _ (P.linear_soundness_probability U respondA hfalse)
  exact div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (card_le_card (P.acceptingCoins_subset U respondA))) (Nat.cast_nonneg _)

end Instance
end DualPacking.ArtinSchreier
