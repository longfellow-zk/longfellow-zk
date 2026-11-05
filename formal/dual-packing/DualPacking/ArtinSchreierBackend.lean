import DualPacking.ArtinSchreier

/-! # Expanded native constraints for the dependent-mask refinement -/

namespace DualPacking.ArtinSchreier.Instance

open Finset Module
open scoped Classical

variable {K F I J : Type*} [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]
  [Fintype I] [DecidableEq I] [Fintype J]

variable (P : Instance K F I J)

omit [Fintype K] [Fintype F] [Fintype J] in
/-- Exact number of adapter cells: free masks and the two scalar cells. -/
theorem adapterCell_count :
    Fintype.card ({k : I // k ≠ P.pivot} ⊕ Fin 2) = Fintype.card I + 1 := by
  have hm : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨P.pivot⟩
  simp only [Fintype.card_sum, Fintype.card_fin]
  have hc : Fintype.card {k : I // k ≠ P.pivot} = Fintype.card I - 1 := by simp
  rw [hc]
  omega

omit [Fintype K] [Fintype F] [Fintype J] [DecidableEq I] in
/-- The first response has one field element per coordinate, followed by the scalar. -/
theorem proverMessage_count : Fintype.card (I ⊕ Unit) = Fintype.card I + 1 := by
  simp

omit [Fintype K] [Fintype F] [Fintype J] in
/-- Eliminate the dependent zeroth mask, using only the original free cells. -/
theorem contract_mask (w : I → F) :
    (∑ k, w k * P.mask k) =
      ∑ j : {k : I // k ≠ P.pivot},
        (w j.1 + w P.pivot * P.basis j.1) * P.masks j := by
  have he : (∑ k ∈ univ.erase P.pivot, w k * P.mask k) =
      ∑ j : {k : I // k ≠ P.pivot}, w j.1 * P.masks j := by
    rw [Finset.sum_subtype (p := fun k : I => k ≠ P.pivot) (univ.erase P.pivot) (by intro k; simp)
      (fun k => w k * P.mask k)]
    apply sum_congr rfl
    intro j _
    simp only [mask, dif_neg j.2]
  rw [← sum_erase_add univ (fun k => w k * P.mask k) (mem_univ P.pivot), he]
  have hp : P.mask P.pivot =
      ∑ j : {k : I // k ≠ P.pivot}, P.basis j.1 * P.masks j := by simp [mask]
  rw [hp, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  ring

noncomputable def nativeOne (delta : I → F) (A : F) : Prop :=
  A = P.r + ∑ j : {k : I // k ≠ P.pivot},
    (delta j.1 + delta P.pivot * P.basis j.1) * P.masks j

noncomputable def nativeTwo (U delta : I → F) (A : F) : Prop :=
  (∑ k, frobenius K F (delta k) * U k) = (∑ i, P.wordCoeff delta i * P.words i) -
    P.targetCoeff delta * P.target -
    (∑ j : {k : I // k ≠ P.pivot},
      (frobenius K F (delta j.1) + frobenius K F (delta P.pivot) * P.basis j.1) * P.masks j) +
    (frobenius K F A - P.b)

/-- Simplified verification entirely in terms of actual committed cells. -/
noncomputable def nativeLinearVerify (U delta : I → F) (A : F) : Prop :=
  (∀ k, traceF K (U k) = 0) ∧ P.nativeOne delta A ∧ P.nativeTwo U delta A

/-- Optional stronger acceptance predicate, retained for comparison. -/
noncomputable def nativeVerify (U delta : I → F) (A : F) : Prop :=
  P.nativeLinearVerify U delta A ∧ frobenius K F P.r = P.b

theorem linearVerify_iff_native (U delta : I → F) (A : F) :
    P.linearVerify U delta A ↔ P.nativeLinearVerify U delta A := by
  simp only [linearVerify, linearOne, honestA, linearTwo, P.contract_mask,
    nativeLinearVerify, nativeOne, nativeTwo]

theorem verify_iff_native (U delta : I → F) (A : F) :
    P.verify U delta A ↔ P.nativeVerify U delta A := by
  rw [verify, nativeVerify, P.linearVerify_iff_native]

/-- Expand a hidden affine target directly into public coefficients on its
original committed cells. No separate target cell or late commitment is needed. -/
theorem nativeLinearVerify_affine {S : Type*} [Fintype S]
    (c : F) (coeff aux : S → F) (htarget : P.target = c + ∑ s, coeff s * aux s)
    (U delta : I → F) (A : F) :
    P.nativeLinearVerify U delta A ↔
      (∀ k, traceF K (U k) = 0) ∧ P.nativeOne delta A ∧
      (∑ k, frobenius K F (delta k) * U k) =
        (∑ i, P.wordCoeff delta i * P.words i) - P.targetCoeff delta * c -
        (∑ s, (P.targetCoeff delta * coeff s) * aux s) -
        (∑ j : {k : I // k ≠ P.pivot},
          (frobenius K F (delta j.1) + frobenius K F (delta P.pivot) * P.basis j.1) *
            P.masks j) + (frobenius K F A - P.b) := by
  simp only [nativeLinearVerify, nativeTwo, htarget, mul_add, mul_sum,
    mul_assoc, sub_add_eq_sub_sub]

theorem native_linear_completeness (htrue : P.target = P.trueValue) (hM : frobenius K F P.r = P.b)
    (delta : I → F) : P.nativeLinearVerify P.honestU delta (P.honestA delta) :=
  (P.linearVerify_iff_native _ _ _).mp (P.linear_completeness htrue hM delta)

theorem native_completeness (htrue : P.target = P.trueValue) (hM : frobenius K F P.r = P.b)
    (delta : I → F) : P.nativeVerify P.honestU delta (P.honestA delta) :=
  (P.verify_iff_native _ _ _).mp (P.completeness htrue hM delta)

variable [DecidableEq F]

noncomputable def nativeLinearAcceptingCoins (U : I → F) (respondA : (I → F) → F) : Finset (I → F) :=
  univ.filter fun delta => P.nativeLinearVerify U delta (respondA delta)

omit [DecidableEq F] in
theorem nativeLinearAcceptingCoins_eq (U : I → F) (respondA : (I → F) → F) :
    P.nativeLinearAcceptingCoins U respondA = P.linearAcceptingCoins U respondA := by
  ext delta
  simp [nativeLinearAcceptingCoins, linearAcceptingCoins, P.linearVerify_iff_native]

noncomputable def nativeLinearAcceptanceProbability (U : I → F) (respondA : (I → F) → F) : ℚ :=
  (P.nativeLinearAcceptingCoins U respondA).card / Fintype.card (I → F)

/-- The reported bound for the expanded verifier with no multiplication check.
Both committed scalar cells are arbitrary; the offset is counted affinely. -/
theorem linear_native_soundness_probability (U : I → F) (respondA : (I → F) → F)
    (hfalse : P.target ≠ P.trueValue) :
    P.nativeLinearAcceptanceProbability U respondA ≤ 1 / (Fintype.card F : ℚ) := by
  rw [nativeLinearAcceptanceProbability, P.nativeLinearAcceptingCoins_eq]
  exact P.linear_soundness_probability U respondA hfalse

/-- Charge failure of an external backend to enforce either linear equation. -/
theorem linear_backend_composition_card (U : I → F) (respondA : (I → F) → F)
    (backendAccepts : (I → F) → Prop) (hfalse : P.target ≠ P.trueValue) :
    (univ.filter backendAccepts).card ≤ Fintype.card F ^ (Fintype.card I - 1) +
      (univ.filter fun delta => backendAccepts delta ∧
        ¬P.nativeLinearVerify U delta (respondA delta)).card := by
  let bad := univ.filter fun delta => backendAccepts delta ∧
    ¬P.nativeLinearVerify U delta (respondA delta)
  have hsub : univ.filter backendAccepts ⊆ P.nativeLinearAcceptingCoins U respondA ∪ bad := by
    intro delta hd
    by_cases hv : P.nativeLinearVerify U delta (respondA delta)
    · exact mem_union_left _ (by simp [nativeLinearAcceptingCoins, hv])
    · exact mem_union_right _ (by simpa [bad, hv] using hd)
  calc
    _ ≤ (P.nativeLinearAcceptingCoins U respondA ∪ bad).card := card_le_card hsub
    _ ≤ (P.nativeLinearAcceptingCoins U respondA).card + bad.card := card_union_le _ _
    _ ≤ _ := by
      rw [P.nativeLinearAcceptingCoins_eq]
      exact Nat.add_le_add_right (P.linear_soundness_card U respondA hfalse) _

noncomputable def nativeAcceptingCoins (U : I → F) (respondA : (I → F) → F) : Finset (I → F) :=
  univ.filter fun delta => P.nativeVerify U delta (respondA delta)

omit [DecidableEq F] in
theorem nativeAcceptingCoins_eq (U : I → F) (respondA : (I → F) → F) :
    P.nativeAcceptingCoins U respondA = P.acceptingCoins U respondA := by
  ext delta
  simp [nativeAcceptingCoins, acceptingCoins, P.verify_iff_native]

noncomputable def nativeAcceptanceProbability (U : I → F) (respondA : (I → F) → F) : ℚ :=
  (P.nativeAcceptingCoins U respondA).card / Fintype.card (I → F)

/-- The reported bound is connected to both expanded native linear constraints
and the optional Frobenius-consistency check. There are no hypotheses about mask honesty. -/
theorem native_soundness_probability (U : I → F) (respondA : (I → F) → F)
    (hfalse : P.target ≠ P.trueValue) :
    P.nativeAcceptanceProbability U respondA ≤ 1 / (Fintype.card F : ℚ) := by
  rw [nativeAcceptanceProbability, P.nativeAcceptingCoins_eq]
  exact P.soundness_probability U respondA hfalse

/-- Backend failure remains an explicit event, including failure of the Frobenius-consistency
gate. The adapter's numerical bound is not used as a total-system bound. -/
theorem backend_composition_card (U : I → F) (respondA : (I → F) → F)
    (backendAccepts : (I → F) → Prop) (hfalse : P.target ≠ P.trueValue) :
    (univ.filter backendAccepts).card ≤ Fintype.card F ^ (Fintype.card I - 1) +
      (univ.filter fun delta => backendAccepts delta ∧
        ¬P.nativeVerify U delta (respondA delta)).card := by
  let bad := univ.filter fun delta => backendAccepts delta ∧
    ¬P.nativeVerify U delta (respondA delta)
  have hsub : univ.filter backendAccepts ⊆ P.nativeAcceptingCoins U respondA ∪ bad := by
    intro delta hd
    by_cases hv : P.nativeVerify U delta (respondA delta)
    · exact mem_union_left _ (by simp [nativeAcceptingCoins, hv])
    · exact mem_union_right _ (by simpa [bad, hv] using hd)
  calc
    _ ≤ (P.nativeAcceptingCoins U respondA ∪ bad).card := card_le_card hsub
    _ ≤ (P.nativeAcceptingCoins U respondA).card + bad.card := card_union_le _ _
    _ ≤ _ := by
      rw [P.nativeAcceptingCoins_eq]
      exact Nat.add_le_add_right (P.soundness_card U respondA hfalse) _

end DualPacking.ArtinSchreier.Instance

namespace DualPacking.ArtinSchreier

section FiniteBase

variable {K F I J : Type*} [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq F]

/-- The field cardinality is derived from the actual basis consumed by the verifier. -/
theorem linear_soundness_by_basis_size (P : Instance K F I J)
    (U : I → F) (respondA : (I → F) → F) (hfalse : P.target ≠ P.trueValue) :
    P.nativeLinearAcceptanceProbability U respondA ≤
      1 / (Fintype.card K : ℚ) ^ Fintype.card I := by
  have h := P.linear_native_soundness_probability U respondA hfalse
  rw [DualPacking.extension_card P.basis] at h
  simpa only [Nat.cast_pow] using h

/-- Exact specialization to an extension of degree six over any finite base field. -/
theorem linear_soundness_degree_six (P : Instance K F (Fin 6) J)
    (U : Fin 6 → F) (respondA : (Fin 6 → F) → F) (hfalse : P.target ≠ P.trueValue) :
    P.nativeLinearAcceptanceProbability U respondA ≤ 1 / (Fintype.card K : ℚ) ^ 6 := by
  simpa only [Fintype.card_fin] using linear_soundness_by_basis_size P U respondA hfalse

end FiniteBase

section PrimeBase

variable {p : ℕ} [Fact p.Prime] {F J : Type*} [Field F] [Fintype F]
  [Algebra (ZMod p) F] [Fintype J] [DecidableEq F]

/-- Prime-field instance of the same native verifier; no field-size premise is assumed. -/
theorem linear_soundness_prime_degree_six (P : Instance (ZMod p) F (Fin 6) J)
    (U : Fin 6 → F) (respondA : (Fin 6 → F) → F) (hfalse : P.target ≠ P.trueValue) :
    P.nativeLinearAcceptanceProbability U respondA ≤ 1 / (p : ℚ) ^ 6 := by
  simpa only [ZMod.card] using linear_soundness_degree_six P U respondA hfalse

end PrimeBase

variable {F J : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [Fintype J] [DecidableEq F]

/-- Exact certificate for the simplified native verifier. -/
theorem linear_soundness_binary128 (P : Instance (ZMod 2) F (Fin 128) J)
    (U : Fin 128 → F) (respondA : (Fin 128 → F) → F)
    (hfalse : P.target ≠ P.trueValue) :
    P.nativeLinearAcceptanceProbability U respondA ≤ (1 : ℚ) / 2 ^ 128 := by
  have h := P.linear_native_soundness_probability U respondA hfalse
  have hc := DualPacking.binary_card P.basis
  simp only [Fintype.card_fin] at hc
  rw [hc] at h
  exact h

/-- Exact binary-field certificate for the same expanded verifier. -/
theorem soundness_binary128 (P : Instance (ZMod 2) F (Fin 128) J)
    (U : Fin 128 → F) (respondA : (Fin 128 → F) → F)
    (hfalse : P.target ≠ P.trueValue) :
    P.nativeAcceptanceProbability U respondA ≤ (1 : ℚ) / 2 ^ 128 := by
  have h := P.native_soundness_probability U respondA hfalse
  have hc := DualPacking.binary_card P.basis
  simp only [Fintype.card_fin] at hc
  rw [hc] at h
  exact h

end DualPacking.ArtinSchreier
