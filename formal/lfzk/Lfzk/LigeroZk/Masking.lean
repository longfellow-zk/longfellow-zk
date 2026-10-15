import LigeroFamily.Protocol.Evaluation
import Mathlib.Tactic.FieldSimp

-- Ported verbatim from `proofs/ligero/LigeroFamily/ZeroKnowledge/Masking.lean` (only the import paths are rewritten);
-- `formal/ligero/` must not change, so the module lives under `Lfzk.LigeroZk`.
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LigeroFamily conditional response masking

The two main decomposition theorems cover different admissible subspaces.
Quadratic differences vanish on the witness suffix.  Special linear
differences vanish on the random prefix and satisfy the permitted witness
functional.  After a query has fixed the opened mask values, the remaining
base-row randomness surjects onto the corresponding subspace.
-/

namespace LigeroFamily

namespace MultiplicativeCode

variable {F : Type*} [Field F] {r w n : ℕ}
variable (C : MultiplicativeCode F r w n)

/-- The virtual affine direction identifies base rows with response rows that
vanish at all `k` Longfellow message positions. -/
theorem exists_vanishing_factor
    (M : C.MaskingBasis) (J : Finset (Fin n)) (hJ : J.card = C.k)
    (response : EvaluationRow F r w n) (hresponse : response ∈ C.response)
    (hzero : ∀ i : MessagePosition r w,
      response (Sum.inl i) = 0) :
    ∃ row : EvaluationRow F r w n, row ∈ C.base ∧
      response = rowMul M.vanishing row := by
  classical
  let S := codePositions (r := r) (w := w) J
  have hS : S.card ≤ C.k := by simp [S, hJ]
  let values : ↥S → F := fun i ↦
    response i.1 / M.vanishing i.1
  let row := C.interpolateBaseRow S hS values
  have hrow : row ∈ C.base := C.interpolateBaseRow_mem S hS values
  refine ⟨row, hrow, ?_⟩
  apply C.response_unique hresponse (M.vanishing_mul_mem hrow)
    (messagePositions r w n ∪ codePositions (r := r) (w := w) J)
  · rw [card_messagePositions_union_codePositions J, hJ, ← C.k_eq]
    omega
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rcases Finset.mem_image.mp hi with ⟨message, _, rfl⟩
      simp [rowMul, hzero, M.vanishing_message]
    · have hiS : i ∈ S := hi
      have hinterp := C.interpolateBaseRow_apply S hS values ⟨i, hiS⟩
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      change row (codePosition j) = _ at hinterp
      simp only [rowMul_apply]
      rw [hinterp]
      dsimp [values]
      field_simp [M.vanishing_code_ne j]

/-- Interpolate one base row with prescribed random-message values and zero
query openings.  The only rate condition used is `r ≤ w`. -/
theorem exists_base_random_query
    (Q : Finset (Fin n)) (hQ : Q.card = r) (hrw : r ≤ w)
    (values : Fin r → F) :
    ∃ row : EvaluationRow F r w n, row ∈ C.base ∧
      (∀ i, row (randomPosition i) = values i) ∧
      (∀ j ∈ Q, row (codePosition j) = 0) := by
  classical
  let S := randomPositions r w n ∪ codePositions (r := r) (w := w) Q
  have hS : S.card ≤ C.k := by
    rw [card_randomPositions_union_codePositions Q, hQ, C.k_eq]
    omega
  let prescribed : ↥S → F := fun i ↦
    match i.1 with
    | Sum.inl (Sum.inl a) => values a
    | _ => 0
  let row := C.interpolateBaseRow S hS prescribed
  refine ⟨row, C.interpolateBaseRow_mem S hS prescribed, ?_, ?_⟩
  · intro i
    have hi : randomPosition i ∈ S := by
      apply Finset.mem_union_left
      simp [randomPositions]
    simpa [prescribed, randomPosition] using
      C.interpolateBaseRow_apply S hS prescribed ⟨randomPosition i, hi⟩
  · intro j hj
    have hjS : codePosition j ∈ S := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    simpa [prescribed, codePosition] using
      C.interpolateBaseRow_apply S hS prescribed ⟨codePosition j, hjS⟩

/-- Interpolate one base row from its witness suffix and zero query openings.
The number of prescribed values is exactly `w+r=k`. -/
theorem exists_base_witness_query
    (Q : Finset (Fin n)) (hQ : Q.card = r) (values : Fin w → F) :
    ∃ row : EvaluationRow F r w n, row ∈ C.base ∧
      (∀ i, row (witnessPosition i) = values i) ∧
      (∀ j ∈ Q, row (codePosition j) = 0) := by
  classical
  let S := witnessPositions r w n ∪ codePositions (r := r) (w := w) Q
  have hS : S.card ≤ C.k := by
    rw [card_witnessPositions_union_codePositions Q, hQ,
      Nat.add_comm, ← C.k_eq]
  let prescribed : ↥S → F := fun i ↦
    match i.1 with
    | Sum.inl (Sum.inr a) => values a
    | _ => 0
  let row := C.interpolateBaseRow S hS prescribed
  refine ⟨row, C.interpolateBaseRow_mem S hS prescribed, ?_, ?_⟩
  · intro i
    have hi : witnessPosition i ∈ S := by
      apply Finset.mem_union_left
      simp [witnessPositions]
    simpa [prescribed, witnessPosition] using
      C.interpolateBaseRow_apply S hS prescribed ⟨witnessPosition i, hi⟩
  · intro j hj
    have hjS : codePosition j ∈ S := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    simpa [prescribed, codePosition] using
      C.interpolateBaseRow_apply S hS prescribed ⟨codePosition j, hjS⟩

/-- **Quadratic conditional masking lemma.**

Every response variation that is zero on the witness suffix and on the
opened columns is a sum of the `V` and `Z_W` mask directions. -/
theorem quadratic_mask_surjective
    (M : C.MaskingBasis) (Q : Finset (Fin n)) (hQ : Q.card = r)
    (hrw : r ≤ w) (J : Finset (Fin n)) (hJ : J.card = C.k)
    (response : EvaluationRow F r w n) (hresponse : response ∈ C.response)
    (hwitness : ∀ i, response (witnessPosition i) = 0)
    (hquery : ∀ j ∈ Q, response (codePosition j) = 0) :
    ∃ first second : EvaluationRow F r w n,
      first ∈ C.base ∧ second ∈ C.base ∧
      (∀ j ∈ Q, first (codePosition j) = 0) ∧
      (∀ j ∈ Q, second (codePosition j) = 0) ∧
      response = rowMul M.vanishing first + rowMul C.zW second := by
  obtain ⟨second, hsecond, hrandom, hsecondQ⟩ :=
    exists_base_random_query C Q hQ hrw
      (fun i ↦ response (randomPosition i))
  let residual := response - rowMul C.zW second
  have hresidual : residual ∈ C.response :=
    C.response.sub_mem hresponse (C.mul_mem C.zW_mem hsecond)
  have hzero : ∀ i : MessagePosition r w,
      residual (Sum.inl i) = 0 := by
    intro i
    cases i with
    | inl i =>
        change response (randomPosition i) -
          C.zW (randomPosition i) * second (randomPosition i) = 0
        rw [hrandom i, C.zW_random i]
        ring
    | inr i =>
        change response (witnessPosition i) -
          C.zW (witnessPosition i) * second (witnessPosition i) = 0
        rw [hwitness i, C.zW_witness i]
        ring
  obtain ⟨first, hfirst, hfactor⟩ :=
    exists_vanishing_factor C M J hJ residual hresidual hzero
  have hfirstQ : ∀ j ∈ Q, first (codePosition j) = 0 := by
    intro j hj
    have heval := congrFun hfactor (codePosition j)
    dsimp [residual] at heval
    simp only [hquery j hj, hsecondQ j hj, mul_zero, sub_zero] at heval
    exact (mul_eq_zero.mp heval.symm).resolve_left (M.vanishing_code_ne j)
  refine ⟨first, second, hfirst, hsecond, hfirstQ, hsecondQ, ?_⟩
  calc
    response = residual + rowMul C.zW second := by
      funext i
      simp [residual]
    _ = rowMul M.vanishing first + rowMul C.zW second := by rw [hfactor]

/-- **Special linear conditional masking lemma.**

For Ligero's coefficient rows `encode 0 A_w`, the unmasked linear response
vanishes on the random prefix.  The public factor `Z_R = encode 0 1` therefore
matches its complete witness suffix with one base row; the remaining response
vanishes at every message position and is a `V` multiple. -/
theorem linear_mask_surjective
    (M : C.MaskingBasis) (Q : Finset (Fin n)) (hQ : Q.card = r)
    (J : Finset (Fin n)) (hJ : J.card = C.k)
    (Λ : (Fin w → F) →ₗ[F] F)
    (response : EvaluationRow F r w n) (hresponse : response ∈ C.response)
    (hrandom : ∀ i, response (randomPosition i) = 0)
    (hfunctional : Λ (witnessValues response) = 0)
    (hquery : ∀ j ∈ Q, response (codePosition j) = 0) :
    ∃ first second : EvaluationRow F r w n,
      first ∈ C.base ∧ second ∈ C.base ∧
      Λ (witnessValues second) = 0 ∧
      (∀ j ∈ Q, first (codePosition j) = 0) ∧
      (∀ j ∈ Q, second (codePosition j) = 0) ∧
      response = rowMul M.vanishing first + rowMul C.zR second := by
  obtain ⟨second, hsecond, hsecondW, hsecondQ⟩ :=
    exists_base_witness_query C Q hQ (witnessValues response)
  let residual := response - rowMul C.zR second
  have hresidual : residual ∈ C.response :=
    C.response.sub_mem hresponse (C.mul_mem C.zR_mem hsecond)
  have hzero : ∀ i : MessagePosition r w,
      residual (Sum.inl i) = 0 := by
    intro i
    cases i with
    | inl i =>
        change response (randomPosition i) -
          C.zR (randomPosition i) * second (randomPosition i) = 0
        rw [hrandom i, C.zR_random i]
        simp
    | inr i =>
        change response (witnessPosition i) -
          C.zR (witnessPosition i) * second (witnessPosition i) = 0
        rw [C.zR_witness, hsecondW i]
        simp [witnessValues]
  obtain ⟨first, hfirst, hfactor⟩ :=
    exists_vanishing_factor C M J hJ residual hresidual hzero
  have hfirstQ : ∀ j ∈ Q, first (codePosition j) = 0 := by
    intro j hj
    have heval := congrFun hfactor (codePosition j)
    dsimp [residual] at heval
    simp only [hquery j hj, hsecondQ j hj, mul_zero, sub_zero] at heval
    exact (mul_eq_zero.mp heval.symm).resolve_left (M.vanishing_code_ne j)
  have hsecondFunctional : Λ (witnessValues second) = 0 := by
    have heq : witnessValues second = witnessValues response := by
      funext i
      exact hsecondW i
    rw [heq]
    exact hfunctional
  refine ⟨first, second, hfirst, hsecond, hsecondFunctional,
    hfirstQ, hsecondQ, ?_⟩
  calc
    response = residual + rowMul C.zR second := by
      funext i
      simp [residual]
    _ = rowMul M.vanishing first + rowMul C.zR second := by rw [hfactor]

end MultiplicativeCode

end LigeroFamily
