import LfzkV1.LigeroZk.CoreTranslation
import polygero.Protocol.Rows

/-!
# Polygero arithmetic-mask translation

Reuse V1's interpolation and conditional linear-mask theorem for Polygero's
actual two checked rows, `V*u + z_R*m`. The second row has zero sum on exactly
the constraint-visible witness coordinates. A residual response that vanishes
at the opened columns can be absorbed while preserving both opened mask rows.

The public response correction includes a `z_R` factor: unlike V1's direct
response mask, Polygero's arithmetic response must vanish on the random prefix.
This module supplies the arithmetic part of the joint simulator, not the
complete compiled zero-knowledge theorem.
-/

namespace LfzkV2.PolygeroMasking

open LigeroFamily MultiplicativeCode

variable {F : Type} [Field F]
variable {r w n q : ℕ}

/-- The full two-row mask tape, before conditioning on any openings. -/
abbrev Tape (C : MultiplicativeCode F r w n) (Λ : (Fin w → F) →ₗ[F] F) :=
  LinearMaskSource C ∅ Λ

/-- Forget the zero-opening condition on a residual mask adjustment. -/
def forgetOpenings (C : MultiplicativeCode F r w n) (Q : Finset (Fin n))
    (Λ : (Fin w → F) →ₗ[F] F) (masks : LinearMaskSource C Q Λ) : Tape C Λ where
  vCoefficient := ⟨masks.vCoefficient.1, masks.vCoefficient.2.1, by simp⟩
  zRCoefficient := ⟨masks.zRCoefficient.1, masks.zRCoefficient.2.1,
    by simp, masks.zRCoefficient.2.2.2⟩

noncomputable def response (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Λ : (Fin w → F) →ₗ[F] F) (masks : Tape C Λ) : EvaluationRow F r w n :=
  (linearMaskMap C M ∅ Λ masks).1

def maskRows {C : MultiplicativeCode F r w n} {Λ : (Fin w → F) →ₗ[F] F}
    (masks : Tape C Λ) : LinearConstraintMask → EvaluationRow F r w n
  | .vCoefficient => masks.vCoefficient.1
  | .zRCoefficient => masks.zRCoefficient.1

/-- This is the same mask expression as the physical Polygero verifier. -/
theorem response_eq_linearMask (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Λ : (Fin w → F) →ₗ[F] F) (masks : Tape C Λ) :
    response C M Λ masks = DirectVerifier.linearMask C M (maskRows masks) := rfl

theorem response_add (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Λ : (Fin w → F) →ₗ[F] F) (a b : Tape C Λ) :
    response C M Λ (a+b) = response C M Λ a + response C M Λ b := by
  funext i
  simp [response, linearMaskMap, rowMul]
  ring

/-- V1's surjectivity theorem supplies a legal two-row adjustment for every
admissible Polygero arithmetic-response difference. -/
noncomputable def adjustment (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : QuerySet n r) (Λ : (Fin w → F) →ₗ[F] F)
    (delta : linearResponseKernel C Q.coordinates Λ) : LinearMaskSource C Q.coordinates Λ :=
  Classical.choose (linearMaskMap_surjective C M Q.coordinates
    (QuerySet.card_coordinates Q) (interpolationQuery C).coordinates
    (interpolationQuery_card C) Λ delta)

theorem adjustment_response (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : QuerySet n r) (Λ : (Fin w → F) →ₗ[F] F)
    (delta : linearResponseKernel C Q.coordinates Λ) :
    response C M Λ (forgetOpenings C Q.coordinates Λ (adjustment C M Q Λ delta)) = delta.1 :=
  congrArg Subtype.val (Classical.choose_spec (linearMaskMap_surjective C M Q.coordinates
    (QuerySet.card_coordinates Q) (interpolationQuery C).coordinates
    (interpolationQuery_card C) Λ delta))

/-- Translating the complete tape, rather than just a response polynomial,
also preserves its uniform finite distribution. -/
noncomputable def translate (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : QuerySet n r) (Λ : (Fin w → F) →ₗ[F] F)
    (delta : linearResponseKernel C Q.coordinates Λ) : Tape C Λ ≃ Tape C Λ :=
  Equiv.addRight (forgetOpenings C Q.coordinates Λ (adjustment C M Q Λ delta))

theorem translate_response (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : QuerySet n r) (Λ : (Fin w → F) →ₗ[F] F)
    (delta : linearResponseKernel C Q.coordinates Λ) (masks : Tape C Λ) :
    response C M Λ (translate C M Q Λ delta masks) = response C M Λ masks + delta.1 := by
  change response C M Λ
    (masks + forgetOpenings C Q.coordinates Λ (adjustment C M Q Λ delta)) = _
  rw [response_add, adjustment_response]

theorem translate_openings (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : QuerySet n r) (Λ : (Fin w → F) →ₗ[F] F)
    (delta : linearResponseKernel C Q.coordinates Λ) (masks : Tape C Λ)
    (j : ↥Q.coordinates) :
    ((translate C M Q Λ delta masks).vCoefficient.1 (codePosition j.1) =
        masks.vCoefficient.1 (codePosition j.1)) ∧
      ((translate C M Q Λ delta masks).zRCoefficient.1 (codePosition j.1) =
        masks.zRCoefficient.1 (codePosition j.1)) := by
  change (masks.vCoefficient.1 (codePosition j.1) +
      (adjustment C M Q Λ delta).vCoefficient.1 (codePosition j.1) = _) ∧
    (masks.zRCoefficient.1 (codePosition j.1) +
      (adjustment C M Q Λ delta).zRCoefficient.1 (codePosition j.1) = _)
  rw [(adjustment C M Q Λ delta).vCoefficient.2.2 j.1 j.2,
    (adjustment C M Q Λ delta).zRCoefficient.2.2.1 j.1 j.2]
  exact ⟨add_zero _, add_zero _⟩

abbrev MaskOpenings (F : Type) {n r : ℕ} (Q : QuerySet n r) :=
  ↥Q.coordinates → F × F

def openMasks {C : MultiplicativeCode F r w n} {Λ : (Fin w → F) →ₗ[F] F}
    (Q : QuerySet n r) (masks : Tape C Λ) : MaskOpenings F Q :=
  fun j => (masks.vCoefficient.1 (codePosition j.1),
    masks.zRCoefficient.1 (codePosition j.1))

theorem openMasks_translate (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : QuerySet n r) (Λ : (Fin w → F) →ₗ[F] F)
    (delta : linearResponseKernel C Q.coordinates Λ) (masks : Tape C Λ) :
    openMasks Q (translate C M Q Λ delta masks) = openMasks Q masks := by
  funext j
  exact Prod.ext (translate_openings C M Q Λ delta masks j).1
    (translate_openings C M Q Λ delta masks j).2

/-- The difference may depend on all opened mask values. Preserving those
values makes the adaptive change of variables injective as well. -/
theorem adaptive_translate_injective (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : QuerySet n r) (Λ : (Fin w → F) →ₗ[F] F)
    (delta : MaskOpenings F Q → linearResponseKernel C Q.coordinates Λ) :
    Function.Injective (fun masks => translate C M Q Λ (delta (openMasks Q masks)) masks) := by
  intro first second heq
  have hopen : openMasks Q first = openMasks Q second := by
    simpa only [openMasks_translate] using congrArg (openMasks Q) heq
  apply (translate C M Q Λ (delta (openMasks Q first))).injective
  simpa only [hopen] using heq

noncomputable def adaptiveTranslate [Fintype F] [DecidableEq F]
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : QuerySet n r) (Λ : (Fin w → F) →ₗ[F] F)
    (delta : MaskOpenings F Q → linearResponseKernel C Q.coordinates Λ) : Tape C Λ ≃ Tape C Λ :=
  Equiv.ofBijective (fun masks => translate C M Q Λ (delta (openMasks Q masks)) masks)
    (adaptive_translate_injective C M Q Λ delta).bijective_of_finite

theorem openMasks_adaptiveTranslate [Fintype F] [DecidableEq F]
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : QuerySet n r) (Λ : (Fin w → F) →ₗ[F] F)
    (delta : MaskOpenings F Q → linearResponseKernel C Q.coordinates Λ) (masks : Tape C Λ) :
    openMasks Q (adaptiveTranslate C M Q Λ delta masks) = openMasks Q masks :=
  openMasks_translate C M Q Λ _ masks

/-- Public witness values with the target in one logical coordinate. -/
def publicValues (layout : ConstraintLayout F q w) (pivot : Fin q) (target : F) : Fin w → F :=
  fun i => if i = layout.logical pivot then target else 0

theorem publicValues_sum (layout : ConstraintLayout F q w) (pivot : Fin q) (target : F) :
    logicalSumLinearMap layout (publicValues layout pivot target) = target := by
  classical
  simp [logicalSumLinearMap, publicValues, layout.logical.injective.eq_iff]

noncomputable def correctionBase (C : MultiplicativeCode F r w n)
    (Q : QuerySet n r) (layout : ConstraintLayout F q w) (pivot : Fin q) (target : F) :
    EvaluationRow F r w n :=
  Classical.choose (exists_base_witness_query C Q.coordinates
    (QuerySet.card_coordinates Q) (publicValues layout pivot target))

theorem correctionBase_properties (C : MultiplicativeCode F r w n)
    (Q : QuerySet n r) (layout : ConstraintLayout F q w) (pivot : Fin q) (target : F) :
    correctionBase C Q layout pivot target ∈ C.base ∧
      (∀ i, correctionBase C Q layout pivot target (witnessPosition i) =
        publicValues layout pivot target i) ∧
      ∀ j ∈ Q.coordinates, correctionBase C Q layout pivot target (codePosition j) = 0 :=
  Classical.choose_spec (exists_base_witness_query C Q.coordinates
    (QuerySet.card_coordinates Q) (publicValues layout pivot target))

/-- The public correction has degree below `2k`, vanishes on the random
prefix and openings, and has the requested logical sum. -/
noncomputable def correction (C : MultiplicativeCode F r w n)
    (Q : QuerySet n r) (layout : ConstraintLayout F q w) (pivot : Fin q) (target : F) :
    EvaluationRow F r w n :=
  rowMul C.zR (correctionBase C Q layout pivot target)

theorem correction_properties (C : MultiplicativeCode F r w n)
    (Q : QuerySet n r) (layout : ConstraintLayout F q w) (pivot : Fin q) (target : F) :
    correction C Q layout pivot target ∈ C.response ∧
      (∀ i, correction C Q layout pivot target (randomPosition i) = 0) ∧
      (∀ j ∈ Q.coordinates, correction C Q layout pivot target (codePosition j) = 0) ∧
      logicalSumLinearMap layout (witnessValues (correction C Q layout pivot target)) = target := by
  obtain ⟨hbase, hwitness, hquery⟩ := correctionBase_properties C Q layout pivot target
  refine ⟨C.mul_mem C.zR_mem hbase, ?_, ?_, ?_⟩
  · intro i
    simp [correction, rowMul, C.zR_random]
  · intro j hj
    simp [correction, rowMul, hquery j hj]
  · have hw : witnessValues (correction C Q layout pivot target) =
        publicValues layout pivot target := by
      funext i
      simp [correction, witnessValues, rowMul, hwitness i]
    rw [hw, publicValues_sum]

section Arithmetic

variable {Equations : Type} [Fintype Equations] {nw nq : ℕ}

abbrev CoreRows (F : Type) (r w n nw nq : ℕ) :=
  (block : CoreBlock) → Fin (block.rowCount nw nq) → EvaluationRow F r w n

theorem linearCore_mem (C : MultiplicativeCode F r w n) (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations) (weights : Equations → F)
    (core : CoreRows F r w n nw nq) (hcore : ∀ b i, core b i ∈ C.base) :
    DirectVerifier.linearCore C layout statement weights core ∈ C.response := by
  apply Submodule.sum_mem
  intro block _
  apply Submodule.sum_mem
  intro row _
  exact C.mul_mem (C.encode_mem _ _) (hcore block row)

theorem linearCore_random (C : MultiplicativeCode F r w n) (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations) (weights : Equations → F)
    (core : CoreRows F r w n nw nq) (i : Fin r) :
    DirectVerifier.linearCore C layout statement weights core (randomPosition i) = 0 := by
  simp [DirectVerifier.linearCore, DirectVerifier.coefficientRow, rowMul, Finset.sum_apply]

theorem linearCore_sum (C : MultiplicativeCode F r w n) (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations) (weights : Equations → F)
    (core : CoreRows F r w n nw nq) :
    logicalSumLinearMap layout
      (witnessValues (DirectVerifier.linearCore C layout statement weights core)) =
        ∑ equation, weights equation *
          statement.linearValue (layoutCoreMessages layout core) equation := by
  classical
  change (∑ i : Fin q, DirectVerifier.linearCore C layout statement weights core
    (witnessPosition (layout.logical i))) = _
  simp only [DirectVerifier.linearCore,
    Finset.sum_apply, rowMul_apply, DirectVerifier.coefficientRow,
    C.encode_witness, layout.extend_logical]
  simp only [ConstraintSystem.A, ConstraintSystem.linearValue, layoutCoreMessages,
    logicalValues, logicalWitnessPosition, Finset.mul_sum, Finset.sum_mul]
  let summand : (Fin q × CoreRow nw nq) → Equations → F :=
    fun index equation => weights equation *
      statement.coefficient equation index.2.1 index.2.2 index.1 *
        core index.2.1 index.2.2 (witnessPosition (layout.logical index.1))
  calc
    _ = ∑ index : Fin q × CoreRow nw nq,
        ∑ equation : Equations, summand index equation := by
      simp [summand, Fintype.sum_prod_type, Fintype.sum_sigma, mul_assoc]
    _ = ∑ equation : Equations,
        ∑ index : Fin q × CoreRow nw nq, summand index equation := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro equation _
      simp only [summand, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      simp [Fintype.sum_sigma, mul_assoc]

theorem linearCore_sum_of_satisfies (C : MultiplicativeCode F r w n)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F) (core : CoreRows F r w n nw nq)
    (hsat : statement.Satisfies (layoutCoreMessages layout core)) :
    logicalSumLinearMap layout
      (witnessValues (DirectVerifier.linearCore C layout statement weights core)) =
        statement.combinedTarget weights := by
  rw [linearCore_sum]
  exact Finset.sum_congr rfl fun equation _ => congrArg (weights equation * ·) (hsat.1 equation)

/-- Difference between the real arithmetic core and the simulated core plus
the public target correction. No arithmetic-mask values enter this difference. -/
noncomputable def arithmeticDifference (C : MultiplicativeCode F r w n)
    (Q : QuerySet n r) (layout : ConstraintLayout F q w) (pivot : Fin q)
    (statement : ConstraintSystem F nw nq q Equations) (weights : Equations → F)
    (source target : CoreRows F r w n nw nq)
    (hsource : ∀ b i, source b i ∈ C.base) (htarget : ∀ b i, target b i ∈ C.base)
    (hsat : statement.Satisfies (layoutCoreMessages layout source))
    (hzero : ∀ equation, statement.linearValue (layoutCoreMessages layout target) equation = 0)
    (hquery : ∀ b i (j : ↥Q.coordinates),
      source b i (codePosition j.1) = target b i (codePosition j.1)) :
    linearResponseKernel C Q.coordinates (logicalSumLinearMap layout) := by
  let real := DirectVerifier.linearCore C layout statement weights source
  let simulated := DirectVerifier.linearCore C layout statement weights target
  let correctionRow := correction C Q layout pivot (statement.combinedTarget weights)
  refine ⟨real - simulated - correctionRow,
    C.response.sub_mem (C.response.sub_mem (linearCore_mem C layout statement weights source hsource)
      (linearCore_mem C layout statement weights target htarget))
      (correction_properties C Q layout pivot (statement.combinedTarget weights)).1, ?_, ?_, ?_⟩
  · intro i
    have hrandom := (correction_properties C Q layout pivot
      (statement.combinedTarget weights)).2.1
    simp [real, simulated, correctionRow, linearCore_random, hrandom i]
  · intro j hj
    have heq : real (codePosition j) = simulated (codePosition j) := by
      simp only [real, simulated, DirectVerifier.linearCore, Finset.sum_apply, rowMul_apply]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro i _
      rw [hquery b i ⟨j,hj⟩]
    have hopen := (correction_properties C Q layout pivot
      (statement.combinedTarget weights)).2.2.1
    simp only [Pi.sub_apply, heq, sub_self, correctionRow, hopen j hj]
  · change logicalSumLinearMap layout
      (witnessValues real - witnessValues simulated - witnessValues correctionRow) = 0
    have hsum := (correction_properties C Q layout pivot
      (statement.combinedTarget weights)).2.2.2
    rw [map_sub, map_sub, linearCore_sum_of_satisfies C layout statement weights source hsat,
      show logicalSumLinearMap layout (witnessValues simulated) = 0 by
        rw [linearCore_sum]
        simp [hzero], hsum]
    ring

/-- Absorbing the actual arithmetic-core difference gives exactly the real
response, with both opened mask rows unchanged by `translate_openings`. -/
theorem arithmetic_response_preserved (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : QuerySet n r) (layout : ConstraintLayout F q w) (pivot : Fin q)
    (statement : ConstraintSystem F nw nq q Equations) (weights : Equations → F)
    (source target : CoreRows F r w n nw nq)
    (hsource : ∀ b i, source b i ∈ C.base) (htarget : ∀ b i, target b i ∈ C.base)
    (hsat : statement.Satisfies (layoutCoreMessages layout source))
    (hzero : ∀ equation, statement.linearValue (layoutCoreMessages layout target) equation = 0)
    (hquery : ∀ b i (j : ↥Q.coordinates),
      source b i (codePosition j.1) = target b i (codePosition j.1))
    (masks : Tape C (logicalSumLinearMap layout)) :
    DirectVerifier.linearCore C layout statement weights target +
        response C M (logicalSumLinearMap layout)
          (translate C M Q (logicalSumLinearMap layout)
            (arithmeticDifference C Q layout pivot statement weights source target
              hsource htarget hsat hzero hquery) masks) +
        correction C Q layout pivot (statement.combinedTarget weights) =
      DirectVerifier.linearCore C layout statement weights source +
        response C M (logicalSumLinearMap layout) masks := by
  rw [translate_response]
  dsimp only [arithmeticDifference]
  abel

end Arithmetic

end LfzkV2.PolygeroMasking
