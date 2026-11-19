import LfzkV2.Current.ZeroKnowledge.FrontendCompleteSimulation

/-! The prime participant's honest complete cell vector. Shared inputs have
no committed prime slot; the only scalar outside the original private input
suffix and sumcheck pads is R. The final two cells are dedicated selector
masks. This constructor uses the exact existing physical index equivalence. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CompletePrimeCells
open SumcheckV2 ApplicationSetup
open scoped Classical
variable {F : Type} {remaining pads shared : ℕ}

def values (privateInputs : Fin remaining → F) (mask : F) (sumcheckPads : Fin pads → F)
    (selectorMasks : Fin 2 → F) : CellLayout.Prime.Slot remaining pads → F :=
  Sum.elim (Sum.elim privateInputs (Sum.elim sumcheckPads selectorMasks)) (fun _ => mask)

def flat (privateInputs : Fin remaining → F) (mask : F) (sumcheckPads : Fin pads → F)
    (selectorMasks : Fin 2 → F) : Fin (CellLayout.Prime.cells remaining pads+2) → F :=
  values privateInputs mask sumcheckPads selectorMasks ∘ (CellLayout.Prime.index remaining pads).symm

theorem flat_read (privateInputs : Fin remaining → F) (mask : F) (sumcheckPads : Fin pads → F)
    (selectorMasks : Fin 2 → F) (slot : CellLayout.Prime.Slot remaining pads) :
    flat privateInputs mask sumcheckPads selectorMasks (CellLayout.Prime.index remaining pads slot) =
      values privateInputs mask sumcheckPads selectorMasks slot := by
  simp only [flat,Function.comp_apply,Equiv.symm_apply_apply]

@[simp] theorem flat_private (privateInputs : Fin remaining → F) (mask : F)
    (sumcheckPads : Fin pads → F) (selectorMasks : Fin 2 → F) (i : Fin remaining) :
    flat privateInputs mask sumcheckPads selectorMasks
      (CellLayout.Prime.index remaining pads (.inl (.inl i))) = privateInputs i := by rw [flat_read]; rfl

@[simp] theorem flat_mask (privateInputs : Fin remaining → F) (mask : F)
    (sumcheckPads : Fin pads → F) (selectorMasks : Fin 2 → F) :
    flat privateInputs mask sumcheckPads selectorMasks
      (CellLayout.Prime.index remaining pads (.inr ())) = mask := by rw [flat_read]; rfl

@[simp] theorem flat_pad (privateInputs : Fin remaining → F) (mask : F)
    (sumcheckPads : Fin pads → F) (selectorMasks : Fin 2 → F) (i : Fin pads) :
    flat privateInputs mask sumcheckPads selectorMasks
      (CellLayout.Prime.index remaining pads (.inl (CellLayout.Prime.pad remaining pads i))) =
        sumcheckPads i := by rw [flat_read]; rfl

@[simp] theorem flat_selector (privateInputs : Fin remaining → F) (mask : F)
    (sumcheckPads : Fin pads → F) (selectorMasks : Fin 2 → F) (i : Fin 2) :
    flat privateInputs mask sumcheckPads selectorMasks
      (CellLayout.Prime.index remaining pads (.inl (CellLayout.Prime.fingerprint remaining pads i))) =
        selectorMasks i := by rw [flat_read]; rfl

theorem flat_selection (privateInputs : Fin remaining → F) (mask : F)
    (sumcheckPads : Fin pads → F) (selectorMasks : Fin 2 → F) (i : Fin 2) :
    flat privateInputs mask sumcheckPads selectorMasks
      (CellLayout.selected (CellLayout.Prime.cells remaining pads) (.inr i)) = selectorMasks i := by
  have hindex : CellLayout.selected (CellLayout.Prime.cells remaining pads) (.inr i) =
      CellLayout.Prime.index remaining pads (.inl (CellLayout.Prime.fingerprint remaining pads i)) := by
    apply Fin.ext
    simp [CellLayout.Prime.fingerprint]
  exact (congrArg (flat privateInputs mask sumcheckPads selectorMasks) hindex).trans
    (flat_selector privateInputs mask sumcheckPads selectorMasks i)

theorem flat_original (privateInputs : Fin remaining → F) (mask : F)
    (sumcheckPads : Fin pads → F) (first second : Fin 2 → F)
    (i : Fin (CellLayout.Prime.cells remaining pads)) :
    flat privateInputs mask sumcheckPads first (CellLayout.selected _ (.inl i)) =
      flat privateInputs mask sumcheckPads second (CellLayout.selected _ (.inl i)) := by
  let slot := (CellLayout.Prime.index remaining pads).symm (CellLayout.selected _ (.inl i))
  have hi : (CellLayout.Prime.index remaining pads slot).val < CellLayout.Prime.cells remaining pads := by
    rw [Equiv.apply_symm_apply]
    exact i.isLt
  change values privateInputs mask sumcheckPads first slot = values privateInputs mask sumcheckPads second slot
  rcases slot with (j | (j | j)) | ⟨⟩
  · rfl
  · rfl
  · have hj := CellLayout.Prime.index_fingerprint remaining pads j
    rw [hj] at hi
    omega
  · rfl

/-- The ordinary prime input vector ignores R, every sumcheck pad and both
fingerprint masks. Thus the later adapter can recover R after prime replay. -/
theorem private_input_values (privateInputs : Fin remaining → F) (mask : F)
    (sumcheckPads : Fin pads → F) (selectorMasks : Fin 2 → F) (sharedValues : Fin shared → F)
    (i : Fin (shared+remaining)) :
    Sum.elim sharedValues (fun other => values privateInputs mask sumcheckPads selectorMasks (.inl other))
      (CellLayout.Prime.input shared remaining pads i) =
        Fin.addCases sharedValues privateInputs i := by
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j <;> simp [CellLayout.Prime.input,values]

end LfzkV2.Current.ZeroKnowledge.Frontend.CompletePrimeCells
