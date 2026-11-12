import LfzkV2.Current.ZeroKnowledge.FrontendPacking
import LfzkV2.Current.CellLayout
import LfzkV2.Packed.Inputs

/-! The complete binary cell vector in the runtime's physical order:
packed words; free packing masks, r and sigma(r); sumcheck pads; then the
two dedicated selection masks. This constructor supplies values at the
existing addresses. It does not introduce field-valued binary inputs.

The deterministic sigma(r) cell is derived from the same sampled r. All
later rows and fingerprints read this one vector. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.PackingCells

open DualPacking.ArtinSchreier SumcheckV2
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
variable {words degree pads : ℕ}

/-- The final partial word is padded with zero base-field coordinates.
Private binary inputs enter this constructor only as booleans. -/
def bitCoordinate {privateCount : ℕ} (bits : Fin privateCount → Bool)
    (word : Fin words) (coordinate : Fin degree) : ZMod 2 :=
  if inside : degree*word.val+coordinate.val < privateCount then
    if bits ⟨degree*word.val+coordinate.val,inside⟩ then 1 else 0
  else 0

def packedWords {privateCount : ℕ} (basis : Module.Basis (Fin degree) (ZMod 2) F)
    (bits : Fin privateCount → Bool) (word : Fin words) : F :=
  ∑ coordinate, basis coordinate * algebraMap (ZMod 2) F (bitCoordinate bits word coordinate)

theorem private_coordinate {privateCount : ℕ} (positive : 0 < degree)
    (capacity : privateCount ≤ words*degree) (bits : Fin privateCount → Bool) (i : Fin privateCount) :
    bitCoordinate bits (CellLayout.primary positive capacity i).1
      (CellLayout.primary positive capacity i).2 = if bits i then 1 else 0 := by
  have position : degree*(i.val/degree)+i.val%degree = i.val := by
    have decomposition := Nat.mod_add_div i.val degree
    omega
  unfold bitCoordinate
  change (if inside : degree*(i.val/degree)+i.val%degree < privateCount then
    if bits ⟨degree*(i.val/degree)+i.val%degree,inside⟩ then 1 else 0 else 0) = _
  simp only [position,dif_pos i.isLt]

omit [Fintype F] in
theorem packedWords_digit {privateCount : ℕ} (positive : 0 < degree)
    (capacity : privateCount ≤ words*degree) (basis : Module.Basis (Fin degree) (ZMod 2) F)
    (bits : Fin privateCount → Bool) (i : Fin privateCount) :
    DualPacking.digit basis (packedWords basis bits (CellLayout.primary positive capacity i).1)
      (CellLayout.primary positive capacity i).2 = if bits i then 1 else 0 := by
  rw [packedWords,DualPacking.digit_pack,private_coordinate positive capacity]
  cases bits i <;> simp

omit [Fintype F] in
theorem packedWords_zero_tail {privateCount : ℕ}
    (basis : Module.Basis (Fin degree) (ZMod 2) F) (bits : Fin privateCount → Bool)
    (word : Fin words) (coordinate : Fin degree)
    (outside : privateCount ≤ degree*word.val+coordinate.val) :
    DualPacking.digit basis (packedWords basis bits word) coordinate = 0 := by
  rw [packedWords,DualPacking.digit_pack]
  simp only [bitCoordinate,dif_neg (Nat.not_lt.mpr outside),map_zero]

def auxiliary (positive : 0 < degree) (masks : Fin (degree-1) → F) (random : F) :
    Fin (degree+1) → F :=
  fun i => Fin.append masks (fun j : Fin 2 => if j = 0 then random else frobenius (ZMod 2) F random)
    (Fin.cast (show degree+1 = (degree-1)+2 by omega) i)

def values (positive : 0 < degree) (packed : Fin words → F)
    (masks : Fin (degree-1) → F) (random : F) (sumcheck : Fin pads → F)
    (selection : Fin 2 → F) : Fin (CellLayout.Binary.cells words degree pads+2) → F :=
  Fin.append (Fin.append (Fin.append packed (auxiliary positive masks random)) sumcheck) selection

theorem word_value (positive : 0 < degree) (packed : Fin words → F)
    (masks : Fin (degree-1) → F) (random : F) (sumcheck : Fin pads → F)
    (selection : Fin 2 → F) (i : Fin words) :
    values positive packed masks random sumcheck selection (CellLayout.Binary.word words degree pads i) =
      packed i := by
  change Fin.append _ _ (Fin.castAdd 2 (Fin.castAdd pads (Fin.castAdd (degree+1) i))) = _
  rw [Fin.append_left,Fin.append_left,Fin.append_left]

theorem mask_value (positive : 0 < degree) (packed : Fin words → F)
    (masks : Fin (degree-1) → F) (random : F) (sumcheck : Fin pads → F)
    (selection : Fin 2 → F) (i : Fin (degree-1)) :
    values positive packed masks random sumcheck selection (CellLayout.Binary.mask words degree pads i) =
      masks i := by
  let j : Fin (degree+1) := ⟨i.val,by have := i.isLt; omega⟩
  change Fin.append _ _ (Fin.castAdd 2 (Fin.castAdd pads (Fin.natAdd words j))) = _
  rw [Fin.append_left,Fin.append_left,Fin.append_right]
  change Fin.append masks _ (Fin.castAdd 2 i) = _
  exact Fin.append_left _ _ i

theorem random_value (positive : 0 < degree) (packed : Fin words → F)
    (masks : Fin (degree-1) → F) (random : F) (sumcheck : Fin pads → F)
    (selection : Fin 2 → F) :
    values positive packed masks random sumcheck selection (CellLayout.Binary.random words degree pads) =
      random := by
  let j : Fin (degree+1) := ⟨degree-1,by omega⟩
  change Fin.append _ _ (Fin.castAdd 2 (Fin.castAdd pads (Fin.natAdd words j))) = _
  rw [Fin.append_left,Fin.append_left,Fin.append_right]
  change Fin.append masks _ (Fin.natAdd (degree-1) (0 : Fin 2)) = _
  rw [Fin.append_right]
  exact if_pos rfl

theorem frobenius_value (positive : 0 < degree) (packed : Fin words → F)
    (masks : Fin (degree-1) → F) (random : F) (sumcheck : Fin pads → F)
    (selection : Fin 2 → F) :
    values positive packed masks random sumcheck selection (CellLayout.Binary.frobenius words degree pads) =
      frobenius (ZMod 2) F random := by
  let j : Fin (degree+1) := ⟨degree,by omega⟩
  change Fin.append _ _ (Fin.castAdd 2 (Fin.castAdd pads (Fin.natAdd words j))) = _
  rw [Fin.append_left,Fin.append_left,Fin.append_right]
  have index : Fin.cast (show degree+1 = (degree-1)+2 by omega) j =
      Fin.natAdd (degree-1) (1 : Fin 2) := by
    apply Fin.ext
    change degree = (degree-1)+1
    omega
  unfold auxiliary
  rw [index,Fin.append_right]
  exact if_neg (by decide)

theorem pad_value (positive : 0 < degree) (packed : Fin words → F)
    (masks : Fin (degree-1) → F) (random : F) (sumcheck : Fin pads → F)
    (selection : Fin 2 → F) (i : Fin pads) :
    values positive packed masks random sumcheck selection (CellLayout.Binary.pad words degree pads i) =
      sumcheck i := by
  change Fin.append _ _ (Fin.castAdd 2 (Fin.natAdd (words+(degree+1)) i)) = _
  rw [Fin.append_left,Fin.append_right]

theorem selection_value (positive : 0 < degree) (packed : Fin words → F)
    (masks : Fin (degree-1) → F) (random : F) (sumcheck : Fin pads → F)
    (selection : Fin 2 → F) (i : Fin 2) :
    values positive packed masks random sumcheck selection
      (CellLayout.selected (CellLayout.Binary.cells words degree pads) (.inr i)) = selection i :=
  Fin.append_right _ _ i

theorem unpack_values {privateCount : ℕ} (positive : 0 < degree)
    (capacity : privateCount ≤ words*degree) (basis : Module.Basis (Fin degree) (ZMod 2) F)
    (bits : Fin privateCount → Bool) (masks : Fin (degree-1) → F) (random : F)
    (sumcheck : Fin pads → F) (selection : Fin 2 → F) (i : Fin privateCount) :
    Packed.unpack basis (CellLayout.Binary.word words degree pads) (CellLayout.primary positive capacity)
      (values positive (packedWords basis bits) masks random sumcheck selection) i =
      if bits i then 1 else 0 := by
  rw [Packed.unpack,word_value]
  exact packedWords_digit positive capacity basis bits i

/-- Free masks use the existing t_1,...,t_(m-1) order, excluding pivot zero. -/
def freeMask (positive : 0 < degree) (masks : Fin (degree-1) → F)
    (i : {i : Fin degree // i ≠ ⟨0,positive⟩}) : F :=
  masks ⟨i.val.val-1,by
    have bounded := i.val.isLt
    have nonzero : i.val.val ≠ 0 := by intro equal; exact i.property (Fin.ext equal)
    omega⟩

/-- The physical order of free masks is just the nonzero basis indices
minus one. This bijection preserves their independent uniform sampling. -/
def freeIndex (positive : 0 < degree) :
    {i : Fin degree // i ≠ ⟨0,positive⟩} ≃ Fin (degree-1) where
  toFun i := ⟨i.val.val-1,by
    have := i.val.isLt
    have nonzero : i.val.val ≠ 0 := by intro equal; exact i.property (Fin.ext equal)
    omega⟩
  invFun j := ⟨⟨j.val+1,by have := j.isLt; omega⟩,by
    intro equal
    have value := congrArg Fin.val equal
    change j.val+1 = 0 at value
    omega⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have nonzero : i.val.val ≠ 0 := by intro equal; exact i.property (Fin.ext equal)
    change i.val.val-1+1 = i.val.val
    omega
  right_inv j := by apply Fin.ext; exact Nat.add_sub_cancel _ _

def freeMaskEquiv (positive : 0 < degree) :
    (Fin (degree-1) → F) ≃ ({i : Fin degree // i ≠ ⟨0,positive⟩} → F) :=
  Equiv.arrowCongr (freeIndex positive).symm (Equiv.refl F)

omit [Field F] [Fintype F] [Algebra (ZMod 2) F] in
theorem freeMaskEquiv_apply (positive : 0 < degree) (masks : Fin (degree-1) → F) :
    freeMaskEquiv positive masks = freeMask positive masks := rfl

theorem packing_realize (nontrivial : 1 < degree)
    (basis : Module.Basis (Fin degree) (ZMod 2) F)
    (coefficients : Fin words → Fin degree → F)
    (target : LinearRow (Fin (CellLayout.Binary.cells words degree pads+2)) F)
    (packed : Fin words → F) (masks : Fin (degree-1) → F) (random : F)
    (sumcheck : Fin pads → F) (selection : Fin 2 → F) :
    let read := values (by omega : 0 < degree) packed masks random sumcheck selection
    (CellLayout.Binary.packing nontrivial basis coefficients target).realize read =
      { basis := basis, pivot := ⟨0,by omega⟩,words := packed,coefficients := coefficients
        target := target.eval read,masks := freeMask (by omega) masks,r := random
        b := frobenius (ZMod 2) F random } := by
  simp only [Packed.Statement.realize,CellLayout.Binary.packing,Function.comp_def,
    word_value,mask_value,random_value,frobenius_value]
  rfl

section Source
variable {publicCount privateCount : ℕ}
variable (nontrivial : 1 < degree) (capacity : privateCount ≤ words*degree)
variable (basis : Module.Basis (Fin degree) (ZMod 2) F)
variable (claim : PadExpression (Fin pads) F)
variable (publicWeights publicInputs : Fin publicCount → F)
variable (privateWeights : Fin privateCount → F)

/-- The symbolic sumcheck input equation is compiled on its original pad
addresses. Its target is independent of the packing and selection masks. -/
def source : Packed.Statement (ZMod 2) F (Fin degree) (Fin words)
    (Fin (CellLayout.Binary.cells words degree pads+2)) :=
  (CellLayout.Binary.packing nontrivial basis 0 ⟨0,[]⟩).withSource
    (CellLayout.primary (by omega : 0 < degree) capacity) claim (CellLayout.Binary.pad words degree pads)
    publicWeights publicInputs privateWeights

variable (bits : Fin privateCount → Bool) (masks : Fin (degree-1) → F)
variable (random : F) (sumcheck : Fin pads → F) (selection : Fin 2 → F)

local notation "read" => values (by omega : 0 < degree) (packedWords basis bits) masks random sumcheck selection
local notation "statement" => source nontrivial capacity basis claim publicWeights publicInputs privateWeights

theorem source_target :
    ((statement).realize read).target = claim.eval sumcheck-SumcheckV2.dot publicWeights publicInputs := by
  rw [source,Packed.Statement.source_target]
  congr 1
  apply congrArg claim.eval
  funext i
  exact pad_value _ _ _ _ _ _ i

theorem source_trueValue :
    ((statement).realize read).trueValue =
      SumcheckV2.dot privateWeights (fun i => if bits i then 1 else 0) := by
  rw [source,Packed.Statement.source_trueValue]
  apply congrArg (SumcheckV2.dot privateWeights)
  funext i
  exact unpack_values _ capacity basis bits masks random sumcheck selection i

theorem source_valid
    (holds : claim.eval sumcheck = SumcheckV2.dot publicWeights publicInputs +
      SumcheckV2.dot privateWeights (fun i => if bits i then 1 else 0)) :
    ((statement).realize read).target = ((statement).realize read).trueValue := by
  rw [source_target,source_trueValue,holds]
  exact add_sub_cancel_left _ _

/-- All instance coordinates, including the affine source target, are
computed from the same flat vector. The target does not depend on its newly
sampled packing or fingerprint masks. -/
theorem source_realize :
    (statement).realize read =
      { basis := basis, pivot := ⟨0,by omega⟩,words := packedWords basis bits
        coefficients := Packed.sourceCoefficients (CellLayout.primary (by omega : 0 < degree) capacity)
          privateWeights
        target := claim.eval sumcheck-SumcheckV2.dot publicWeights publicInputs
        masks := freeMask (by omega) masks,r := random,b := frobenius (ZMod 2) F random } := by
  change (CellLayout.Binary.packing nontrivial basis
    (Packed.sourceCoefficients (CellLayout.primary (by omega : 0 < degree) capacity) privateWeights)
    ⟨claim.constant-SumcheckV2.dot publicWeights publicInputs,
      mapTerms claim.terms (CellLayout.Binary.pad words degree pads)⟩).realize read = _
  rw [packing_realize]
  congr 1
  exact source_target nontrivial capacity basis claim publicWeights publicInputs privateWeights
    bits masks random sumcheck selection

/-- Changing packing coins preserves the source equation and all ordinary
words/pads. The second scalar cell is recomputed from the changed r. -/
theorem source_change_masks
    (otherMasks : Fin (degree-1) → F) (otherRandom : F) (otherSelection : Fin 2 → F) :
    (statement).realize
        (values (by omega : 0 < degree) (packedWords basis bits) otherMasks otherRandom sumcheck otherSelection) =
      Packing.honest ((statement).realize read) (freeMask (by omega) otherMasks,otherRandom) := by
  rw [source_realize]
  unfold Packing.honest
  have words_eq : ((statement).realize read).words = packedWords basis bits := by
    funext i
    exact word_value _ _ _ _ _ _ i
  have target_eq := source_target nontrivial capacity basis claim publicWeights publicInputs privateWeights
    bits masks random sumcheck selection
  simp only [words_eq,target_eq]
  rfl

/-- Public packing messages satisfy the actual source rows at the recovered
flat cells. The simulator itself uses only the forward sampler; recovered
words and masks belong to the distribution coupling. -/
theorem simulated_source_rows (pivotOne : basis ⟨0,by omega⟩ = 1)
    (holds : claim.eval sumcheck = SumcheckV2.dot publicWeights publicInputs +
      SumcheckV2.dot privateWeights (fun i => if bits i then 1 else 0))
    (delta : (Fin degree → Masking.TraceZero (ZMod 2) F) → Fin degree → F)
    (coins : Packing.Tape (F := F) (⟨0,by omega⟩ : Fin degree)) :
    let baseInstance := (statement).realize read
    let valid := source_valid nontrivial capacity basis claim publicWeights publicInputs privateWeights
      bits masks random sumcheck selection holds
    let recovered := (Packing.coupling baseInstance pivotOne valid delta).symm coins
    let recoveredRead : Fin (CellLayout.Binary.cells words degree pads+2) → F :=
      values (by omega : 0 < degree) (packedWords basis bits)
      ((freeMaskEquiv (by omega)).symm recovered.1) recovered.2 sumcheck selection
    let view := Packing.simulate basis ⟨0,by omega⟩ coins
    RowsHold ((statement).rows (fun i => (view.1 i).val) (delta view.1) view.2) recoveredRead := by
  dsimp only
  let baseInstance := (statement).realize read
  have valid := source_valid nontrivial capacity basis claim publicWeights publicInputs privateWeights
    bits masks random sumcheck selection holds
  let recovered := (Packing.coupling baseInstance pivotOne valid delta).symm coins
  let recoveredRead : Fin (CellLayout.Binary.cells words degree pads+2) → F :=
    values (by omega : 0 < degree) (packedWords basis bits)
    ((freeMaskEquiv (by omega)).symm recovered.1) recovered.2 sumcheck selection
  let view := Packing.simulate basis ⟨0,by omega⟩ coins
  have same : (statement).realize recoveredRead = Packing.honest baseInstance recovered := by
    rw [source_change_masks nontrivial capacity basis claim publicWeights publicInputs privateWeights
      bits masks random sumcheck selection]
    apply congrArg (Packing.honest baseInstance)
    apply Prod.ext
    · exact (freeMaskEquiv (by omega : 0 < degree)).apply_symm_apply recovered.1
    · rfl
  have native : ((statement).realize recoveredRead).nativeLinearVerify
      (fun i => (view.1 i).val) (delta view.1) view.2 := by
    rw [same]
    exact Packing.recovered_constraints baseInstance pivotOne valid delta coins
  exact ((statement).rows_iff_native recoveredRead _ _ _ native.1).mpr native

/-- Honest values satisfy the exact two affine rows authenticated later.
This uses the final sumcheck input equation, not a packing-acceptance premise. -/
theorem source_rows
    (holds : claim.eval sumcheck = SumcheckV2.dot publicWeights publicInputs +
      SumcheckV2.dot privateWeights (fun i => if bits i then 1 else 0)) (delta : Fin degree → F) :
    let inst := (statement).realize read
    (∀ i, traceF (ZMod 2) (inst.honestU i) = 0) ∧
      RowsHold ((statement).rows inst.honestU delta (inst.honestA delta)) read := by
  have valid := source_valid nontrivial capacity basis claim publicWeights publicInputs privateWeights
    bits masks random sumcheck selection holds
  have honestMask : frobenius (ZMod 2) F ((statement).realize read).r = ((statement).realize read).b := by
    change frobenius (ZMod 2) F (read (CellLayout.Binary.random words degree pads)) =
      read (CellLayout.Binary.frobenius words degree pads)
    rw [random_value,frobenius_value]
  have native := ((statement).realize read).native_linear_completeness valid honestMask delta
  exact ⟨native.1,((statement).rows_iff_native read _ _ _ native.1).mpr native⟩

end Source

end LfzkV2.Current.ZeroKnowledge.Frontend.PackingCells
