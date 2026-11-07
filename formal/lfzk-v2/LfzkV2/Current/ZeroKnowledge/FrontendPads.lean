import LfzkV2.Current.ZeroKnowledge.FrontendCircuit
import LfzkV2.Current.CellLayout

/-! The simulator coupling uses exactly the current committed pad suffix:
two cells for each round, then A,B,AB,D, then the next layer.  AB is derived
from the independently sampled A and B cells; it is not an additional random
coin and does not introduce a backend multiplication equation. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend
open SumcheckV2
open scoped Classical
variable {F Pad : Type} [Field F]

def layerIndex (n : ℕ) : LayerPad n ≃ Fin (2*n+4) :=
  (Equiv.sumCongr (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)))
    (Equiv.refl (Fin 4))).trans finSumFinEquiv

@[simp] theorem layerIndex_round (n : ℕ) (i : Fin n) (j : Fin 2) :
    (layerIndex n (.inl (i,j))).val = 2*i.val+j.val := by
  simp [layerIndex,finProdFinEquiv,finSumFinEquiv,Nat.add_comm]

@[simp] theorem layerIndex_terminal (n : ℕ) (j : Fin 4) :
    (layerIndex n (.inr j)).val = 2*n+j.val := by
  simp [layerIndex,finSumFinEquiv]

def layerAddress {n : ℕ} (ids : Layered.Replay.LayerPads Pad n) : LayerPad n → Pad
  | .inl (i,j) => if j = 0 then (ids.round i).1 else (ids.round i).2
  | .inr j => ![ids.a,ids.b,ids.ab,ids.d] j

def layerPhysicalValues {n : ℕ} (tape : LayerTape F n) (i : Fin (2*n+4)) : F :=
  padValues tape ((layerIndex n).symm i)

@[simp] theorem layerPhysicalValues_index {n : ℕ} (tape : LayerTape F n) (j : LayerPad n) :
    layerPhysicalValues tape (layerIndex n j) = padValues tape j := by
  simp [layerPhysicalValues]

def circuitPadValues : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    CircuitTape circuit → Fin (CellLayout.Pads.count circuit) → F
  | _, _, .input, _, i => Fin.elim0 i
  | _, _, .entry _ _ rest, tape, i => circuitPadValues rest tape i
  | _, _, .layer _ _ rest, tape, i =>
      Fin.addCases (layerPhysicalValues tape.1) (circuitPadValues rest tape.2) i

def Assignment : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    Layered.Replay.PadPlan (Pad := Pad) circuit → CircuitTape circuit → (Pad → F) → Prop
  | _, _, .input, _, _, _ => True
  | _, _, .entry _ _ rest, ids, tape, pads => Assignment rest ids tape pads
  | _, _, .layer _ _ rest, ids, tape, pads =>
      (∀ i, pads (layerAddress ids.1 i) = padValues tape.1 i) ∧
        Assignment rest ids.2 tape.2 pads

omit [Field F] in
theorem allocated_head {out n input assertions : ℕ}
    (body : Native.CircuitLayer (Cube out) (Cube n) (Fin assertions) F)
    (rest : Layered.Circuit F n input)
    (address : Fin (CellLayout.Pads.count (.layer assertions body rest)) → Pad) (j : LayerPad n) :
    layerAddress (CellLayout.Pads.plan (.layer assertions body rest) address).1 j =
      address (Fin.castAdd (CellLayout.Pads.count rest) (layerIndex n j)) := by
  rcases j with ⟨i,j⟩ | j
  · fin_cases j <;> norm_num [layerAddress,CellLayout.Pads.plan]
    all_goals
      apply congrArg address
      apply Fin.ext
      simp
  · fin_cases j <;> dsimp only [layerAddress,CellLayout.Pads.plan]
    all_goals
      apply congrArg address
      apply Fin.ext
      simp

theorem assignment_of_values {out input : ℕ} (circuit : Layered.Circuit F out input)
    (address : Fin (CellLayout.Pads.count circuit) → Pad) (tape : CircuitTape circuit)
    (pads : Pad → F) (hvalues : ∀ i, pads (address i) = circuitPadValues circuit tape i) :
    Assignment circuit (CellLayout.Pads.plan circuit address) tape pads := by
  induction circuit with
  | input => trivial
  | entry _ _ _ ih => exact ih address tape hvalues
  | @layer out mid input assertions body rest ih =>
      constructor
      · intro j
        rw [allocated_head, hvalues]
        simp only [circuitPadValues,Fin.addCases_left,layerPhysicalValues_index]
      · apply ih (fun i => address ⟨2*mid+4+i.val,by
          have := i.isLt; dsimp [CellLayout.Pads.count]; omega⟩) tape.2
        intro i
        rw [hvalues]
        exact @Fin.addCases_right (2*mid+4) (CellLayout.Pads.count rest) (fun _ => F)
          (layerPhysicalValues tape.1) (circuitPadValues rest tape.2) i

theorem circuitPadValues_assignment {out input : ℕ} (circuit : Layered.Circuit F out input)
    (tape : CircuitTape circuit) :
    Assignment circuit (CellLayout.Pads.plan circuit id) tape (circuitPadValues circuit tape) :=
  assignment_of_values circuit id tape _ (fun _ => rfl)

end LfzkV2.Current.ZeroKnowledge.Frontend
