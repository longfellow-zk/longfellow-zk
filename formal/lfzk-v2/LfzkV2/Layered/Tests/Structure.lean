import LfzkV2.Layered.Fragments
import LfzkV2.Layered.SparseLayer
import LfzkV2.Layered.Prover
import LfzkV2.Layered.Sizes

/-! Structural cases for scalar outputs, coincident shared inputs, no-entry
steps, and non-power-of-two sparse offsets. No standalone wire fragments or
per-circuit terminal factors are introduced. -/

namespace LfzkV2.Layered.Tests

open SumcheckV2

private def scalarEntry : Entry (Cube 0) (Cube 0) 1 where
  carry _ := none
  fresh _ := ()

private def sharedEntry : Entry (Cube 0) (Cube 0) 1 where
  carry x := some x
  fresh _ := ()

private def scalarCircuit (F : Type) : Layered.Circuit F 0 0 :=
  .entry 1 scalarEntry .input

example (F : Type) : (scalarCircuit F).layers = 0 := rfl
example (F : Type) : (scalarCircuit F).ordinaryBudget = 1 := rfl
example (F : Type) : Replay.slots (scalarCircuit F) = 1 := rfl

example {F : Type} [Field F] (w : Cube 0 → F) :
    (scalarCircuit F).Satisfies w ↔ w () = 0 := by
  simp [scalarCircuit, Circuit.Satisfies, Circuit.eval, Entry.residuals, scalarEntry]

example {F : Type} [Field F] (a : Cube 0 → F) (rho : Fin 1 → F) :
    sharedEntry.weights a rho () = a () + rho 0 := by
  simp [Entry.weights, sharedEntry, Cube]

example {F : Type} [Field F] (rho sigma : F) :
    Circuit.inputWeights (Pad := Unit) (.entry 1 sharedEntry (.entry 1 sharedEntry (.input : Layered.Circuit F 0 0)))
      ((fun _ => rho), (fun _ => sigma), ()) 0 () = rho + sigma := by
  simp [Circuit.inputWeights, Entry.weights, sharedEntry, Cube]

example {F : Type} [Field F] (rho sigma : F) :
    Circuit.proof (Pad := Unit) (.entry 1 sharedEntry (.entry 1 sharedEntry (.input : Layered.Circuit F 0 0)))
      ((fun _ => rho), (fun _ => sigma), ()) 0 = [] := rfl

private def zeroLayer (F : Type) [Field F] :
    Native.CircuitLayer (Cube 0) (Cube 0) (Fin 0) F :=
  ⟨fun _ _ _ => 0, fun _ _ => 0, fun _ => 0, Fin.elim0⟩

private def mixedDepth (F : Type) [Field F] : Layered.Circuit F 0 0 :=
  .entry 1 scalarEntry (.layer 0 (zeroLayer F) (.entry 1 sharedEntry .input))

example {F : Type} [Field F] : (mixedDepth F).layers = 1 := rfl
example {F : Type} [Field F] : (mixedDepth F).ordinaryBudget = 3 := rfl
example {F : Type} [Field F] : Replay.slots (mixedDepth F) = 4 := rfl

/-- A zero-layer circuit still constrains the shared input after the other
circuit's layer has finished. Its scalar output receives a challenge. -/
example {F : Type} [Field F] (w : Cube 0 → F) :
    (mixedDepth F).Satisfies w ↔ w () = 0 := by
  simp [mixedDepth, Circuit.Satisfies, Circuit.eval, Native.CircuitLayer.outputs,
    LfzkV2.quadratic, dot, zeroLayer, Entry.residuals, scalarEntry, sharedEntry]

private def range3 : Fin 3 → Fin 11 := fun i => ⟨i.val, by omega⟩
private def range5 : Fin 5 → Fin 11 := fun i => ⟨3+i.val, by omega⟩
private def last3 : Fin 3 → Fin 11 := fun i => ⟨8+i.val, by omega⟩

example : range3 2 = 2 ∧ range5 0 = 3 ∧ range5 4 = 7 ∧ last3 0 = 8 ∧ last3 2 = 10 := by decide

example {F : Type} [Field F] (fragments : List (QuadFragment (Fin 2) (Fin 11) F))
    (a : Fin 2 → F) (m : Fin 11 → F) (alpha : F) (r : Fin 11) :
    m r + alpha*((flatten fragments).map (Term.right a m r)).sum =
      m r + alpha*(fragments.map fun fragment =>
        (fragment.globalTerms.map (Term.right a m r)).sum).sum :=
  transition_flatten fragments a m alpha r

end LfzkV2.Layered.Tests
