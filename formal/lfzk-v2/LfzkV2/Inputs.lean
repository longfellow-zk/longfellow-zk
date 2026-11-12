import LfzkV2.InputBinding
import LfzkV2.Program

/-! Public/private input binding, including zero padding to a coefficient cube. -/

namespace LfzkV2

open SumcheckV2 Classical

variable {F ι κ : Type} [Field F] [Fintype ι] [Fintype κ]

/-- The circuit-level reduction for the actual rows emitted by the V2 compiler. -/
theorem compiled_circuit_reduction {out input nPublic nPrivate : ℕ} {Pad Slot : Type}
    (circuit : Circuit F out input) (m : circuit.Messages Pad Slot) (point : Fin out → F)
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot) (witness : Slot → F) (cs : Constraints Pad Slot F)
    (hbuild : buildConstraints (circuit.proof m) = some cs)
    (hproducts : ProductsHold cs coordinate witness)
    (hrows : RowsHold (compile cs coordinate privateCoordinate
      (fun i => circuit.inputWeights m (monomialWeights point) (index (.inl i))) publicInputs
      (fun i => circuit.inputWeights m (monomialWeights point) (index (.inr i)))) witness)
    (hfalse : ¬ circuit.Satisfies (circuitInputs index publicInputs privateCoordinate witness)) :
    OutputBad (circuit.eval (circuitInputs index publicInputs privateCoordinate witness)) point ∨
      AssertedBad (witness ∘ coordinate) 0
        (circuit.execution m (circuitInputs index publicInputs privateCoordinate witness)
          (monomialWeights point)) := by
  apply circuit.soundness_reduction m _ point (witness ∘ coordinate) hfalse
  rw [input_sum]
  exact (compiled_iff_clear (circuit.proof m) cs hbuild coordinate privateCoordinate
    _ publicInputs _ witness hproducts).mp hrows

end LfzkV2
