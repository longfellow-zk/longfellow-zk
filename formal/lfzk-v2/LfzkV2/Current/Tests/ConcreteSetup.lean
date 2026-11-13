import LfzkV2.Current.ConcreteSetup

/-! Public layout and topology checks for the current mdoc specialization. -/
noncomputable section
namespace LfzkV2.Current.Tests.ConcreteSetup
open SumcheckV2

example : ConcreteSetup.rows 263 = 1 := by decide
example : ConcreteSetup.rows 264 = 2 := by decide
example : ConcreteSetup.rows 0 = 1 := by decide

example (cells : ℕ) : cells+2 ≤ ConcreteSetup.rows cells*265 :=
  ConcreteSetup.rows_capacity cells

example (i : Fin 265) :
    (ConcreteSetup.positionIndex (LigeroFamily.witnessPosition i)).val = 84+i.val := rfl

example (i : Fin 2443) :
    (ConcreteSetup.positionIndex (LigeroFamily.codePosition i)).val = 349+i.val := rfl

example : (ConcreteSetup.primeNodes ⟨2791,by decide⟩).val = 2791 := by
  exact ZMod.val_natCast_of_lt (by decide)

example : (ConcreteSetup.cubeIndex 2 (true,false,())).val = 1 := rfl
example : (ConcreteSetup.cubeIndex 2 (false,true,())).val = 2 := rfl

-- The shared values lead the hash witness: signature value i is hash private bit i.
example {B : Type} [Field B] [Algebra (ZMod 2) B] (circuit : ConcreteSetup.BinaryCircuit B) :
    (circuit.sharedPrivate ⟨256,by decide⟩).val = 256 := rfl
example {B : Type} [Field B] [Algebra (ZMod 2) B] (circuit : ConcreteSetup.BinaryCircuit B) :
    (circuit.sharedPrivate ⟨767,by decide⟩).val = 767 := rfl

-- Physical commitment order: frontend values in value order, then the storage
-- reduction's auxiliary cells, then the two selection masks. Packed binary:
-- words, sumcheck pads, packing masks t_1..t_(m-1), r, b. Split prime:
-- remaining inputs, pads, R.
example : (CellLayout.Binary.pad 3 4 5 0).val = 3 := rfl
example : (CellLayout.Binary.mask 3 4 5 0).val = 8 := rfl
example : (CellLayout.Binary.random 3 4 5).val = 11 := rfl
example : (CellLayout.Binary.frobenius 3 4 5).val = 12 := rfl
example : (CellLayout.selected (CellLayout.Binary.cells 3 4 5) (.inr 0)).val = 13 := by decide
example : (CellLayout.Prime.index 3 4 (.inl (.inr (.inl 0)))).val = 3 := by simp
example : (CellLayout.Prime.index 3 4 (.inr ())).val = 7 := by simp
example : (CellLayout.Prime.index 3 4 (.inl (.inr (.inr 0)))).val = 8 := by
  rw [CellLayout.Prime.index_fingerprint]; rfl

-- R and the two pads follow the hash's own private inputs.
example {B : Type} [Field B] [Algebra (ZMod 2) B] (circuit : ConcreteSetup.BinaryCircuit B) :
    (circuit.advicePrivate 1 9).val = circuit.hashPrivate+275 := by
  simp [ConcreteSetup.BinaryCircuit.advicePrivate,Nat.add_assoc]

-- The virtual suffix starts right after the committed inputs.
example {B : Type} [Field B] [Algebra (ZMod 2) B] (circuit : ConcreteSetup.BinaryCircuit B) :
    (ConcreteSetup.cubeIndex circuit.input (circuit.virtualIndex 0)).val = circuit.nPublic+circuit.nPrivate := by
  simp [ConcreteSetup.BinaryCircuit.virtualIndex]

private def fragment (component : ℕ) : ConcreteTopology.Fragment 0 0 (ZMod 3) where
  circuit := component
  layer := 0
  quads := {
    outputs := 1
    inputs := 1
    outputIndex := fun _ => ()
    inputIndex := fun _ => ()
    terms := [.quadratic 0 0 0 1] }
  quadratic := [(0,0)]
  linear := [0]

private def circuit : ConcreteTopology.Circuit (ZMod 3) 0 0 :=
  .layer [fragment 0,fragment 1] .input

/-- Multiple fragments share the same assertion, terminal and combine
boundaries even at the scalar-layer edge case. -/
example : circuit.plan.frontend.roles .binary =
    [.assertions .binary 0 [] [⟨0,0,1,1⟩,⟨1,0,1,1⟩],
      .terminal .binary 0,.combine .binary 0 []] := rfl

example : (ConcreteTopology.Layer.circuit [fragment 0,fragment 1]).assertions ⟨0,by decide⟩ =
    .quadratic () () := rfl

example : (ConcreteTopology.Layer.circuit [fragment 0,fragment 1]).assertions ⟨2,by decide⟩ =
    .linear () := rfl

example : (ConcreteSetup.backend ConcreteSetup.primeNodes 263).backend.r = 84 ∧
    (ConcreteSetup.backend ConcreteSetup.primeNodes 263).backend.q = 265 ∧
    (ConcreteSetup.backend ConcreteSetup.primeNodes 263).backend.nw = 1 := by
  exact ⟨rfl,rfl,rfl⟩

#print axioms ConcreteSetup.rows_capacity
#print axioms ConcreteSetup.primeNodes
#print axioms ConcreteSetup.binaryNodes
#print axioms ConcreteSetup.addresses_eq
#print axioms ConcreteSetup.BinaryCircuit.plan

end LfzkV2.Current.Tests.ConcreteSetup
