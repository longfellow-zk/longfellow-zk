import LfzkV2.Layered.Packed
import LfzkV2.Current.Prime

/-! The two frontend compilers at their affine-row boundary. These records
keep the circuit, messages, layouts and compiled constraints together; they
do not assume frontend acceptance or a soundness reduction. A backend reader
supplies every selected cell, including the sumcheck and packing pads. -/
namespace LfzkV2.Current
open SumcheckV2 DualPacking.ArtinSchreier

namespace Frontend

structure Packed (B I J Slot Pad : Type) [Field B] [Fintype B]
    [Algebra (ZMod 2) B] [Fintype I] [DecidableEq I] [Fintype J] where
  out : ℕ
  input : ℕ
  nPublic : ℕ
  nPrivate : ℕ
  circuit : Layered.Circuit B out input
  messages : Layered.Circuit.Messages Pad circuit
  packing : LfzkV2.Packed.Statement (ZMod 2) B I J Slot
  inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input
  packedIndex : Fin nPrivate ↪ J × I
  publicInputs : Fin nPublic → B
  coordinate : Pad → Slot
  constraints : Linear.Constraints Pad B
  built : Linear.buildConstraints (circuit.proof messages 0) = some constraints
  U : I → B
  delta : I → B
  A : B

namespace Packed
variable {B I J Slot Pad : Type} [Field B] [Fintype B] [DecidableEq B]
  [Algebra (ZMod 2) B] [Fintype I] [DecidableEq I] [Fintype J]
variable (b : Packed B I J Slot Pad)

noncomputable def inputs (read : Slot → B) : Cube b.input → B :=
  b.packing.inputs b.inputIndex b.packedIndex b.publicInputs read

noncomputable def rows : List (LinearRow Slot B) :=
  Linear.Packed.rows b.packing b.constraints b.packedIndex b.coordinate
    (fun i => b.circuit.inputWeights b.messages 0 (b.inputIndex (.inl i))) b.publicInputs
    (fun i => b.circuit.inputWeights b.messages 0 (b.inputIndex (.inr i))) b.U b.delta b.A

noncomputable def source : LfzkV2.Packed.Statement (ZMod 2) B I J Slot :=
  b.packing.withSource b.packedIndex b.constraints.inputClaim b.coordinate
    (fun i => b.circuit.inputWeights b.messages 0 (b.inputIndex (.inl i))) b.publicInputs
    (fun i => b.circuit.inputWeights b.messages 0 (b.inputIndex (.inr i)))

noncomputable def Bad (read : Slot → B) : Prop :=
  Layered.Circuit.Bad b.circuit b.messages (b.inputs read) 0 (read ∘ b.coordinate) 0 ∨
    b.source.Bad read b.U b.delta

/-- The verifier's trace check is explicit. Satisfaction of the actual packed
rows then gives circuit satisfaction or one of the existing algebraic events. -/
theorem rows_satisfy_or_bad (read : Slot → B)
    (htrace : ∀ k, traceF (ZMod 2) (b.U k) = 0) (hrows : RowsHold b.rows read) :
    b.circuit.Satisfies (b.inputs read) ∨ b.Bad read := by
  classical
  by_cases h : b.circuit.Satisfies (b.inputs read)
  · exact Or.inl h
  · exact Or.inr (Layered.Packed.rows_soundness b.packing b.circuit b.messages b.constraints
      b.built b.inputIndex b.packedIndex b.publicInputs b.coordinate read b.U b.delta b.A htrace hrows h)

end Packed

/-- The prime compiler retains its complete row vector before batching.
`Slot` will be partitioned into shared binary inputs and prime cells by the
application; it includes pad slots as well as private-input slots. -/
structure Prime (N Slot Pad : Type) [Field N] where
  out : ℕ
  input : ℕ
  nPublic : ℕ
  nPrivate : ℕ
  circuit : Layered.Circuit N out input
  messages : Layered.Circuit.Messages Pad circuit
  inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input
  publicInputs : Fin nPublic → N
  privateCoordinate : Fin nPrivate → Slot
  coordinate : Pad → Slot
  constraints : Linear.Constraints Pad N
  built : Linear.buildConstraints (circuit.proof messages 0) = some constraints

namespace Prime
variable {N Slot Pad : Type} [Field N]
variable (n : Prime N Slot Pad)

noncomputable def inputs (read : Slot → N) : Cube n.input → N :=
  circuitInputs n.inputIndex n.publicInputs n.privateCoordinate read

noncomputable def rows : List (LinearRow Slot N) :=
  Linear.compile n.constraints n.coordinate n.privateCoordinate
    (fun i => n.circuit.inputWeights n.messages 0 (n.inputIndex (.inl i))) n.publicInputs
    (fun i => n.circuit.inputWeights n.messages 0 (n.inputIndex (.inr i)))

noncomputable def Bad (read : Slot → N) : Prop :=
  Layered.Circuit.Bad n.circuit n.messages (n.inputs read) 0 (read ∘ n.coordinate) 0

theorem rows_satisfy_or_bad (read : Slot → N) (hrows : RowsHold n.rows read) :
    n.circuit.Satisfies (n.inputs read) ∨ n.Bad read := by
  classical
  by_cases h : n.circuit.Satisfies (n.inputs read)
  · exact Or.inl h
  · exact Or.inr (Layered.Circuit.compiled_circuit_reduction n.circuit n.messages n.inputIndex
      n.publicInputs n.privateCoordinate n.coordinate read n.constraints n.built hrows h)

end Prime
end Frontend
end LfzkV2.Current
