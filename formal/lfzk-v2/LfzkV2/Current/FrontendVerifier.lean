import LfzkV2.Current.Application

/-! Concrete frontend reconstruction for the current verifier.  Public setup
fixes the circuit, input addresses and pad plan.  The proof supplies only the
masked polynomial payload; replay supplies the answers.  In particular neither
the compiled affine constraints nor a certificate that compilation succeeded
is accepted from the prover or from a caller.

This is the typed frontend stage, after length and field decoding.  Its callers
still have to obtain the payload and answers from the canonical transcript.
The separate transcript reader proves that correspondence. -/
noncomputable section
namespace LfzkV2.Current.FrontendVerifier
open SumcheckV2

variable {F Pad C : Type} [Field F]

/-- Run the existing affine compiler on messages reconstructed from the
grouped answer stream.  The fallback is unreachable: `constraints_built`
proves that every well-shaped payload compiles successfully. -/
def constraints {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Layered.Replay.Payload circuit)
    (decode : C → ℕ → F) (nonzero : C → Linear.TerminalSampling.Nonzero F)
    (answers : ℕ → C) : Linear.Constraints Pad F :=
  (Linear.buildConstraints
    (circuit.proof (FrontendReplay.read decode nonzero circuit plan payload answers) 0)).getD
    ⟨[], zeroClaim⟩

theorem constraints_built {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Layered.Replay.Payload circuit)
    (decode : C → ℕ → F) (nonzero : C → Linear.TerminalSampling.Nonzero F)
    (answers : ℕ → C) :
    Linear.buildConstraints
      (circuit.proof (FrontendReplay.read decode nonzero circuit plan payload answers) 0) =
      some (constraints circuit plan payload decode nonzero answers) := by
  obtain ⟨cs, hcs⟩ := FrontendReplay.constraints_total decode nonzero circuit plan payload answers
  simp only [constraints, hcs, Option.getD_some]

/-- All prime input addresses are public.  No sumcheck messages, affine
rows, replay identities or soundness certificates are part of setup. -/
structure PrimeSetup (N Slot Pad : Type) [Field N] where
  out : ℕ
  input : ℕ
  nPublic : ℕ
  nPrivate : ℕ
  circuit : Layered.Circuit N out input
  inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input
  publicInputs : Fin nPublic → N
  privateCoordinate : Fin nPrivate → Slot
  coordinate : Pad → Slot
  plan : Layered.Replay.PadPlan (Pad := Pad) circuit

namespace PrimeSetup
variable {N Slot : Type} [Field N] (setup : PrimeSetup N Slot Pad)

def prepare (payload : Layered.Replay.Payload setup.circuit)
    (decode : C → ℕ → N) (nonzero : C → Linear.TerminalSampling.Nonzero N)
    (answers : ℕ → C) : Frontend.Prime N Slot Pad where
  out := setup.out
  input := setup.input
  nPublic := setup.nPublic
  nPrivate := setup.nPrivate
  circuit := setup.circuit
  messages := FrontendReplay.read decode nonzero setup.circuit setup.plan payload answers
  inputIndex := setup.inputIndex
  publicInputs := setup.publicInputs
  privateCoordinate := setup.privateCoordinate
  coordinate := setup.coordinate
  constraints := constraints setup.circuit setup.plan payload decode nonzero answers
  built := constraints_built setup.circuit setup.plan payload decode nonzero answers

def replay (payload : Layered.Replay.Payload setup.circuit)
    (decode : C → ℕ → N) (nonzero : C → Linear.TerminalSampling.Nonzero N)
    (answers : ℕ → C) : Application.Replay
      (setup.prepare payload decode nonzero answers).circuit
      (setup.prepare payload decode nonzero answers).messages C where
  decode := decode
  nonzero := nonzero
  plan := setup.plan
  payload := payload
  answers := answers
  agrees := rfl

end PrimeSetup

/-- The binary public setup fixes the complete input-packing map.  The
packing witness and sumcheck pads are backend cells, never extra field-valued
inputs to the binary circuit. -/
structure PackedSetup (B I J Slot Pad : Type) [Field B] [Fintype B]
    [Algebra (ZMod 2) B] [Fintype I] [DecidableEq I] [Fintype J] where
  out : ℕ
  input : ℕ
  nPublic : ℕ
  nPrivate : ℕ
  circuit : Layered.Circuit B out input
  packing : LfzkV2.Packed.Statement (ZMod 2) B I J Slot
  inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input
  packedIndex : Fin nPrivate ↪ J × I
  publicInputs : Fin nPublic → B
  nVirtual : ℕ
  virtualIndex : Fin nVirtual ↪ Cube input
  /-- Per-proof virtual definitions; they never change the circuit or its plan. -/
  virtualInputs : Fin nVirtual → VirtualInput (Fin nPrivate) B
  coordinate : Pad → Slot
  plan : Layered.Replay.PadPlan (Pad := Pad) circuit

namespace PackedSetup
variable {B I J Slot : Type} [Field B] [Fintype B]
  [Algebra (ZMod 2) B] [Fintype I] [DecidableEq I] [Fintype J]
variable (setup : PackedSetup B I J Slot Pad)

def prepare (payload : Layered.Replay.Payload setup.circuit)
    (decode : C → ℕ → B) (nonzero : C → Linear.TerminalSampling.Nonzero B)
    (answers : ℕ → C) (U delta : I → B) (A : B) : Frontend.Packed B I J Slot Pad where
  out := setup.out
  input := setup.input
  nPublic := setup.nPublic
  nPrivate := setup.nPrivate
  circuit := setup.circuit
  messages := FrontendReplay.read decode nonzero setup.circuit setup.plan payload answers
  packing := setup.packing
  inputIndex := setup.inputIndex
  packedIndex := setup.packedIndex
  publicInputs := setup.publicInputs
  nVirtual := setup.nVirtual
  virtualIndex := setup.virtualIndex
  virtualInputs := setup.virtualInputs
  coordinate := setup.coordinate
  constraints := constraints setup.circuit setup.plan payload decode nonzero answers
  built := constraints_built setup.circuit setup.plan payload decode nonzero answers
  U := U
  delta := delta
  A := A

def replay (payload : Layered.Replay.Payload setup.circuit)
    (decode : C → ℕ → B) (nonzero : C → Linear.TerminalSampling.Nonzero B)
    (answers : ℕ → C) (U delta : I → B) (A : B) : Application.Replay
      (setup.prepare payload decode nonzero answers U delta A).circuit
      (setup.prepare payload decode nonzero answers U delta A).messages C where
  decode := decode
  nonzero := nonzero
  plan := setup.plan
  payload := payload
  answers := answers
  agrees := rfl

end PackedSetup
end LfzkV2.Current.FrontendVerifier
