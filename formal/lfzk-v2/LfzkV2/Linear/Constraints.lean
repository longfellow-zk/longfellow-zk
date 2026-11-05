import SumcheckV2.LinearTerminal
import LfzkV2.Native.Constraints

/-!
# Linear-terminal constraints and their sparse compiler

This namespace describes the `LFV5` frontend at Rust commit `21cb029`.
Every terminal contributes one affine equation over four ordinary committed
cells. In particular, candidate product cells are never assumed consistent.
The older `LfzkV2.Native` transcript remains the Step4 checkpoint.
-/

namespace LfzkV2.Linear

open SumcheckV2

variable {F Pad Slot : Type} [Field F]

structure LayerTranscript (Pad F : Type) where
  rounds : List (RoundPoly F × Pad × Pad)
  challenges : List F
  cross : F
  scale : F
  messageA : F
  messageB : F
  padA : Pad
  padB : Pad
  padAB : Pad
  padD : Pad
  alpha : F
  constant : F
  linear : F

namespace LayerTranscript

def clearRounds (t : LayerTranscript Pad F) (pads : Pad → F) : List (RoundPoly F) :=
  t.rounds.map fun (m, p0, p1) => unmask m ⟨pads p0, pads p1⟩

def terminalPads (t : LayerTranscript Pad F) (pads : Pad → F) : LinearTerminal.Pads F :=
  ⟨pads t.padA, pads t.padB, pads t.padAB, pads t.padD⟩

def clearA (t : LayerTranscript Pad F) (pads : Pad → F) : F :=
  LinearTerminal.clearA t.messageA t.scale (t.terminalPads pads)

def clearB (t : LayerTranscript Pad F) (pads : Pad → F) : F :=
  LinearTerminal.clearB t.messageB t.scale (t.terminalPads pads)

def nextValue (t : LayerTranscript Pad F) (pads : Pad → F) : F :=
  t.clearA pads + t.alpha * (t.clearB pads - t.linear)

def nextClaim (t : LayerTranscript Pad F) : PadExpression Pad F :=
  LinearTerminal.nextClaim t.messageA t.messageB t.scale t.alpha t.linear t.padA t.padB

theorem eval_nextClaim (t : LayerTranscript Pad F) (pads : Pad → F) :
    t.nextClaim.eval pads = t.nextValue pads :=
  LinearTerminal.eval_nextClaim _ _ _ _ _ _ _ t.padAB t.padD pads

def row (t : LayerTranscript Pad F) (claim : PadExpression Pad F) : PadExpression Pad F :=
  LinearTerminal.row claim t.cross t.scale t.messageA t.messageB t.padAB t.padD

theorem eval_row (t : LayerTranscript Pad F) (claim : PadExpression Pad F) (pads : Pad → F) :
    (t.row claim).eval pads = LinearTerminal.residual (claim.eval pads) t.cross t.scale
      t.messageA t.messageB (t.terminalPads pads) :=
  LinearTerminal.eval_row claim _ _ _ _ t.padA t.padB t.padAB t.padD pads

end LayerTranscript

structure Constraints (Pad F : Type) where
  layers : List (PadExpression Pad F)
  inputClaim : PadExpression Pad F

def Constraints.Holds (cs : Constraints Pad F) (pads : Pad → F) (inputSum : F) : Prop :=
  (∀ row ∈ cs.layers, row.eval pads = 0) ∧ cs.inputClaim.eval pads = inputSum

def buildFrom (claim : PadExpression Pad F) : List (LayerTranscript Pad F) →
    Option (Constraints Pad F)
  | [] => some ⟨[], claim⟩
  | t :: ts => do
      let terminal ← (Native.subtractConstant claim t.constant).rounds t.rounds t.challenges
      let rest ← buildFrom t.nextClaim ts
      pure ⟨t.row terminal :: rest.layers, rest.inputClaim⟩

def buildConstraints (ts : List (LayerTranscript Pad F)) : Option (Constraints Pad F) :=
  buildFrom zeroClaim ts

/-- This is a verifier predicate: the terminal scalar comes from the rounds,
and is then checked by the authenticated affine row. -/
def ClearAccepts (pads : Pad → F) (claim : F) : List (LayerTranscript Pad F) → F → Prop
  | [], inputSum => claim = inputSum
  | t :: ts, inputSum =>
      (∃ terminal,
        verify_multi_round (claim - t.constant) (t.clearRounds pads) t.challenges = some terminal ∧
        LinearTerminal.residual terminal t.cross t.scale t.messageA t.messageB
          (t.terminalPads pads) = 0) ∧
      ClearAccepts pads (t.nextValue pads) ts inputSum

theorem buildFrom_correct (claim : PadExpression Pad F) (ts : List (LayerTranscript Pad F))
    (pads : Pad → F) (inputSum : F) :
    (∃ cs, buildFrom claim ts = some cs ∧ cs.Holds pads inputSum) ↔
      ClearAccepts pads (claim.eval pads) ts inputSum := by
  induction ts generalizing claim with
  | nil => simp [buildFrom, Constraints.Holds, ClearAccepts]
  | cons t ts ih =>
      have heval := PadExpression.eval_rounds (Native.subtractConstant claim t.constant)
        t.rounds t.challenges pads
      rw [Native.eval_subtractConstant] at heval
      change Option.map (fun e => e.eval pads)
        ((Native.subtractConstant claim t.constant).rounds t.rounds t.challenges) =
        verify_multi_round (claim.eval pads - t.constant) (t.clearRounds pads) t.challenges at heval
      cases hr : (Native.subtractConstant claim t.constant).rounds t.rounds t.challenges with
      | none =>
          simp only [hr, Option.map_none] at heval
          simp [buildFrom, hr, ClearAccepts, ← heval]
      | some terminal =>
          simp only [hr, Option.map_some] at heval
          cases ht : buildFrom t.nextClaim ts with
          | none =>
              have htail : ¬ ClearAccepts pads (t.nextValue pads) ts inputSum := by
                rw [← t.eval_nextClaim, ← ih]
                simp [ht]
              simp [buildFrom, hr, ht, ClearAccepts, htail]
          | some rest =>
              have htail : rest.Holds pads inputSum ↔
                  ClearAccepts pads (t.nextValue pads) ts inputSum := by
                rw [← t.eval_nextClaim, ← ih]
                simp [ht]
              simpa [buildFrom, hr, ht, Constraints.Holds, ClearAccepts,
                ← heval, t.eval_row, and_assoc] using and_congr_right (fun _ => htail)

theorem buildConstraints_correct (ts : List (LayerTranscript Pad F)) (pads : Pad → F)
    (inputSum : F) :
    (∃ cs, buildConstraints ts = some cs ∧ cs.Holds pads inputSum) ↔
      ClearAccepts pads 0 ts inputSum := by
  simpa [buildConstraints, zeroClaim, PadExpression.eval] using
    buildFrom_correct zeroClaim ts pads inputSum

def compile {nPublic nPrivate : ℕ} (cs : Constraints Pad F)
    (coordinate : Pad → Slot) (privateCoordinate : Fin nPrivate → Slot)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F) :
    List (LinearRow Slot F) :=
  cs.layers.map (fun row => ⟨row.constant, mapTerms row.terms coordinate⟩) ++
    [compileInput cs.inputClaim coordinate privateCoordinate publicWeights publicInputs privateWeights]

/-- The input equation is shared with the checkpoint compiler. Terminal rows
need only renaming of coordinates; no auxiliary product or copy rows exist. -/
theorem compile_correct {nPublic nPrivate : ℕ} (cs : Constraints Pad F)
    (coordinate : Pad → Slot) (privateCoordinate : Fin nPrivate → Slot)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F)
    (witness : Slot → F) :
    RowsHold (compile cs coordinate privateCoordinate publicWeights publicInputs privateWeights)
        witness ↔
      cs.Holds (witness ∘ coordinate)
        (dot (Sum.elim publicWeights privateWeights)
          (Sum.elim publicInputs (witness ∘ privateCoordinate))) := by
  simp only [RowsHold, compile, List.forall_mem_append, List.forall_mem_map,
    List.forall_mem_singleton, eval_compileInput, sub_eq_zero, Constraints.Holds]
  simp [PadExpression.eval, mapTerms, Function.comp_def]

theorem compiled_iff_clear {nPublic nPrivate : ℕ}
    (ts : List (LayerTranscript Pad F)) (cs : Constraints Pad F)
    (hbuild : buildConstraints ts = some cs)
    (coordinate : Pad → Slot) (privateCoordinate : Fin nPrivate → Slot)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F)
    (witness : Slot → F) :
    RowsHold (compile cs coordinate privateCoordinate publicWeights publicInputs privateWeights)
        witness ↔
      ClearAccepts (witness ∘ coordinate) 0 ts
        (dot (Sum.elim publicWeights privateWeights)
          (Sum.elim publicInputs (witness ∘ privateCoordinate))) := by
  rw [compile_correct]
  have h := buildConstraints_correct ts (witness ∘ coordinate)
    (dot (Sum.elim publicWeights privateWeights)
      (Sum.elim publicInputs (witness ∘ privateCoordinate)))
  simpa only [hbuild, Option.some.injEq, exists_eq_left'] using h

end LfzkV2.Linear
