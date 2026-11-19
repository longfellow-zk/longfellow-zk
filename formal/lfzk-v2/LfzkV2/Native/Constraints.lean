import LfzkV2.Compiler

/-!
# Native affine sumcheck constraints

The two corrections are reconstructed from the trusted circuit and earlier
challenges, not supplied by the prover. All round, pad, product-slot, and sparse
compiler operations are shared with the quadratic frontend. This builder adds
exactly the two constant updates in `rust/src/runtime/v2/sumcheck/symbolic.rs`.
-/

namespace LfzkV2.Native

open SumcheckV2

variable {F Pad Slot : Type} [Field F]

def subtractConstant (e : PadExpression Pad F) (k : F) : PadExpression Pad F :=
  ⟨e.constant - k, e.terms⟩

@[simp] theorem eval_subtractConstant (e : PadExpression Pad F) (k : F) (pads : Pad → F) :
    (subtractConstant e k).eval pads = e.eval pads - k := by
  simp only [subtractConstant, PadExpression.eval]
  ring

structure LayerTranscript (Pad Slot F : Type) where
  messages : LfzkV2.LayerTranscript Pad Slot F
  constant : F
  linear : F

namespace LayerTranscript

def nextValue (t : LayerTranscript Pad Slot F) (pads : Pad → F) : F :=
  t.messages.clearA pads + t.messages.alpha * (t.messages.clearB pads - t.linear)

def nextClaim (t : LayerTranscript Pad Slot F) : PadExpression Pad F :=
  subtractConstant t.messages.nextClaim (t.messages.alpha * t.linear)

@[simp] theorem eval_nextClaim (t : LayerTranscript Pad Slot F) (pads : Pad → F) :
    t.nextClaim.eval pads = t.nextValue pads := by
  simp only [nextClaim, eval_subtractConstant, LfzkV2.LayerTranscript.eval_nextClaim,
    nextValue]
  ring

end LayerTranscript

def buildFrom (claim : PadExpression Pad F) :
    List (LayerTranscript Pad Slot F) → Option (Constraints Pad Slot F)
  | [] => some ⟨[], claim⟩
  | t :: ts =>
      match (subtractConstant claim t.constant).rounds t.messages.rounds t.messages.challenges,
          buildFrom t.nextClaim ts with
      | some terminal, some rest =>
          some ⟨t.messages.constraint terminal :: rest.layers, rest.inputClaim⟩
      | _, _ => none

def buildConstraints (ts : List (LayerTranscript Pad Slot F)) : Option (Constraints Pad Slot F) :=
  buildFrom zeroClaim ts

def ClearAccepts (pads : Pad → F) (claim : F) : List (LayerTranscript Pad Slot F) → F → Prop
  | [], inputSum => claim = inputSum
  | t :: ts, inputSum =>
      verify_multi_round (claim - t.constant) (t.messages.clearRounds pads)
          t.messages.challenges = some (t.messages.clearA pads * t.messages.clearB pads) ∧
        ClearAccepts pads (t.nextValue pads) ts inputSum

/-- Exact corrected symbolic execution, including malformed round-count rejection. -/
theorem buildFrom_correct (claim : PadExpression Pad F)
    (ts : List (LayerTranscript Pad Slot F)) (pads : Pad → F) (inputSum : F) :
    (∃ cs, buildFrom claim ts = some cs ∧ cs.Holds pads inputSum) ↔
      ClearAccepts pads (claim.eval pads) ts inputSum := by
  induction ts generalizing claim with
  | nil => simp [buildFrom, Constraints.Holds, ClearAccepts]
  | cons t ts ih =>
      have hround := PadExpression.eval_rounds (subtractConstant claim t.constant)
        t.messages.rounds t.messages.challenges pads
      rw [eval_subtractConstant] at hround
      cases hterminal : (subtractConstant claim t.constant).rounds
          t.messages.rounds t.messages.challenges with
      | none =>
          simp only [hterminal, Option.map_none] at hround
          simp [buildFrom, hterminal, ClearAccepts, LfzkV2.LayerTranscript.clearRounds,
            ← hround]
      | some terminal =>
          simp only [hterminal, Option.map_some] at hround
          cases hrest : buildFrom t.nextClaim ts with
          | none =>
              have htail := ih t.nextClaim
              simp only [hrest, reduceCtorEq, false_and, exists_false,
                LayerTranscript.eval_nextClaim] at htail
              simp [buildFrom, hterminal, hrest, ClearAccepts, ← htail]
          | some rest =>
              have htail := ih t.nextClaim
              simp [hrest] at htail
              simpa [buildFrom, hterminal, hrest, Constraints.Holds, ClearAccepts,
                LfzkV2.LayerTranscript.clearRounds, ← hround,
                LfzkV2.LayerTranscript.constraint_holds_iff, and_assoc] using
                and_congr_right (fun _ => htail)

theorem buildConstraints_correct (ts : List (LayerTranscript Pad Slot F))
    (pads : Pad → F) (inputSum : F) :
    (∃ cs, buildConstraints ts = some cs ∧ cs.Holds pads inputSum) ↔
      ClearAccepts pads 0 ts inputSum := by
  simpa [buildConstraints, zeroClaim, PadExpression.eval] using
    buildFrom_correct (zeroClaim : PadExpression Pad F) ts pads inputSum

/-- The existing sparse compiler applies unchanged to the corrected expressions.
Product consistency is still checked separately; it is never inferred from a row. -/
theorem compiled_iff_clear {nPublic nPrivate : ℕ}
    (ts : List (LayerTranscript Pad Slot F)) (cs : Constraints Pad Slot F)
    (hbuild : buildConstraints ts = some cs)
    (coordinate : Pad → Slot) (privateCoordinate : Fin nPrivate → Slot)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F)
    (witness : Slot → F) (hproducts : ProductsHold cs coordinate witness) :
    RowsHold (compile cs coordinate privateCoordinate publicWeights publicInputs privateWeights)
        witness ↔
      ClearAccepts (witness ∘ coordinate) 0 ts
        (dot (Sum.elim publicWeights privateWeights)
          (Sum.elim publicInputs (witness ∘ privateCoordinate))) := by
  rw [compile_correct cs coordinate privateCoordinate publicWeights publicInputs privateWeights
    witness hproducts]
  have h := buildConstraints_correct ts (witness ∘ coordinate)
    (dot (Sum.elim publicWeights privateWeights)
      (Sum.elim publicInputs (witness ∘ privateCoordinate)))
  simpa only [hbuild, Option.some.injEq, exists_eq_left'] using h

end LfzkV2.Native
