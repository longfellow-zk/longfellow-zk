import SumcheckV2.Masked

/-!
# V2 symbolic layer execution

The layer order is from circuit outputs to inputs, as in
`runtime/v2/sumcheck/src/symbolic.rs`. Round messages carry their logical pad
identifiers. Product slots are separate committed coordinates: the symbolic
builder records their affine residuals, while the backend must also check the
pad products. Mismatched round/challenge counts are rejected.
-/

namespace LfzkV2

open SumcheckV2

variable {F Pad Slot : Type} [Field F]

structure LayerTranscript (Pad Slot F : Type) where
  rounds : List (RoundPoly F × Pad × Pad)
  challenges : List F
  messageA : F
  messageB : F
  padA : Pad
  padB : Pad
  productSlot : Slot
  alpha : F

namespace LayerTranscript

def clearRounds (t : LayerTranscript Pad Slot F) (pads : Pad → F) : List (RoundPoly F) :=
  t.rounds.map fun (m, p0, p1) => unmask m ⟨pads p0, pads p1⟩

def clearA (t : LayerTranscript Pad Slot F) (pads : Pad → F) : F := t.messageA + pads t.padA
def clearB (t : LayerTranscript Pad Slot F) (pads : Pad → F) : F := t.messageB + pads t.padB

def nextClaim (t : LayerTranscript Pad Slot F) : PadExpression Pad F :=
  PadExpression.claimNext t.messageA t.messageB t.alpha t.padA t.padB

@[simp] theorem eval_nextClaim (t : LayerTranscript Pad Slot F) (pads : Pad → F) :
    t.nextClaim.eval pads = t.clearA pads + t.alpha * t.clearB pads :=
  PadExpression.eval_claimNext ..

end LayerTranscript

structure LayerConstraint (Pad Slot F : Type) where
  expression : PadExpression Pad F
  padA : Pad
  padB : Pad
  productSlot : Slot

def LayerConstraint.Holds (c : LayerConstraint Pad Slot F) (pads : Pad → F) : Prop :=
  c.expression.eval pads = pads c.padA * pads c.padB

structure Constraints (Pad Slot F : Type) where
  layers : List (LayerConstraint Pad Slot F)
  inputClaim : PadExpression Pad F

def Constraints.Holds (cs : Constraints Pad Slot F) (pads : Pad → F) (inputSum : F) : Prop :=
  (∀ c ∈ cs.layers, c.Holds pads) ∧ cs.inputClaim.eval pads = inputSum

def LayerTranscript.constraint (t : LayerTranscript Pad Slot F) (e : PadExpression Pad F) :
    LayerConstraint Pad Slot F :=
  ⟨e.subtractClaimProduct t.messageA t.messageB t.padA t.padB,
    t.padA, t.padB, t.productSlot⟩

theorem LayerTranscript.constraint_holds_iff (t : LayerTranscript Pad Slot F)
    (e : PadExpression Pad F) (pads : Pad → F) :
    (t.constraint e).Holds pads ↔ e.eval pads = t.clearA pads * t.clearB pads := by
  change (e.subtractClaimProduct t.messageA t.messageB t.padA t.padB).eval pads =
    pads t.padA * pads t.padB ↔ _
  rw [← sub_eq_zero, PadExpression.eval_subtractClaimProduct, sub_eq_zero]
  rfl

/-- The Rust builder's complete layer loop, including its final input claim. -/
def buildFrom (claim : PadExpression Pad F) :
    List (LayerTranscript Pad Slot F) → Option (Constraints Pad Slot F)
  | [] => some ⟨[], claim⟩
  | t :: ts =>
      match claim.rounds t.rounds t.challenges, buildFrom t.nextClaim ts with
      | some terminal, some rest =>
          some ⟨t.constraint terminal :: rest.layers, rest.inputClaim⟩
      | _, _ => none

def zeroClaim : PadExpression Pad F := ⟨0, []⟩

def buildConstraints (ts : List (LayerTranscript Pad Slot F)) : Option (Constraints Pad Slot F) :=
  buildFrom zeroClaim ts

/-- Product checks depend only on the layout, not on messages or challenges. -/
theorem buildFrom_products (claim : PadExpression Pad F)
    (ts : List (LayerTranscript Pad Slot F)) (cs : Constraints Pad Slot F)
    (hbuild : buildFrom claim ts = some cs) :
    cs.layers.map (fun c => (c.padA, c.padB, c.productSlot)) =
      ts.map (fun t => (t.padA, t.padB, t.productSlot)) := by
  induction ts generalizing claim cs with
  | nil =>
      simp only [buildFrom, Option.some.injEq] at hbuild
      subst cs
      rfl
  | cons t ts ih =>
      cases hround : claim.rounds t.rounds t.challenges with
      | none => simp [buildFrom, hround] at hbuild
      | some terminal =>
          cases hrest : buildFrom t.nextClaim ts with
          | none => simp [buildFrom, hround, hrest] at hbuild
          | some rest =>
              simp only [buildFrom, hround, hrest, Option.some.injEq] at hbuild
              subst cs
              simp only [List.map_cons, LayerTranscript.constraint]
              rw [ih t.nextClaim rest hrest]

/-- Numerical verification after adding back the committed pads. -/
def ClearAccepts (pads : Pad → F) (claim : F) : List (LayerTranscript Pad Slot F) → F → Prop
  | [], inputSum => claim = inputSum
  | t :: ts, inputSum =>
      verify_multi_round claim (t.clearRounds pads) t.challenges =
        some (t.clearA pads * t.clearB pads) ∧
      ClearAccepts pads (t.clearA pads + t.alpha * t.clearB pads) ts inputSum

/-- Symbolic constraints and clear verification agree for the whole transcript.
This also accounts for rejection of unequal round/challenge list lengths. -/
theorem buildFrom_correct (claim : PadExpression Pad F)
    (ts : List (LayerTranscript Pad Slot F)) (pads : Pad → F) (inputSum : F) :
    (∃ cs, buildFrom claim ts = some cs ∧ cs.Holds pads inputSum) ↔
      ClearAccepts pads (claim.eval pads) ts inputSum := by
  induction ts generalizing claim with
  | nil => simp [buildFrom, Constraints.Holds, ClearAccepts]
  | cons t ts ih =>
      have hround := PadExpression.eval_rounds claim t.rounds t.challenges pads
      cases hterminal : claim.rounds t.rounds t.challenges with
      | none =>
          simp only [hterminal, Option.map_none] at hround
          simp [buildFrom, hterminal, ClearAccepts, LayerTranscript.clearRounds,
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
                LayerTranscript.clearRounds, ← hround,
                LayerTranscript.constraint_holds_iff, and_assoc] using
                and_congr_right (fun _ => htail)

/-- The initial claim is zero, including in a zero-layer circuit. -/
theorem buildConstraints_correct (ts : List (LayerTranscript Pad Slot F))
    (pads : Pad → F) (inputSum : F) :
    (∃ cs, buildConstraints ts = some cs ∧ cs.Holds pads inputSum) ↔
      ClearAccepts pads 0 ts inputSum := by
  simpa [buildConstraints, zeroClaim, PadExpression.eval] using
    buildFrom_correct (zeroClaim : PadExpression Pad F) ts pads inputSum

end LfzkV2
