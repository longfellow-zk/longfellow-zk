import LfzkV2.Native.Prover
import LfzkV2.Native.Events
import Mathlib.Data.ZMod.Basic

/-! Native affine API checks: both corrections, assertion kinds, and degenerate shapes. -/

namespace LfzkV2.Native.APITest

open SumcheckV2 Classical

def scalarTranscript : Native.LayerTranscript Bool (Fin 4) ℚ where
  messages := {
    rounds := [], challenges := [], messageA := 3, messageB := 5,
    padA := false, padB := true, productSlot := 3, alpha := 7 }
  constant := -15
  linear := 2

-- Q=1, L=2, W=3: q=5 and the zero-output claim removes K=-15.
-- The corrected next claim is 3+7*(5-2)=24, with input weight 1+7=8.
example : Native.ClearAccepts (fun _ => (0 : ℚ)) 0 [scalarTranscript] 24 := by
  norm_num [Native.ClearAccepts, scalarTranscript, LayerTranscript.nextValue,
    LfzkV2.LayerTranscript.clearRounds, LfzkV2.LayerTranscript.clearA,
    LfzkV2.LayerTranscript.clearB, verify_multi_round]

example : ¬ Native.ClearAccepts (fun _ => (0 : ℚ)) 0
    [{ scalarTranscript with constant := 0 }] 24 := by
  norm_num [Native.ClearAccepts, scalarTranscript, LayerTranscript.nextValue,
    LfzkV2.LayerTranscript.clearRounds, LfzkV2.LayerTranscript.clearA,
    LfzkV2.LayerTranscript.clearB, verify_multi_round]

example : ¬ Native.ClearAccepts (fun _ => (0 : ℚ)) 0
    [{ scalarTranscript with linear := 0 }] 24 := by
  norm_num [Native.ClearAccepts, scalarTranscript, LayerTranscript.nextValue,
    LfzkV2.LayerTranscript.clearRounds, LfzkV2.LayerTranscript.clearA,
    LfzkV2.LayerTranscript.clearB, verify_multi_round]

example : ∃ cs, Native.buildConstraints [scalarTranscript] = some cs ∧
    cs.Holds (fun _ => 0) 24 :=
  (Native.buildConstraints_correct _ _ _).mpr (by
    norm_num [Native.ClearAccepts, scalarTranscript, LayerTranscript.nextValue,
      LfzkV2.LayerTranscript.clearRounds, LfzkV2.LayerTranscript.clearA,
      LfzkV2.LayerTranscript.clearB, verify_multi_round])

example : Native.buildConstraints
    [{ scalarTranscript with messages := { scalarTranscript.messages with challenges := [2] } }] =
      none := by
  rfl

example : Native.buildConstraints ([] : List (Native.LayerTranscript Unit Unit ℚ)) =
    some ⟨[], zeroClaim⟩ := rfl

example : ¬ Native.ClearAccepts (fun _ : Unit => (0 : ℚ)) 0
    ([] : List (Native.LayerTranscript Unit Unit ℚ)) 1 := by
  norm_num [Native.ClearAccepts]

def linearLayer : Native.CircuitLayer Unit Unit (Fin 0) ℚ where
  quadratic := fun _ _ _ => 0
  linear := fun _ _ => 2
  constant := fun _ => -6
  assertions := Fin.elim0

def linearCircuit : Native.Circuit ℚ 0 0 := .layer (mid := 0) 0 linearLayer .input

example : linearCircuit.Satisfies (fun _ => 3) := by
  constructor
  · funext i
    change linearLayer.outputs (fun _ : Unit => 3) i = 0
    norm_num [Native.CircuitLayer.outputs, linearLayer, quadratic, dot]
  · simp [linearCircuit, Native.Circuit.AssertionsValid]

-- A scalar linear layer has zero rounds; it uses the same combination test.
example : linearCircuit.sharpLayerBudget = 1 := rfl

def mixedAssertions : Native.CircuitLayer Unit Unit (Fin 2) ℚ where
  quadratic := fun _ _ _ => 0
  linear := fun _ _ => 0
  constant := fun _ => 0
  assertions := fun i => if i = 0 then .linear () else .quadratic () ()

example : mixedAssertions.effectiveQuadratic (fun _ => 0)
    (fun i => if i = 0 then 7 else 11) () () = 11 := by
  norm_num [Native.CircuitLayer.effectiveQuadratic, mixedAssertions,
    Native.AssertionTerm.quadraticKernel, Fin.sum_univ_two]

example : mixedAssertions.effectiveLinear (fun _ => 0)
    (fun i => if i = 0 then 7 else 11) () = 7 := by
  norm_num [Native.CircuitLayer.effectiveLinear, mixedAssertions,
    Native.AssertionTerm.linearKernel, Fin.sum_univ_two]

def duplicateLinearAssertions : Native.CircuitLayer Unit Unit (Fin 2) ℚ :=
  { mixedAssertions with assertions := fun _ => .linear () }

example : duplicateLinearAssertions.effectiveLinear (fun _ => 0)
    (fun i => if i = 0 then 7 else 11) () = 18 := by
  norm_num [Native.CircuitLayer.effectiveLinear, duplicateLinearAssertions, mixedAssertions,
    Native.AssertionTerm.linearKernel, Fin.sum_univ_two]

def invalidAssertionCircuit : Native.Circuit ℚ 0 0 := .layer (mid := 0) 2 mixedAssertions .input

example : invalidAssertionCircuit.eval (fun _ => 1) = 0 := by
  funext i
  simp [invalidAssertionCircuit, Native.Circuit.eval, Native.CircuitLayer.outputs,
    mixedAssertions, quadratic, dot]

example : ¬ invalidAssertionCircuit.Satisfies (fun _ => 1) := by
  intro h
  have hzero := h.2.1 (0 : Fin 2)
  norm_num [Native.CircuitLayer.residuals, mixedAssertions, Native.AssertionTerm.residual,
    Native.Circuit.eval] at hzero

-- The correction remains essential in characteristic two: A=1, B=0, L=1,
-- alpha=1 produces the next claim zero, matching the next input weight zero.
def binaryTranscript : Native.LayerTranscript Unit Unit (ZMod 2) where
  messages := {
    rounds := [], challenges := [], messageA := 1, messageB := 0,
    padA := (), padB := (), productSlot := (), alpha := 1 }
  constant := 0
  linear := 1

example : Native.ClearAccepts (fun _ => (0 : ZMod 2)) 0 [binaryTranscript] 0 := by
  norm_num [Native.ClearAccepts, binaryTranscript, LayerTranscript.nextValue,
    LfzkV2.LayerTranscript.clearRounds, LfzkV2.LayerTranscript.clearA,
    LfzkV2.LayerTranscript.clearB, verify_multi_round]

example : ¬ Native.ClearAccepts (fun _ => (0 : ZMod 2)) 0
    [{ binaryTranscript with linear := 0 }] 0 := by
  norm_num [Native.ClearAccepts, binaryTranscript, LayerTranscript.nextValue,
    LfzkV2.LayerTranscript.clearRounds, LfzkV2.LayerTranscript.clearA,
    LfzkV2.LayerTranscript.clearB, verify_multi_round]

-- The native events use the same root bounds, over any finite field.
example {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (test : ChallengeTest F) (h : test.Valid) :
    (Finset.univ.filter test.Bad).card ≤ test.budget := ChallengeTest.card_bad_le test h

end LfzkV2.Native.APITest
