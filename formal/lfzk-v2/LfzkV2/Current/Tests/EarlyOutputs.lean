import LfzkV2.Linear.Constraints

/-! The scalar counterexample exercised by the Rust tests in
`runtime/v2/sumcheck/tests/fragments.rs`. All committed pads are zero. The
future output coefficient is `gamma`; if known early, it can be included in
the first masked claim. Both terminal equations and the final input equation
then pass for every later scale and combine challenge, despite input `1`.
The second layer is an identity, so the example has a genuine shorter circuit.
This checks the actual affine frontend verifier predicate. -/
namespace LfzkV2.Current.Tests.EarlyOutputs
open SumcheckV2

variable {F : Type} [Field F]

def terminal (A B linear scale alpha : F) : Linear.LayerTranscript Unit F where
  rounds := []
  challenges := []
  cross := 0
  scale := scale
  messageA := A
  messageB := B
  padA := ()
  padB := ()
  padAB := ()
  padD := ()
  alpha := alpha
  constant := 0
  linear := linear

theorem early_output_attack (gamma scale₀ scale₁ alpha₀ alpha₁ : F) :
    Linear.ClearAccepts (fun _ : Unit => (0 : F)) 0
      [terminal (1+gamma) 0 0 scale₀ alpha₀,
        terminal 1 (1+gamma) (1+gamma) scale₁ alpha₁] 1 := by
  simp [Linear.ClearAccepts, terminal, Linear.LayerTranscript.clearRounds,
    LinearTerminal.residual, Linear.LayerTranscript.terminalPads,
    Linear.LayerTranscript.nextValue, Linear.LayerTranscript.clearA,
    Linear.LayerTranscript.clearB, LinearTerminal.clearA, LinearTerminal.clearB]

/-- This is acceptance on a fixed false output, for every future challenge,
not a low-probability collision or a guessed final seal. -/
theorem accepted_false_output (gamma scale₀ scale₁ alpha₀ alpha₁ : F) :
    Linear.ClearAccepts (fun _ : Unit => (0 : F)) 0
      [terminal (1+gamma) 0 0 scale₀ alpha₀,
        terminal 1 (1+gamma) (1+gamma) scale₁ alpha₁] 1 ∧ (1 : F) ≠ 0 :=
  ⟨early_output_attack gamma scale₀ scale₁ alpha₀ alpha₁, one_ne_zero⟩

end LfzkV2.Current.Tests.EarlyOutputs
