import LfzkV2.Current.ZeroKnowledge.FrontendCorrectness

/-! Where a stage starts in the current verifier's grouped answer replay
(`Current.FrontendReplay`). A continuing stage starts one answer earlier,
at the preceding combine answer. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend
open SumcheckV2
open scoped Classical
variable {F C Pad : Type} [Field F]

def replayStart {out input : ℕ} (_circuit : Layered.Circuit F out input)
    (state : ℕ) (continuing : Bool) : ℕ :=
  if continuing then state-1 else state

def replayOffset {out input : ℕ} (_circuit : Layered.Circuit F out input)
    (continuing : Bool) : ℕ :=
  if continuing then 1 else 0

end LfzkV2.Current.ZeroKnowledge.Frontend
