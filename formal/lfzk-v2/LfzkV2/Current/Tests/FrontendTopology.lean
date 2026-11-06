import LfzkV2.Current.FrontendTopology

namespace LfzkV2.Current.Tests.FrontendTopology
open SumcheckV2 LfzkV2.Current.FrontendTopology LfzkV2.Current.FrontendSchedule

private def body (coefficient : ℕ) : LfzkV2.Native.CircuitLayer (Cube 0) (Cube 0) (Fin 1) ℕ where
  quadratic _ _ _ := coefficient
  linear _ _ := coefficient+1
  constant _ := coefficient+2
  assertions _ := .quadratic () ()

private def metadata : LayerMetadata (body 0) where
  fragments := [⟨7,4,1,0⟩]
  count := rfl
  quadratic_first i := by fin_cases i; rfl

private def first : Layered.Circuit ℕ 0 0 := .layer 1 (body 0) .input
private def second : Layered.Circuit ℕ 0 0 := .layer 1 (body 19) .input
private def same : Same first second := .layer (fun _ => rfl) .input
private def plan : Plan ℕ first := .layer metadata .input

-- Changing every gate coefficient retains the supplied fragment identifiers
-- and exactly the same assertion, terminal and combine boundaries.
example : (same.plan plan).frontend.roles .binary =
    [.assertions .binary 0 [] [⟨7,4,1,0⟩],.terminal .binary 0,.combine .binary 0 []] := rfl
example : (same.plan plan).capacity = 1 := rfl

private def linearBody : LfzkV2.Native.CircuitLayer (Cube 0) (Cube 0) (Fin 1) ℕ where
  quadratic _ _ _ := 0
  linear _ _ := 0
  constant _ := 0
  assertions _ := .linear ()

-- Matching dimensions alone cannot relabel a quadratic assertion as linear.
example : ¬ Nonempty (Same first (.layer 1 linearBody .input)) := by
  rintro ⟨topology⟩
  cases topology with
  | layer classes tail =>
      have impossible := classes 0
      contradiction

end LfzkV2.Current.Tests.FrontendTopology
