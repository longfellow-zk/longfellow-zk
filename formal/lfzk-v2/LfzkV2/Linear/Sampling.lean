import LfzkV2.Linear.HashReplay

/-! Whole-answer samplers for the actual replay. The full hash answer remains
visible to the adversary, while ordinary and nonzero terminal projections
have separate balance equations. -/

namespace LfzkV2.Linear.Replay

open Challenges Finset
open scoped Classical

variable {F C Key : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype C]

structure Sampling {out input : ℕ} (circuit : Native.Circuit F out input) where
  decode : (n : ℕ) → C → Fin n → F
  terminal : TerminalSampling.Sampler F C
  fieldFiber : ℕ
  balanced : fieldFiber * Fintype.card F = Fintype.card C
  blocks : (i : Fin (slots circuit)) → Sampler F C (roleKind circuit ((roleEquiv circuit).symm i))
  agrees : ∀ i, (blocks i).decode =
    decodeSample decode terminal.decode (roleKind circuit ((roleEquiv circuit).symm i))
  terminal_fiber : ∀ i (hs : roleKind circuit ((roleEquiv circuit).symm i) = .terminal),
    (hs ▸ blocks i).fiber = terminal.fiber

def pointSampler {out input : ℕ} (circuit : Native.Circuit F out input)
    (sampling : Sampling (C := C) circuit) (point : Point Key F circuit) :
    Sampler F C (pointKind circuit point) :=
  match point with
  | (_, none) =>
      { decode := fun _ => Fin.elim0
        fiber := Fintype.card C
        fiber_bound := fun _ => card_filter_le _ _
        balanced := by simp [ChallengeBlocks.Kind.dimension] }
  | (_, some p) => sampling.blocks p.1

theorem pointSampler_bad_card {out input : ℕ} (circuit : Native.Circuit F out input)
    (sampling : Sampling (C := C) circuit) (point : Point Key F circuit)
    (data : Data F (pointKind circuit point)) (hvalid : data.Valid) :
    (univ.filter fun answer => data.Bad ((pointSampler circuit sampling point).decode answer)).card ≤
      (pointKind circuit point).rawBudget sampling.fieldFiber sampling.terminal.fiber := by
  apply Sampler.bad_card_le _ sampling.fieldFiber sampling.terminal.fiber sampling.balanced
    ?_ data hvalid
  intro hs
  rcases point with ⟨key, opt⟩
  cases opt with
  | none => cases hs
  | some p => exact sampling.terminal_fiber p.1 hs

end LfzkV2.Linear.Replay
