import LfzkV2.Linear.Circuit
import LfzkV2.Linear.Challenges
import LfzkV2.ReplayPrimitives

/-!
# The linear-terminal message and challenge schedule

Each layer sends its cross coefficient before the terminal scale and its two
masked claims before the combining challenge. The plan fixes all four cells
before commitment. Scalar layers still execute both terminal challenges.
-/

namespace LfzkV2.Linear.Replay

open SumcheckV2

variable {F Pad C : Type} [Field F]

structure LayerPads (Pad : Type) (rounds : ℕ) where
  round : Fin rounds → Pad × Pad
  a : Pad
  b : Pad
  ab : Pad
  d : Pad

structure LayerPayload (F : Type) (rounds : ℕ) where
  rounds : Fin rounds → RoundPoly F
  cross : F
  claimA : F
  claimB : F

abbrev PadPlan : {out input : ℕ} → Native.Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .layer (mid := mid) _ _ rest => LayerPads Pad mid × PadPlan rest

abbrev Payload : {out input : ℕ} → Native.Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .layer (mid := mid) _ _ rest => LayerPayload F mid × Payload rest

open LfzkV2.Replay (vectorSlots)

end LfzkV2.Linear.Replay
