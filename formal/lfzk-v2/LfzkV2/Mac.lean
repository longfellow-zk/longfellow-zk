import LfzkV1.Mac

/-! V2's cross-field MAC: one verifier multiplier for all blocks and one
private additive pad per block. Soundness permits different fixed pads on
the two extracted sides. -/

namespace LfzkV2.Mac

open Finset
open scoped Classical

variable {F : Type} [Field F] {blocks : ℕ}

def tag (av : F) (ap message : Fin blocks → F) : Fin blocks → F :=
  fun j => av * message j + ap j

/-- Only the fixed-pair affine collision lemma is reused from V1. -/
theorem collision_card_le_one [Fintype F] [DecidableEq F]
    (ap ap' message message' : Fin blocks → F) (hne : message ≠ message') :
    (univ.filter fun av => tag av ap message = tag av ap' message').card ≤ 1 :=
  LfzkV1.Mac.macTag_collision_card_le_one ap ap' message message' hne

end LfzkV2.Mac
