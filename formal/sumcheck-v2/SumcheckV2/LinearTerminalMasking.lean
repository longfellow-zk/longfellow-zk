import SumcheckV2.LinearTerminal

/-!
# The honest terminal masking bijection

For fixed true claims and a fixed nonzero scale, the three independent pads
are in bijection with the cross message and two masked claims. This is a
local algebraic hiding fact. It does not assert joint zero knowledge of an
adaptive transcript and its commitment openings.
-/

namespace SumcheckV2.LinearTerminal

variable {F : Type} [Field F]

def honestMessages (A B scale : F) (pads : F × F × F) : F × F × F :=
  (A * pads.2.1 + B * pads.1 - pads.2.2,
    A + scale * pads.1, B + scale * pads.2.1)

def recoverPads (A B scale : F) (messages : F × F × F) : F × F × F :=
  ((messages.2.1 - A) / scale, (messages.2.2 - B) / scale,
    A * ((messages.2.2 - B) / scale) + B * ((messages.2.1 - A) / scale) - messages.1)

theorem recover_honest (A B scale : F) (hnonzero : scale ≠ 0) (pads : F × F × F) :
    recoverPads A B scale (honestMessages A B scale pads) = pads := by
  rcases pads with ⟨pA, pB, pD⟩
  simp [recoverPads, honestMessages, hnonzero]

theorem honest_recover (A B scale : F) (hnonzero : scale ≠ 0) (messages : F × F × F) :
    honestMessages A B scale (recoverPads A B scale messages) = messages := by
  rcases messages with ⟨cross, mA, mB⟩
  simp [recoverPads, honestMessages]
  constructor <;> field_simp <;> ring

def maskingEquiv (A B scale : F) (hnonzero : scale ≠ 0) : (F × F × F) ≃ (F × F × F) where
  toFun := honestMessages A B scale
  invFun := recoverPads A B scale
  left_inv := recover_honest A B scale hnonzero
  right_inv := honest_recover A B scale hnonzero

end SumcheckV2.LinearTerminal
