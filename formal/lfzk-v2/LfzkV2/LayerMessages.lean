import LfzkV2.Constraints

/-! Logical layer messages and their symbolic transcript, shared by the
native runtime and the standalone quadratic circuit model. -/
namespace LfzkV2
open SumcheckV2

variable {F Pad Slot : Type} [Field F]

structure LayerMessages (Pad Slot F : Type) (rounds assertions : ℕ) where
  messages : List (RoundPoly F × Pad × Pad)
  point : Fin rounds → F
  messageA : F
  messageB : F
  padA : Pad
  padB : Pad
  productSlot : Slot
  alpha : F
  beta : Fin assertions → F

def LayerMessages.transcript {n a : ℕ} (m : LayerMessages Pad Slot F n a) :
    LayerTranscript Pad Slot F :=
  ⟨m.messages, List.ofFn m.point, m.messageA, m.messageB, m.padA, m.padB,
    m.productSlot, m.alpha⟩

theorem honestMessages_length {n : ℕ} (q w : Cube n → F) (point : Fin n → F) :
    (honestMessages q w point).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [honestMessages, List.length_cons, ih]

end LfzkV2
