import SumcheckV2.LinearTerminalMasking
import Mathlib.Data.Fintype.Card

/-! The cross coefficient is sent before the terminal scale is known.  A
fixed-scale bijection alone therefore does not justify Fiat--Shamir hiding.
Here the nonzero scale may be any function of that first message (and of an
already fixed prefix).  The inverse reads the scale at the same message.

The resulting simulator samples the cross coefficient and both masked factors
uniformly.  Recovering secret pads is only the coupling used in the proof; the
simulator itself needs neither clear factor.  Commitment and opening privacy
are separate obligations, not hypotheses hidden in this local result. -/
namespace SumcheckV2.LinearTerminal

open scoped Classical

variable {F : Type} [Field F]

def adaptiveHonestMessages (A B : F) (scale : F → {r : F // r ≠ 0})
    (pads : F × F × F) : F × F × F :=
  let cross := A * pads.2.1 + B * pads.1 - pads.2.2
  honestMessages A B (scale cross).val pads

def adaptiveRecoverPads (A B : F) (scale : F → {r : F // r ≠ 0})
    (messages : F × F × F) : F × F × F :=
  recoverPads A B (scale messages.1).val messages

theorem adaptive_recover_honest (A B : F) (scale : F → {r : F // r ≠ 0})
    (pads : F × F × F) :
    adaptiveRecoverPads A B scale (adaptiveHonestMessages A B scale pads) = pads := by
  exact recover_honest A B _ (scale _).property pads

theorem adaptive_honest_recover (A B : F) (scale : F → {r : F // r ≠ 0})
    (messages : F × F × F) :
    adaptiveHonestMessages A B scale (adaptiveRecoverPads A B scale messages) = messages := by
  have h := honest_recover A B (scale messages.1).val (scale messages.1).property messages
  have hc := congrArg Prod.fst h
  change A * (recoverPads A B (scale messages.1).val messages).2.1 +
    B * (recoverPads A B (scale messages.1).val messages).1 -
    (recoverPads A B (scale messages.1).val messages).2.2 = messages.1 at hc
  simpa only [adaptiveHonestMessages, adaptiveRecoverPads, hc] using h

def adaptiveMaskingEquiv (A B : F) (scale : F → {r : F // r ≠ 0}) :
    (F × F × F) ≃ (F × F × F) where
  toFun := adaptiveHonestMessages A B scale
  invFun := adaptiveRecoverPads A B scale
  left_inv := adaptive_recover_honest A B scale
  right_inv := adaptive_honest_recover A B scale

/-- Exactly one honest pad tape gives each simulated message triple.  This
is equality of the full three-message distribution, even for adaptive scales. -/
theorem adaptive_uniform_fiber [Fintype F] (A B : F)
    (scale : F → {r : F // r ≠ 0}) (messages : F × F × F) :
    (Finset.univ.filter fun pads => adaptiveHonestMessages A B scale pads = messages).card = 1 := by
  classical
  have heq : (Finset.univ.filter fun pads =>
      adaptiveHonestMessages A B scale pads = messages) =
      {adaptiveRecoverPads A B scale messages} := by
    ext pads
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact (adaptiveMaskingEquiv A B scale).apply_eq_iff_eq_symm_apply
  rw [heq, Finset.card_singleton]

/-- The candidate product cell is derived, not an independent random pad.
Keeping it in the coupling is essential for a later joint commitment proof. -/
def honestPadCells (pads : F × F × F) : Pads F :=
  ⟨pads.1, pads.2.1, pads.1 * pads.2.1, pads.2.2⟩

theorem adaptive_simulated_terminal (A B : F)
    (scale : F → {r : F // r ≠ 0}) (messages : F × F × F) :
    residual (A * B) messages.1 (scale messages.1).val messages.2.1 messages.2.2
      (honestPadCells (adaptiveRecoverPads A B scale messages)) = 0 := by
  let pads := adaptiveRecoverPads A B scale messages
  have h := adaptive_honest_recover A B scale messages
  have hc := congrArg Prod.fst h
  have ha := congrArg (fun m : F × F × F => m.2.1) h
  have hb := congrArg (fun m : F × F × F => m.2.2) h
  change A * pads.2.1 + B * pads.1 - pads.2.2 = messages.1 at hc
  change A + (scale (A * pads.2.1 + B * pads.1 - pads.2.2)).val * pads.1 = messages.2.1 at ha
  change B + (scale (A * pads.2.1 + B * pads.1 - pads.2.2)).val * pads.2.1 = messages.2.2 at hb
  rw [hc] at ha hb
  change residual (A * B) messages.1 (scale messages.1).val messages.2.1 messages.2.2
    ⟨pads.1, pads.2.1, pads.1 * pads.2.1, pads.2.2⟩ = 0
  simpa only [hc, ha, hb] using
    (completeness A B pads.1 pads.2.1 pads.2.2 (scale messages.1).val)

end SumcheckV2.LinearTerminal
