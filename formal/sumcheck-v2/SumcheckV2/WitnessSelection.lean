import SumcheckV2.Round
import WitnessSelection.IOP

/-! Frontend bounds after early masked fingerprints. Backend mask rows need not
be unique. ChainedFiatShamir handles adaptive total-oracle searches and feedback. -/
namespace SumcheckV2
open Finset
open scoped Classical

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

/-- A later ordinary quadratic round pays two roots, not two per candidate. -/
theorem selected_round_bad_card_le
    (s : Finset (WitnessSelection.Candidate F ι)) (a : WitnessSelection.Coins F ι)
    (t : F × F) (hgood : a ∉ WitnessSelection.badCoins s)
    (truth : WitnessSelection.Candidate F ι → Polynomial F)
    (message : RoundPoly F) (claim : F)
    (hdegree : ∀ w ∈ s, (truth w).natDegree ≤ 2) :
    (univ.filter fun z => ∃ w ∈ s, WitnessSelection.fingerprint a w = t ∧
      BadRoundEvent (truth w) message claim z).card ≤ 2 := by
  apply WitnessSelection.selected_bad_card_le s a t hgood
    (fun w z => BadRoundEvent (truth w) message claim z) 2
  intro w hw _
  exact bad_round_roots (truth w) message claim (hdegree w hw)

end SumcheckV2
