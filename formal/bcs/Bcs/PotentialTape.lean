import Bcs.PotentialOracle
import Bcs.RoundByRound

/-!
# Sequential-tape counting for rational positive-increase charges

This is the IOP counterpart of the prefix-only random-oracle compiler.
Every slot's charge may depend on all preceding answers, and local bounds
may vary by role.  The pathwise extraction-failure telescope is a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace Bcs.PotentialTape

open Finset Bcs.TotalOracle
open scoped Classical

theorem ratio_le
    {C : Type} [Fintype C] [Nonempty C] {T : ℕ}
    (E : (Fin T → C) → Prop) [DecidablePred E]
    (charge : (i : Fin T) → (Fin i.val → C) → C → ℚ)
    (budget : Fin T → ℚ)
    (hnonneg : ∀ i pref c, 0 ≤ charge i pref c)
    (hlocal : ∀ i pref, ∑ c : C, charge i pref c ≤ budget i)
    (hpath : ∀ tape, E tape →
      1 ≤ ∑ i : Fin T,
        charge i (Sumcheck.extract_prefix tape i) (tape i)) :
    ((univ.filter E).card : ℚ) /
      (Fintype.card C : ℚ) ^ T ≤
      (∑ i : Fin T, budget i) / Fintype.card C := by
  classical
  let wt (i : Fin T) (tape : Fin T → C) (c : C) : ℚ :=
    charge i (Sumcheck.extract_prefix tape i) c
  have hoff : ∀ (i : Fin T) (H H' : Fin T → C),
      Bcs.TotalOracle.AgreeOff (ι := Fin T) (C := C) i H H' →
      ∀ c, wt i H c = wt i H' c := by
    intro i H H' h c
    simp only [wt]
    congr 1
    funext j
    have hne : (⟨j.val, lt_trans j.isLt i.isLt⟩ : Fin T) ≠ i := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only at hv
      omega
    exact h _ hne
  simpa only [Fintype.card_fin] using
    (potential_event_ratio_le_budget E (fun _ _ => True)
    (by intros; simp) wt hoff budget (∑ i : Fin T, budget i)
    (fun i H => hlocal i (Sumcheck.extract_prefix H i))
    (by intro H; simp) (fun i H c => hnonneg i (Sumcheck.extract_prefix H i) c)
    (fun H hE => by simpa only [ite_true, wt] using hpath H hE))

end Bcs.PotentialTape
