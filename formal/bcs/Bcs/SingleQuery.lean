import Bcs.FinalQuery
import Bcs.PotentialOracle
import Mathlib.Tactic.FieldSimp

/-! A single verifier lookup after adaptive oracle search, with rational
per-answer budgets and an off-coordinate context. -/

namespace Bcs.TotalOracle
open Finset Merkle.RandomOracle
open scoped Classical

variable {Q C Out : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]

theorem tree_final_event_ratio_le {N : ℕ} (tree : Tree Q C Out N) (point : Out → Q)
    (localEvent : Q → (Q → C) → C → Prop)
    (hoff : ∀ x H H', AgreeOff x H H' → ∀ c, localEvent x H c ↔ localEvent x H' c)
    (epsilon : ℚ) (hepsilon : 0 ≤ epsilon)
    (hlocal : ∀ x H, (∑ c : C, if localEvent x H c then (1 : ℚ) else 0) ≤
      Fintype.card C*epsilon)
    (event : (Q → C) → Prop)
    (hfinal : ∀ H, event H → localEvent (point (tree.run H).1) H (H (point (tree.run H).1))) :
    ((univ.filter event).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card Q ≤
      (N+1 : ℕ)*epsilon := by
  let extended := appendFinalQuery tree point
  let charged := fun x H => x ∈ queried extended H
  letI (H : Q → C) (x : Q) : Decidable (charged x H) := Classical.propDecidable _
  let weight := fun x H c => if localEvent x H c then (1 : ℚ) else 0
  have hcount H : (univ.filter fun x => charged x H).card ≤ N+1 := by
    have he : (univ.filter fun x => charged x H) = (queried extended H).toFinset := by
      ext x
      simp [charged]
    rw [he]
    exact (List.toFinset_card_le _).trans ((queried_length_le extended H).trans_eq (by omega))
  have hp H (hH : event H) :
      1 ≤ ∑ x : Q, if charged x H then weight x H (H x) else 0 := by
    have hx : charged (point (tree.run H).1) H := appendFinalQuery_mem tree point H
    have he := hfinal H hH
    have h := single_le_sum (f := fun x => if charged x H then weight x H (H x) else 0)
      (fun _ _ => by dsimp [weight]; split_ifs <;> norm_num) (mem_univ (point (tree.run H).1))
    simpa only [hx, weight, if_pos he, if_true] using h
  have hbound := potential_event_ratio_le event charged
    (fun x H H' h => mem_queried_iff extended x h) weight
    (by intro x H H' h c; simp only [weight, propext (hoff x H H' h c)])
    (N+1) (Fintype.card C*epsilon) (mul_nonneg (Nat.cast_nonneg _) hepsilon) hcount hlocal
    (by intro x H c; dsimp [weight]; split_ifs <;> norm_num) hp
  have hc : (Fintype.card C : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := C)
  exact hbound.trans_eq (by field_simp)

end Bcs.TotalOracle
