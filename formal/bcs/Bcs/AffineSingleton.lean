import Bcs.AffineBlock

namespace Bcs.TotalOracle.Footprint
open Finset Merkle.RandomOracle
open scoped Classical

theorem singleton_oracle_sound
    {Q C Out : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    (domain : Finset Q) (point : Out → Q)
    (bad : Q → (Q → C) → Prop) (epsilon : ℚ) (hepsilon : 0 ≤ epsilon)
    (hlocal : ∀ x H, average (fun c =>
      if bad x (Function.update H x c) then (1 : ℚ) else 0) ≤ epsilon)
    (hsupport : ∀ x H, bad x H → x ∈ domain) :
    Bcs.AffineBlock.OracleSound domain (fun out H => bad (point out) H)
      (Bcs.AffineBlock.Rate.diagonal epsilon hepsilon) := by
  intro N tree
  apply Bcs.AffineBlock.of_footprints tree point domain (fun x => {x})
    (fun x H => if bad x H then 1 else 0)
    (fun x _ => if x ∈ domain then epsilon else 0)
  · intro x H; split_ifs <;> norm_num
  · intro x off; split_ifs <;> simp_all
  · intro x off
    by_cases hx : x ∈ domain
    · simp only [hx, if_true]
      let base := (split (C := C) {x}).symm (fun _ => Classical.choice inferInstance, off)
      let atX : Inside ({x} : Finset Q) := ⟨x, mem_singleton_self x⟩
      have he (on : Inside ({x} : Finset Q) → C) :
          (split {x}).symm (on, off) = Function.update base x (on atX) := by
        funext y
        by_cases hy : y = x
        · subst y
          simp [split, Equiv.piEquivPiSubtypeProd, atX]
        · simp [base, split, Equiv.piEquivPiSubtypeProd, hy]
      simp_rw [he]
      exact (average_eval atX (fun c =>
        if bad x (Function.update base x c) then (1 : ℚ) else 0)).trans_le (hlocal x base)
    · have hb (H : Q → C) : ¬ bad x H := fun h => hx (hsupport x H h)
      simp [hx, hb]
  · intro H q
    simp only [Finset.mem_singleton, Bcs.AffineBlock.Rate.diagonal]
    simp
  · intro H out
    simp only [Finset.mem_singleton, Bcs.AffineBlock.Rate.diagonal]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    split_ifs <;> simp_all
  · intro H hf
    exact ⟨point (tree.run H).1, mem_singleton_self _, by simp [hf]⟩

end Bcs.TotalOracle.Footprint
