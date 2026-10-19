import Bcs.FootprintCharging

/-! A selected output may identify one bad hash input. A bound after
resampling that input, uniformly over every complementary oracle, gives
the usual `N+1` bound without restricting query order. -/

namespace Bcs.TotalOracle.Footprint

open Finset Merkle.RandomOracle
open scoped Classical

theorem selected_singleton_event_le
    {Q C Out : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    {N : ℕ} (tree : Tree Q C Out N) (point : Out → Q)
    (bad : Q → (Q → C) → Prop) (epsilon : ℚ) (hepsilon : 0 ≤ epsilon)
    (hlocal : ∀ x H, average (fun c =>
      if bad x (Function.update H x c) then (1 : ℚ) else 0) ≤ epsilon) :
    Bcs.FiniteProbability.density (fun H => bad (point (tree.run H).1) H) ≤
      (N + 1) * epsilon := by
  have h : Bcs.FiniteProbability.density (fun H => bad (point (tree.run H).1) H) ≤
      epsilon + N * epsilon := by
    apply selected_event_le tree point (fun x => {x})
      (fun x H => if bad x H then 1 else 0) (fun _ _ => epsilon) _ epsilon epsilon
    · intro x H; split_ifs <;> norm_num
    · intros; exact hepsilon
    · exact hepsilon
    · intro x off
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
    · intro H q; simp
    · intro H out; simp
    · intro H hf
      exact ⟨point (tree.run H).1, mem_singleton_self _, by simp [hf]⟩
  convert h using 1
  ring

end Bcs.TotalOracle.Footprint
