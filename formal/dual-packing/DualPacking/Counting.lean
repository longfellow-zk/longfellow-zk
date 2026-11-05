import Mathlib

/-! # Exact finite counting for late independent linear batching -/

namespace DualPacking

open Finset
open scoped Classical

variable {F H : Type*} [Field F] [Fintype F] [Fintype H]
  [DecidableEq F] [DecidableEq H]

/-- A nonzero affine equation has at most one completion at a chosen pivot. -/
theorem affine_batch_card_le (v : H → F) (hv : ∃ k, v k ≠ 0) (c : F) :
    (univ.filter fun g : H → F => ∑ j, v j * g j = c).card ≤
      Fintype.card F ^ (Fintype.card H - 1) := by
  obtain ⟨k, hk⟩ := hv
  let S := {g : H → F // ∑ j, v j * g j = c}
  let restrict : S → ({j : H // j ≠ k} → F) := fun g j => g.1 j.1
  have hinj : Function.Injective restrict := by
    intro g h heq
    have hrest : ∀ j, j ≠ k → g.1 j = h.1 j := fun j hj =>
      congrFun heq ⟨j, hj⟩
    have hs : (∑ j ∈ univ.erase k, v j * g.1 j) =
        ∑ j ∈ univ.erase k, v j * h.1 j := by
      apply sum_congr rfl
      intro j hj
      rw [hrest j (mem_erase.mp hj).1]
    have hg := sum_erase_add univ (fun j => v j * g.1 j) (mem_univ k)
    have hh := sum_erase_add univ (fun j => v j * h.1 j) (mem_univ k)
    have hp : v k * g.1 k = v k * h.1 k := by
      rw [g.2] at hg
      rw [h.2, ← hs] at hh
      exact add_left_cancel (hg.trans hh.symm)
    apply Subtype.ext
    funext j
    by_cases hj : j = k
    · subst j
      exact mul_left_cancel₀ hk hp
    · exact hrest j hj
  have hc := Fintype.card_le_of_injective restrict hinj
  have hindex : Fintype.card {j : H // j ≠ k} = Fintype.card H - 1 := by
    simp
  simpa [S, Fintype.card_subtype, Fintype.card_fun, hindex] using hc

end DualPacking
