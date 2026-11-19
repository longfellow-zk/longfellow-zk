import SumcheckV2.Layer

/-! Shared quadratic tensor algebra, independent of a circuit proof model. -/
namespace LfzkV2
open SumcheckV2 Classical

variable {F Wire : Type} [Field F] [Fintype Wire]

def quadratic (K : Wire → Wire → F) (w : Wire → F) : F :=
  ∑ l, ∑ r, K l r * w l * w r

theorem quadratic_eq_dot (K : Wire → Wire → F) (w : Wire → F) :
    quadratic K w = dot (bindRight K w) w := by
  simp only [quadratic, dot, bindRight, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem quadratic_add (K L : Wire → Wire → F) (w : Wire → F) :
    quadratic (fun l r => K l r + L l r) w = quadratic K w + quadratic L w := by
  simp [quadratic, add_mul, Finset.sum_add_distrib]

theorem quadratic_weighted_sum {ι : Type} [Fintype ι]
    (weights : ι → F) (K : ι → Wire → Wire → F) (w : Wire → F) :
    quadratic (fun l r => ∑ i, weights i * K i l r) w =
      dot weights (fun i => quadratic (K i) w) := by
  simp only [quadratic, dot, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ l, ∑ r, ∑ i, weights i * K i l r * w l * w r) =
        ∑ l, ∑ i, ∑ r, weights i * K i l r * w l * w r := by
          apply Finset.sum_congr rfl
          intro l _
          exact Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ r, weights i * K i l r * w l * w r := Finset.sum_comm
    _ = _ := by simp only [mul_assoc]

end LfzkV2
