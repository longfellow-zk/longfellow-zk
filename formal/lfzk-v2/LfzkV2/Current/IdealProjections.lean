import LfzkV2.Current.BalancedDecoder
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Fin.Basic

/-! Exact finite ideal challenge projections. These factor a symbolic
uniform answer into the coordinates read by a role and independent unused
coordinates. They do not assert exact balance for a bounded byte seed. -/
noncomputable section
namespace LfzkV2.Current.IdealProjections
open Finset
open scoped Classical

variable {Raw Sample Unused : Type} [Fintype Raw] [Fintype Sample] [Fintype Unused]

/-- A product factorization constructs the balanced fibers; no sampler
correctness or event-probability certificate is supplied by the caller. -/
def decoder (e : Raw ≃ Sample × Unused) : BalancedDecoder Raw Sample where
  decode raw := (e raw).1
  fiber := Fintype.card Unused
  fiber_bound sample := by
    have hc := Finset.card_equiv e
      (s := univ.filter fun raw => (e raw).1 = sample)
      (t := ({sample} : Finset Sample).product univ) (by
        intro raw
        simp only [mem_filter,mem_univ,true_and]
        constructor
        · intro h
          exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr h,Finset.mem_univ _⟩
        · intro h
          exact Finset.mem_singleton.mp (Finset.mem_product.mp h).1)
    exact hc.trans_le (by simp)
  balanced := by
    rw [Fintype.card_congr e,Fintype.card_prod]
    exact Nat.mul_comm _ _

def compose {Middle : Type} [Fintype Middle]
    (first : BalancedDecoder Raw Middle) (second : BalancedDecoder Middle Sample) :
    BalancedDecoder Raw Sample where
  decode raw := second.decode (first.decode raw)
  fiber := first.fiber*second.fiber
  fiber_bound sample := Bcs.card_decode_le first.decode first.fiber first.fiber_bound
    (fun middle => second.decode middle = sample) second.fiber (second.fiber_bound sample)
  balanced := by
    calc
      (first.fiber*second.fiber)*Fintype.card Sample =
          first.fiber*(second.fiber*Fintype.card Sample) := Nat.mul_assoc _ _ _
      _ = Fintype.card Raw := by rw [second.balanced,first.balanced]

/-- The first vector coordinates are a direct product factor, without
changing their order or introducing extra challenge draws. -/
def vectorPrefix {F : Type} (count remaining : ℕ) :
    (Fin (count+remaining) → F) ≃ (Fin count → F) × (Fin remaining → F) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl F)).trans
    (Equiv.sumArrowEquivProdArrow (Fin count) (Fin remaining) F)

theorem vectorPrefix_apply {F : Type} (count remaining : ℕ)
    (values : Fin (count+remaining) → F) (i : Fin count) :
    (vectorPrefix count remaining values).1 i = values (i.castAdd remaining) := rfl

/-- Consecutive coordinates factor even when a local assertion test reads
only the middle of the larger shared answer vector. -/
def slice {F : Type} (before count after : ℕ) :
    (Fin (before+(count+after)) → F) ≃
      (Fin count → F) × ((Fin before → F) × (Fin after → F)) :=
  (vectorPrefix before (count+after)).trans
    ((Equiv.prodCongr (Equiv.refl (Fin before → F)) (vectorPrefix count after)).trans
      ((Equiv.prodAssoc _ _ _).symm.trans
        ((Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.refl (Fin after → F))).trans
          (Equiv.prodAssoc _ _ _))))

theorem slice_apply {F : Type} (before count after : ℕ)
    (values : Fin (before+(count+after)) → F) (i : Fin count) :
    (slice before count after values).1 i = values ⟨before+i.val,by have := i.isLt; omega⟩ := rfl

def boundedSlice {F : Type} (capacity before count : ℕ) (fits : before+count ≤ capacity) :
    (Fin capacity → F) ≃
      (Fin count → F) × ((Fin before → F) × (Fin (capacity-(before+count)) → F)) :=
  (Equiv.arrowCongr (finCongr (by omega : capacity = before+(count+(capacity-(before+count)))))
    (Equiv.refl F)).trans (slice before count (capacity-(before+count)))

theorem boundedSlice_apply {F : Type} (capacity before count : ℕ) (fits : before+count ≤ capacity)
    (values : Fin capacity → F) (i : Fin count) :
    (boundedSlice capacity before count fits values).1 i =
      values ⟨before+i.val,by have := i.isLt; omega⟩ := rfl

end LfzkV2.Current.IdealProjections
