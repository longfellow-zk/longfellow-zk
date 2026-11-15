import Bcs.Counting
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Field

/-! Uniform finite-event densities, transport, conditioning and union bounds. -/
namespace Bcs.FiniteProbability
open Finset
open scoped Classical BigOperators

noncomputable def density {Omega : Type*} [Fintype Omega] (event : Omega → Prop) : ℚ :=
  ((univ.filter event).card : ℚ) / Fintype.card Omega

theorem density_congr {Omega : Type*} [Fintype Omega] {p q : Omega → Prop}
    (h : ∀ x, p x ↔ q x) : density p = density q := by
  unfold density
  rw [show univ.filter p = univ.filter q by exact filter_congr fun x _ => h x]

theorem density_equiv {Omega Other : Type*} [Fintype Omega] [Fintype Other]
    (eqv : Omega ≃ Other) (event : Other → Prop) :
    density (fun x => event (eqv x)) = density event := by
  classical
  unfold density
  rw [Fintype.card_congr eqv]
  congr 2
  apply Finset.card_bij (fun x _ => eqv x)
  · intro x hx; simpa only [mem_filter, mem_univ, true_and] using hx
  · intro x _ y _ h; exact eqv.injective h
  · intro y hy; refine ⟨eqv.symm y, ?_, eqv.apply_symm_apply y⟩
    simpa only [mem_filter, mem_univ, true_and, eqv.apply_symm_apply] using hy

theorem density_mono {Omega : Type*} [Fintype Omega] {p q : Omega → Prop}
    (h : ∀ x, p x → q x) : density p ≤ density q := by
  classical
  unfold density
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_le_card (show univ.filter p ⊆ univ.filter q from
    fun x hx => mem_filter.mpr ⟨mem_univ _,h x (mem_filter.mp hx).2⟩)

theorem density_not {Omega : Type*} [Fintype Omega] [Nonempty Omega] (p : Omega → Prop) :
    density (fun x => ¬p x) = 1-density p := by
  classical
  have hc : (univ.filter p).card+(univ.filter fun x : Omega => ¬p x).card = Fintype.card Omega := by
    convert card_filter_add_card_filter_not (s := (univ : Finset Omega)) p using 1
    simp
  have hq : (Fintype.card Omega : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold density
  rw [eq_sub_iff_add_eq]
  rw [← add_div,← Nat.cast_add,Nat.add_comm]
  convert div_self hq using 1
  congr 1
  norm_cast
  convert hc using 1
  congr 2
  ext x
  simp

theorem density_product_average {Data Pair : Type*} [Fintype Data] [Fintype Pair]
    [Nonempty Data] [Nonempty Pair] (event : Data → Pair → Prop) :
    density (fun x : Data × Pair => event x.1 x.2) =
      (∑ data, density (event data))/Fintype.card Data := by
  classical
  unfold density
  rw [Bcs.card_filter_prod_fst,Fintype.card_prod]
  push_cast
  rw [← sum_div]
  field_simp

theorem density_product_snd {Data Pair : Type*} [Fintype Data] [Fintype Pair]
    [Nonempty Data] (event : Pair → Prop) :
    density (fun x : Data × Pair => event x.2) = density event := by
  classical
  unfold density
  rw [show univ.filter (fun x : Data × Pair => event x.2) =
    (univ : Finset Data) ×ˢ (univ.filter event) by ext x; simp]
  simp only [card_product,card_univ,Fintype.card_prod,Nat.cast_mul]
  have hq : (Fintype.card Data : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem density_le_of_ratio_le {Omega : Type*} [Fintype Omega]
    (event : Omega → Prop) [DecidablePred event] (epsilon : ℚ)
    (h : ((univ.filter event).card : ℚ) / Fintype.card Omega ≤ epsilon) :
    density event ≤ epsilon := by
  classical
  refine le_trans ?_ h
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro x hx
  simpa only [mem_filter, mem_univ, true_and] using hx

theorem density_union_le {Index Omega : Type*} [Fintype Index] [Fintype Omega]
    (event : Omega → Prop) (piece : Index → Omega → Prop)
    (hcover : ∀ x, event x → ∃ i, piece i x) :
    density event ≤ ∑ i, density (piece i) := by
  classical
  have hsub : univ.filter event ⊆ univ.biUnion (fun i => univ.filter (piece i)) := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x (mem_filter.mp hx).2
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  have hc := (card_le_card hsub).trans card_biUnion_le
  unfold density
  simp only [div_eq_mul_inv, ← sum_mul]
  rw [← Nat.cast_sum]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact_mod_cast hc

theorem density_product_gate {Data Pair : Type*} [Fintype Data] [Fintype Pair]
    [Nonempty Pair] (gate : Data → Prop) :
    density (fun x : Data × Pair => gate x.1) = density gate := by
  classical
  unfold density
  rw [show univ.filter (fun x : Data × Pair => gate x.1) =
    (univ.filter gate) ×ˢ (univ : Finset Pair) by ext x; simp]
  simp only [card_product, card_univ, Fintype.card_prod, Nat.cast_mul]
  have hp : (Fintype.card Pair : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end Bcs.FiniteProbability
