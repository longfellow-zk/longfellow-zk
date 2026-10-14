import CodingTheory.ListDecoding.UniformFamily
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Floor
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Delsarte's linear-programming bound using Hahn kernels

This development proves the Delsarte LP bound for uniform intersection
families in the Johnson scheme. Hahn names the polynomial family used by the
kernels; the packing method and bound are due to Philippe Delsarte.

Reference: P. Delsarte, *An algebraic approach to the association schemes of
coding theory*, Philips Research Reports Supplements, No. 10 (1973).
[Publication record](https://hdl.handle.net/2078.5/58922).

Let `𝒜` be a family of `w`-subsets of `Fin n` whose distinct members meet in
at most `lam` points.  For a degree `k`, weight every `k`-subset `S` by the
harmonic zonal function

  `ψₖ(|S ∩ A|)`,  where `ψₖ(x) = (-1)^x C(n - w - k + x, x) / C(w, x)`.

Counting `k`-subsets by their intersections with the four cells
`A ∩ B`, `A \ B`, `B \ A` and the rest gives

  `∑_{|S| = k} ψₖ(|S ∩ A|) ψₖ(|S ∩ B|) = Hₖ(|A ∩ B|)`,

for an explicit polynomial `Hₖ` (`hahnKernel`).  Consequently
`∑_{A, B ∈ 𝒜} Hₖ(|A ∩ B|)` is a sum of squares (`hahnKernel_gram_nonneg`).
The proofs use this explicit Gram representation directly. Degree one is
exactly the Johnson kernel
`n (n t - w²) / w²` (`hahnKernel_one`).

Delsarte's linear-programming argument (`card_le_of_delsarte`) turns every
nonnegative combination `f₀ + ∑ₖ fₖ Hₖ` that is nonpositive on all admissible
intersection sizes of distinct members into the cardinality bound
`|𝒜| ≤ (f₀ + ∑ₖ fₖ Hₖ(w)) / f₀`.  The decidable integer form
(`certificateValid`, `certifiedBound`) is what concrete certificates check.
-/

namespace CodingTheory.HahnDelsarte

open Finset
open scoped BigOperators

section Split

variable {α β : Type*} [DecidableEq α] [AddCommMonoid β]

/-- `k`-subsets of a disjoint union, sorted by the size of their left part. -/
theorem sum_powersetCard_union {U V : Finset α} (hUV : Disjoint U V) (k : ℕ)
    (f : Finset α → β) :
    ∑ S ∈ (U ∪ V).powersetCard k, f S =
      ∑ i ∈ range (k + 1), ∑ X ∈ U.powersetCard i,
        ∑ Y ∈ V.powersetCard (k - i), f (X ∪ Y) := by
  have hmaps : ∀ S ∈ (U ∪ V).powersetCard k, (S ∩ U).card ∈ range (k + 1) := by
    intro S hS
    have hcard := (mem_powersetCard.mp hS).2
    have hle := card_le_card (inter_subset_left : S ∩ U ⊆ S)
    exact mem_range.mpr (by omega)
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro i hi
  rw [← sum_product']
  apply sum_nbij' (fun S ↦ (S ∩ U, S ∩ V)) (fun p ↦ p.1 ∪ p.2)
  · intro S hS
    obtain ⟨⟨hSsub, hScard⟩, hSi⟩ := by simpa only [mem_filter, mem_powersetCard] using hS
    have hdisj : Disjoint (S ∩ U) (S ∩ V) :=
      hUV.mono inter_subset_right inter_subset_right
    have hsplit : S ∩ U ∪ S ∩ V = S := by
      rw [← inter_union_distrib_left, inter_eq_left.mpr hSsub]
    have hcard : (S ∩ U).card + (S ∩ V).card = k := by
      rw [← card_union_of_disjoint hdisj, hsplit, hScard]
    simp only [mem_product, mem_powersetCard]
    exact ⟨⟨inter_subset_right, hSi⟩, inter_subset_right, by omega⟩
  · intro p hp
    obtain ⟨⟨hX, hXcard⟩, hY, hYcard⟩ := by simpa only [mem_product, mem_powersetCard] using hp
    have hik : i < k + 1 := mem_range.mp hi
    have hYU : p.2 ∩ U = ∅ := disjoint_iff_inter_eq_empty.mp (hUV.symm.mono_left hY)
    simp only [mem_filter, mem_powersetCard]
    refine ⟨⟨union_subset_union hX hY, ?_⟩, ?_⟩
    · rw [card_union_of_disjoint (hUV.mono hX hY), hXcard, hYcard]
      omega
    · rw [union_inter_distrib_right, inter_eq_left.mpr hX, hYU, union_empty, hXcard]
  · intro S hS
    obtain ⟨⟨hSsub, -⟩, -⟩ := by simpa only [mem_filter, mem_powersetCard] using hS
    change S ∩ U ∪ S ∩ V = S
    rw [← inter_union_distrib_left, inter_eq_left.mpr hSsub]
  · intro p hp
    obtain ⟨⟨hX, -⟩, hY, -⟩ := by simpa only [mem_product, mem_powersetCard] using hp
    have hYU : p.2 ∩ U = ∅ := disjoint_iff_inter_eq_empty.mp (hUV.symm.mono_left hY)
    have hXV : p.1 ∩ V = ∅ := disjoint_iff_inter_eq_empty.mp (hUV.mono_left hX)
    refine Prod.ext ?_ ?_
    · change (p.1 ∪ p.2) ∩ U = p.1
      rw [union_inter_distrib_right, inter_eq_left.mpr hX, hYU, union_empty]
    · change (p.1 ∪ p.2) ∩ V = p.2
      rw [union_inter_distrib_right, inter_eq_left.mpr hY, hXV, empty_union]
  · intro S hS
    obtain ⟨⟨hSsub, -⟩, -⟩ := by simpa only [mem_filter, mem_powersetCard] using hS
    change f S = f (S ∩ U ∪ S ∩ V)
    rw [← inter_union_distrib_left, inter_eq_left.mpr hSsub]

/-- Sums over `m`-subsets of `W` that depend only on the intersection with
`B`: two-cell count. -/
theorem sum_powersetCard_card_inter (W B : Finset α) (m : ℕ) (h : ℕ → β) :
    ∑ Y ∈ W.powersetCard m, h (Y ∩ B).card =
      ∑ c ∈ range (m + 1),
        ((W ∩ B).card.choose c * (W \ B).card.choose (m - c)) • h c := by
  have hW : W ∩ B ∪ W \ B = W := by
    rw [union_comm]
    exact sdiff_union_inter W B
  have hdisj : Disjoint (W ∩ B) (W \ B) := (disjoint_sdiff_inter W B).symm
  conv_lhs => rw [← hW]
  rw [sum_powersetCard_union hdisj]
  apply sum_congr rfl
  intro c _hc
  have hconst : ∀ X ∈ (W ∩ B).powersetCard c,
      ∑ Y ∈ (W \ B).powersetCard (m - c), h ((X ∪ Y) ∩ B).card =
        ∑ _Y ∈ (W \ B).powersetCard (m - c), h c := by
    intro X hX
    apply sum_congr rfl
    intro Y hY
    obtain ⟨hXsub, hXcard⟩ := mem_powersetCard.mp hX
    obtain ⟨hYsub, -⟩ := mem_powersetCard.mp hY
    have hXB : X ∩ B = X := inter_eq_left.mpr (hXsub.trans inter_subset_right)
    have hYB : Y ∩ B = ∅ :=
      disjoint_iff_inter_eq_empty.mp (sdiff_disjoint.mono_left hYsub)
    rw [union_inter_distrib_right, hXB, hYB, union_empty, hXcard]
  rw [sum_congr rfl hconst]
  simp only [sum_const, card_powersetCard, smul_smul]

/-- Sums over `k`-subsets of the whole universe that depend only on their
intersections with `A` and `B`: four-cell count. -/
theorem sum_powersetCard_univ_card_inter {n : ℕ} (A B : Finset (Fin n)) (k : ℕ)
    (φ : ℕ → ℕ → β) :
    ∑ S ∈ (univ : Finset (Fin n)).powersetCard k, φ (S ∩ A).card (S ∩ B).card =
      ∑ i ∈ range (k + 1), ∑ a ∈ range (i + 1),
        ((A ∩ B).card.choose a * (A \ B).card.choose (i - a)) •
          ∑ c ∈ range (k - i + 1),
            ((Aᶜ ∩ B).card.choose c * (Aᶜ \ B).card.choose (k - i - c)) •
              φ i (a + c) := by
  rw [← union_compl A, sum_powersetCard_union disjoint_compl_right]
  apply sum_congr rfl
  intro i _hi
  have hkey : ∀ X ∈ A.powersetCard i, ∀ Y ∈ Aᶜ.powersetCard (k - i),
      φ ((X ∪ Y) ∩ A).card ((X ∪ Y) ∩ B).card =
        φ i ((X ∩ B).card + (Y ∩ B).card) := by
    intro X hX Y hY
    obtain ⟨hXsub, hXcard⟩ := mem_powersetCard.mp hX
    obtain ⟨hYsub, -⟩ := mem_powersetCard.mp hY
    have hYA : Y ∩ A = ∅ :=
      disjoint_iff_inter_eq_empty.mp (disjoint_compl_right.symm.mono_left hYsub)
    have hXA : (X ∪ Y) ∩ A = X := by
      rw [union_inter_distrib_right, inter_eq_left.mpr hXsub, hYA, union_empty]
    have hXYB : ((X ∪ Y) ∩ B).card = (X ∩ B).card + (Y ∩ B).card := by
      rw [union_inter_distrib_right, card_union_of_disjoint]
      exact (disjoint_compl_right.mono hXsub hYsub).mono inter_subset_left inter_subset_left
    rw [hXA, hXcard, hXYB]
  rw [sum_congr rfl fun X hX ↦ sum_congr rfl (hkey X hX)]
  have hinner : ∀ X ∈ A.powersetCard i,
      ∑ Y ∈ Aᶜ.powersetCard (k - i), φ i ((X ∩ B).card + (Y ∩ B).card) =
        ∑ c ∈ range (k - i + 1),
          ((Aᶜ ∩ B).card.choose c * (Aᶜ \ B).card.choose (k - i - c)) •
            φ i ((X ∩ B).card + c) := fun X _ ↦
    sum_powersetCard_card_inter Aᶜ B (k - i) (fun c ↦ φ i ((X ∩ B).card + c))
  rw [sum_congr rfl hinner]
  exact sum_powersetCard_card_inter A B i (fun a ↦ ∑ c ∈ range (k - i + 1),
    ((Aᶜ ∩ B).card.choose c * (Aᶜ \ B).card.choose (k - i - c)) • φ i (a + c))

end Split

/-! ### Hahn kernels -/

/-- Harmonic zonal weight of a `k`-subset meeting a `w`-set in `x` points. -/
def hahnWeight (n w k x : ℕ) : ℚ :=
  (-1) ^ x * (((n + x) - (w + k)).choose x : ℚ) / (w.choose x : ℚ)

/-- Degree-`k` Hahn kernel at intersection size `t`: the four-cell count of
`∑_{|S| = k} ψₖ(|S ∩ A|) ψₖ(|S ∩ B|)` for `w`-sets with `|A ∩ B| = t`. -/
def hahnKernel (n w k t : ℕ) : ℚ :=
  ∑ i ∈ range (k + 1), hahnWeight n w k i *
    ∑ a ∈ range (i + 1), ((t.choose a * (w - t).choose (i - a) : ℕ) : ℚ) *
      ∑ c ∈ range (k - i + 1),
        (((w - t).choose c * (n + t - 2 * w).choose (k - i - c) : ℕ) : ℚ) *
          hahnWeight n w k (a + c)

variable {n w : ℕ}

/-- **Degree one is Johnson.**  The first Hahn kernel is the Johnson kernel
`n (n t - w²) / w²`, so degree-one certificates reproduce the Johnson count. -/
theorem hahnKernel_one {t : ℕ} (hw : 0 < w) (hwn : w ≤ n) (ht : t ≤ w)
    (htn : 2 * w ≤ n + t) :
    hahnKernel n w 1 t = (n : ℚ) * (n * t - w ^ 2) / w ^ 2 := by
  have hw' : (w : ℚ) ≠ 0 := by exact_mod_cast hw.ne'
  simp only [hahnKernel, hahnWeight, sum_range_succ, sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one, Nat.sub_zero, Nat.sub_self,
    Nat.cast_one, one_mul, mul_one, Nat.add_zero, Nat.cast_mul]
  rw [show n + 1 - (w + 1) = n - w by omega]
  rw [Nat.cast_sub ht, Nat.cast_sub hwn, Nat.cast_sub htn]
  push_cast
  field_simp
  ring

/-- The harmonic weights realize the Hahn kernel as a Gram matrix. -/
theorem sum_hahnWeight_mul_hahnWeight (A B : Finset (Fin n))
    (hA : A.card = w) (hB : B.card = w) (k : ℕ) :
    ∑ S ∈ (univ : Finset (Fin n)).powersetCard k,
        hahnWeight n w k (S ∩ A).card * hahnWeight n w k (S ∩ B).card =
      hahnKernel n w k (A ∩ B).card := by
  rw [sum_powersetCard_univ_card_inter A B k
    (fun x y ↦ hahnWeight n w k x * hahnWeight n w k y)]
  have hAB : (A \ B).card = w - (A ∩ B).card := by
    rw [card_sdiff, hA, inter_comm]
  have hBA : (Aᶜ ∩ B).card = w - (A ∩ B).card := by
    have hset : Aᶜ ∩ B = B \ A := by
      ext x
      simp only [mem_inter, mem_compl, mem_sdiff]
      tauto
    rw [hset, card_sdiff, hB]
  have hrest : (Aᶜ \ B).card = n + (A ∩ B).card - 2 * w := by
    have hset : Aᶜ \ B = (A ∪ B)ᶜ := by
      ext x
      simp only [mem_sdiff, mem_compl, mem_union]
      tauto
    have hunion := card_union_add_card_inter A B
    have hle : (A ∪ B).card ≤ n := by
      simpa using card_le_univ (A ∪ B)
    rw [hset, card_compl, Fintype.card_fin]
    omega
  rw [hAB, hBA, hrest]
  unfold hahnKernel
  simp only [nsmul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro c _
  ring

/-- **Delsarte positivity.**  For a `w`-uniform family, the Gram sum of every
Hahn kernel is a sum of squares. -/
theorem hahnKernel_gram_nonneg (family : Finset (Finset (Fin n)))
    (huniform : ∀ A ∈ family, A.card = w) (k : ℕ) :
    0 ≤ ∑ A ∈ family, ∑ B ∈ family, hahnKernel n w k (A ∩ B).card := by
  have hrewrite : ∑ A ∈ family, ∑ B ∈ family, hahnKernel n w k (A ∩ B).card =
      ∑ S ∈ (univ : Finset (Fin n)).powersetCard k,
        (∑ A ∈ family, hahnWeight n w k (S ∩ A).card) *
          ∑ B ∈ family, hahnWeight n w k (S ∩ B).card := by
    calc
      ∑ A ∈ family, ∑ B ∈ family, hahnKernel n w k (A ∩ B).card =
          ∑ A ∈ family, ∑ B ∈ family, ∑ S ∈ (univ : Finset (Fin n)).powersetCard k,
            hahnWeight n w k (S ∩ A).card * hahnWeight n w k (S ∩ B).card := by
        apply sum_congr rfl
        intro A hA
        apply sum_congr rfl
        intro B hB
        rw [sum_hahnWeight_mul_hahnWeight A B (huniform A hA) (huniform B hB)]
      _ = ∑ A ∈ family, ∑ S ∈ (univ : Finset (Fin n)).powersetCard k, ∑ B ∈ family,
            hahnWeight n w k (S ∩ A).card * hahnWeight n w k (S ∩ B).card := by
        apply sum_congr rfl
        intro A _
        exact sum_comm
      _ = ∑ S ∈ (univ : Finset (Fin n)).powersetCard k, ∑ A ∈ family, ∑ B ∈ family,
            hahnWeight n w k (S ∩ A).card * hahnWeight n w k (S ∩ B).card := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro S _
        rw [sum_mul_sum]
  rw [hrewrite]
  exact sum_nonneg fun S _ ↦ mul_self_nonneg _

/-! ### Delsarte linear-programming bound -/

/-- **Delsarte bound, quadratic form.** If `f₀ + ∑_{k=1}^{K} fₖ Hₖ(t)` has nonnegative
`fₖ` and is nonpositive at every intersection size `t ≤ lam` realizable by two
`w`-subsets of `Fin n`, then `|𝒜|² f₀ ≤ |𝒜| (f₀ + ∑ₖ fₖ Hₖ(w))`. -/
theorem card_sq_mul_le_of_delsarte {lam K : ℕ} (family : Finset (Finset (Fin n)))
    (huniform : ∀ A ∈ family, A.card = w)
    (hinter : ∀ A ∈ family, ∀ B ∈ family, A ≠ B → (A ∩ B).card ≤ lam)
    (f₀ : ℚ) (f : ℕ → ℚ) (hf : ∀ k ∈ Icc 1 K, 0 ≤ f k)
    (hneg : ∀ t, 2 * w ≤ n + t → t ≤ lam →
      f₀ + ∑ k ∈ Icc 1 K, f k * hahnKernel n w k t ≤ 0) :
    (family.card : ℚ) ^ 2 * f₀ ≤
      family.card * (f₀ + ∑ k ∈ Icc 1 K, f k * hahnKernel n w k w) := by
  let P : ℕ → ℚ := fun t ↦ f₀ + ∑ k ∈ Icc 1 K, f k * hahnKernel n w k t
  have hswap : ∑ A ∈ family, ∑ B ∈ family, ∑ k ∈ Icc 1 K, f k * hahnKernel n w k (A ∩ B).card =
      ∑ k ∈ Icc 1 K, f k *
        ∑ A ∈ family, ∑ B ∈ family, hahnKernel n w k (A ∩ B).card := by
    calc
      ∑ A ∈ family, ∑ B ∈ family, ∑ k ∈ Icc 1 K, f k * hahnKernel n w k (A ∩ B).card =
          ∑ A ∈ family, ∑ k ∈ Icc 1 K, ∑ B ∈ family,
            f k * hahnKernel n w k (A ∩ B).card :=
        sum_congr rfl fun _ _ ↦ sum_comm
      _ = ∑ k ∈ Icc 1 K, ∑ A ∈ family, ∑ B ∈ family,
            f k * hahnKernel n w k (A ∩ B).card := sum_comm
      _ = _ := by simp_rw [mul_sum]
  have hexpand : ∑ A ∈ family, ∑ B ∈ family, P (A ∩ B).card =
      (family.card : ℚ) ^ 2 * f₀ +
        ∑ k ∈ Icc 1 K, f k *
          ∑ A ∈ family, ∑ B ∈ family, hahnKernel n w k (A ∩ B).card := by
    simp only [P, sum_add_distrib, sum_const, nsmul_eq_mul]
    rw [hswap]
    ring
  have hlow : (family.card : ℚ) ^ 2 * f₀ ≤
      ∑ A ∈ family, ∑ B ∈ family, P (A ∩ B).card := by
    rw [hexpand]
    have hnonneg : 0 ≤ ∑ k ∈ Icc 1 K, f k *
        ∑ A ∈ family, ∑ B ∈ family, hahnKernel n w k (A ∩ B).card :=
      sum_nonneg fun k hk ↦ mul_nonneg (hf k hk) (hahnKernel_gram_nonneg family huniform k)
    linarith
  have hup : ∑ A ∈ family, ∑ B ∈ family, P (A ∩ B).card ≤ family.card * P w := by
    calc
      ∑ A ∈ family, ∑ B ∈ family, P (A ∩ B).card ≤ ∑ _A ∈ family, P w := by
        apply sum_le_sum
        intro A hA
        rw [← add_sum_erase family _ hA, inter_self, huniform A hA]
        have hoff : ∑ B ∈ family.erase A, P (A ∩ B).card ≤ 0 := by
          apply sum_nonpos
          intro B hB
          have hBA : B ≠ A := ne_of_mem_erase hB
          have hBmem : B ∈ family := mem_of_mem_erase hB
          apply hneg
          · have hunion := card_union_add_card_inter A B
            have hle : (A ∪ B).card ≤ n := by
              simpa using card_le_univ (A ∪ B)
            rw [huniform A hA, huniform B hBmem] at hunion
            omega
          · exact hinter A hA B hBmem (Ne.symm hBA)
        linarith
      _ = family.card * P w := by rw [sum_const, nsmul_eq_mul]
  exact hlow.trans hup

/-- **Delsarte bound.** The Hahn-kernel certificate bounds the family size by any
`L` with `f₀ + ∑ₖ fₖ Hₖ(w) < (L + 1) f₀`. -/
theorem card_le_of_delsarte {lam K : ℕ} (family : Finset (Finset (Fin n)))
    (huniform : ∀ A ∈ family, A.card = w)
    (hinter : ∀ A ∈ family, ∀ B ∈ family, A ≠ B → (A ∩ B).card ≤ lam)
    (f₀ : ℚ) (f : ℕ → ℚ) (hf : ∀ k ∈ Icc 1 K, 0 ≤ f k)
    (hneg : ∀ t, 2 * w ≤ n + t → t ≤ lam →
      f₀ + ∑ k ∈ Icc 1 K, f k * hahnKernel n w k t ≤ 0)
    (L : ℕ) (hf₀ : 0 < f₀)
    (hL : f₀ + ∑ k ∈ Icc 1 K, f k * hahnKernel n w k w < (L + 1) * f₀) :
    family.card ≤ L := by
  have h := card_sq_mul_le_of_delsarte family huniform hinter f₀ f hf hneg
  by_contra hcon
  have hc : (L : ℚ) + 1 ≤ family.card := by exact_mod_cast Nat.lt_of_not_le hcon
  have hcpos : (0 : ℚ) < family.card := lt_of_lt_of_le (by positivity) hc
  have h1 := mul_lt_mul_of_pos_left hL hcpos
  have h2 := mul_le_mul_of_nonneg_left hc (le_of_lt (mul_pos hcpos hf₀))
  nlinarith

/-! ### Decidable integer certificates -/

/-- The certificate polynomial `f₀ + ∑_{k=1}^{K} fₖ Hₖ(t)` for integer
coefficients `coeffs = [f₀, f₁, …, f_K]`. -/
def certificatePolynomial (n w : ℕ) (coeffs : List ℕ) (t : ℕ) : ℚ :=
  (coeffs.headD 0 : ℚ) +
    ∑ k ∈ Icc 1 (coeffs.length - 1), (coeffs.getD k 0 : ℚ) * hahnKernel n w k t

/-- Decidable Delsarte certificate for `w`-uniform families with pairwise
intersections at most `lam`: a positive constant term and a nonpositive
certificate polynomial at every realizable intersection size `t ≤ lam`. -/
def certificateValid (n w lam : ℕ) (coeffs : List ℕ) : Bool :=
  decide (0 < coeffs.headD 0) &&
    (List.range (lam + 1)).all fun t ↦
      decide (n + t < 2 * w) || decide (certificatePolynomial n w coeffs t ≤ 0)

/-- The family-size bound certified by `coeffs`. -/
def certifiedBound (n w : ℕ) (coeffs : List ℕ) : ℕ :=
  ⌊certificatePolynomial n w coeffs w / (coeffs.headD 0 : ℚ)⌋₊

/-- A valid integer certificate bounds every admissible uniform family. -/
theorem card_le_certifiedBound {lam : ℕ} {coeffs : List ℕ}
    (hvalid : certificateValid n w lam coeffs = true)
    (family : Finset (Finset (Fin n)))
    (huniform : ∀ A ∈ family, A.card = w)
    (hinter : ∀ A ∈ family, ∀ B ∈ family, A ≠ B → (A ∩ B).card ≤ lam) :
    family.card ≤ certifiedBound n w coeffs := by
  simp only [certificateValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at hvalid
  obtain ⟨hpos, hall⟩ := hvalid
  have hf₀ : (0 : ℚ) < (coeffs.headD 0 : ℚ) := by exact_mod_cast hpos
  refine card_le_of_delsarte family huniform hinter (coeffs.headD 0 : ℚ)
    (fun k ↦ (coeffs.getD k 0 : ℚ)) (K := coeffs.length - 1)
    (fun k _ ↦ by positivity) ?_ _ hf₀ ?_
  · intro t ht hlam
    rcases hall t (by omega) with h | h
    · exact absurd h (by omega)
    · simpa only [certificatePolynomial] using h
  · have hfloor := Nat.lt_floor_add_one
      (certificatePolynomial n w coeffs w / (coeffs.headD 0 : ℚ))
    rw [div_lt_iff₀ hf₀] at hfloor
    simpa only [certificatePolynomial, certifiedBound] using hfloor

/-- A valid integer certificate is a uniform-family bound. -/
theorem uniformFamilyBound_of_certificate {lam : ℕ} {coeffs : List ℕ}
    (hvalid : certificateValid n w lam coeffs = true) :
    UniformFamilyBound n w lam (certifiedBound n w coeffs) :=
  fun family huniform hinter ↦ card_le_certifiedBound hvalid family huniform hinter

end CodingTheory.HahnDelsarte
