import AffineAgreement.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! Shared minimum-distance and sparse affine support lemmas. -/

namespace AffineAgreement

open scoped BigOperators

variable {F : Type*} [Field F] [DecidableEq F]

namespace Internal

/-! ## Minimum-distance consequences -/

theorem eq_zero_of_weight_lt_distance {n d : ℕ}
    {C : LinearCode F n}
    (hmin : HasMinimumDistanceAtLeast C d)
    {c : Word F n} (hc : c ∈ C) (hweight : weight c < d) : c = 0 :=
  CodingTheory.eq_zero_of_weight_lt_distance hmin hc hweight

theorem eq_of_agree_on {n d : ℕ} {C : LinearCode F n}
    (hmin : HasMinimumDistanceAtLeast C d)
    {x y : Word F n} (hx : x ∈ C) (hy : y ∈ C)
    (I : Finset (Fin n)) (hI : n - d < I.card)
    (hagree : ∀ i ∈ I, x i = y i) : x = y := by
  have hdisjoint : Disjoint (supportOn Finset.univ (x - y)) I := by
    exact Finset.disjoint_left.mpr (by
      intro i his hiI
      exact (mem_supportOn Finset.univ (x - y) i).mp his |>.2
        (sub_eq_zero.mpr (hagree i hiI)))
  have hunion :
      ((supportOn Finset.univ (x - y)) ∪ I).card ≤ n := by
    simpa using Finset.card_le_card
      (show (supportOn Finset.univ (x - y)) ∪ I ⊆
          (Finset.univ : Finset (Fin n)) by
        exact Finset.union_subset (supportOn_subset _ _) (Finset.subset_univ _))
  rw [Finset.card_union_of_disjoint hdisjoint] at hunion
  have hlt : weight (x - y) < d := by
    dsimp [weight]
    omega
  have hz := eq_zero_of_weight_lt_distance hmin (C.sub_mem hx hy) hlt
  exact sub_eq_zero.mp hz

/-! ## Sparse affine lines -/

private theorem active_coordinate_nonzero_count {n : ℕ}
    (x y : Word F n) (S : Finset F) (i : Fin n)
    (hi : i ∈ jointSupport x y) :
    S.card - 1 ≤ (S.filter fun a ↦ affineWord x y a i ≠ 0).card := by
  let Z := S.filter fun a ↦ affineWord x y a i = 0
  have hZ : Z.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha0 := (Finset.mem_filter.mp ha).2
    have hb0 := (Finset.mem_filter.mp hb).2
    by_cases hy : y i = 0
    · have hx : x i ≠ 0 := by
        simpa [jointSupport, hy] using hi
      simp [affineWord, hy, hx] at ha0
    · apply sub_eq_zero.mp
      apply (mul_eq_zero.mp ?_).resolve_right hy
      calc
        (a - b) * y i = affineWord x y a i - affineWord x y b i := by
          simp [affineWord]
          ring
        _ = 0 := by rw [ha0, hb0, sub_self]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (fun a ↦ affineWord x y a i = 0)
  have hnonzero :
      (S.filter fun a ↦ ¬affineWord x y a i = 0).card =
        (S.filter fun a ↦ affineWord x y a i ≠ 0).card := by
    rfl
  rw [hnonzero] at hsplit
  change Z.card +
    (S.filter fun a ↦ affineWord x y a i ≠ 0).card = S.card at hsplit
  rw [← hsplit]
  omega

private theorem sum_affine_supports {n : ℕ}
    (x y : Word F n) (S : Finset F) :
    ∑ a ∈ S, weight (affineWord x y a) =
      ∑ i, (S.filter fun a ↦ affineWord x y a i ≠ 0).card := by
  have hsupp (a : F) : weight (affineWord x y a) =
      ∑ i : Fin n, if affineWord x y a i ≠ 0 then (1 : ℕ) else 0 := by
    change ((Finset.univ : Finset (Fin n)).filter fun i ↦
      affineWord x y a i ≠ 0).card = _
    exact (Finset.sum_boole (R := ℕ)
      (fun i ↦ affineWord x y a i ≠ 0) Finset.univ).symm
  have hfilter (i : Fin n) :
      (S.filter fun a ↦ affineWord x y a i ≠ 0).card =
        ∑ a ∈ S, if affineWord x y a i ≠ 0 then 1 else 0 := by
    exact (Finset.sum_boole (R := ℕ)
      (fun a ↦ affineWord x y a i ≠ 0) S).symm
  simp_rw [hsupp, hfilter]
  rw [Finset.sum_comm]

theorem affineLine_incidence_bound {n e : ℕ}
    (x y : Word F n) (S : Finset F)
    (hweight : ∀ a ∈ S, weight (affineWord x y a) ≤ e) :
    (S.card - 1) * (jointSupport x y).card ≤ S.card * e := by
  have hlower : (S.card - 1) * (jointSupport x y).card ≤
      ∑ i, (S.filter fun a ↦ affineWord x y a i ≠ 0).card := by
    calc
      (S.card - 1) * (jointSupport x y).card =
          ∑ i ∈ jointSupport x y, (S.card - 1) := by simp [mul_comm]
      _ ≤ ∑ i ∈ jointSupport x y,
          (S.filter fun a ↦ affineWord x y a i ≠ 0).card := by
        exact Finset.sum_le_sum fun i hi ↦
          active_coordinate_nonzero_count x y S i hi
      _ ≤ ∑ i,
          (S.filter fun a ↦ affineWord x y a i ≠ 0).card := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ ↦ Nat.zero_le _)
  calc
    _ ≤ ∑ i, (S.filter fun a ↦ affineWord x y a i ≠ 0).card := hlower
    _ = ∑ a ∈ S, weight (affineWord x y a) :=
      (sum_affine_supports x y S).symm
    _ ≤ ∑ _a ∈ S, e := Finset.sum_le_sum fun a ha ↦ hweight a ha
    _ = S.card * e := by simp

theorem jointSupport_card_le {n e : ℕ}
    (x y : Word F n) (S : Finset F) (hS : 2 ≤ S.card)
    (hweight : ∀ a ∈ S, weight (affineWord x y a) ≤ e) :
    (jointSupport x y).card ≤ e + e / (S.card - 1) := by
  have hinc := affineLine_incidence_bound x y S hweight
  have hpos : 0 < S.card - 1 := by omega
  have hquot : (jointSupport x y).card ≤
      S.card * e / (S.card - 1) := by
    exact (Nat.le_div_iff_mul_le hpos).2 (by
      simpa [mul_comm] using hinc)
  have hcard : S.card = (S.card - 1) + 1 := by omega
  have hrewrite : S.card * e / (S.card - 1) =
      e + e / (S.card - 1) := by
    rw [hcard, Nat.add_sub_cancel, add_mul, one_mul]
    rw [add_comm ((S.card - 1) * e) e,
      Nat.add_mul_div_left _ _ hpos, add_comm]
  rwa [hrewrite] at hquot

theorem jointSupport_card_le_of_many {n e : ℕ}
    (x y : Word F n) (S : Finset F) (hS : e + 1 < S.card)
    (hweight : ∀ a ∈ S, weight (affineWord x y a) ≤ e) :
    (jointSupport x y).card ≤ e := by
  have h := jointSupport_card_le x y S (by omega) hweight
  have hdiv : e / (S.card - 1) = 0 := Nat.div_eq_of_lt (by omega)
  simpa [hdiv] using h

/-- If the active support has a known lower bound `L > e`, incidence bounds
the number of radius-`e` points on the affine line by `L / (L-e)`. -/
theorem affineLine_card_le_of_support_lower {n e L : ℕ}
    (x y : Word F n) (S : Finset F)
    (hS : 1 ≤ S.card) (heL : e < L)
    (hL : L ≤ (jointSupport x y).card)
    (hweight : ∀ a ∈ S, weight (affineWord x y a) ≤ e) :
    S.card ≤ L / (L - e) := by
  have hinc := affineLine_incidence_bound x y S hweight
  have hscaled : (S.card - 1) * L ≤ S.card * e := by
    calc
      (S.card - 1) * L ≤
          (S.card - 1) * (jointSupport x y).card :=
        Nat.mul_le_mul_left _ hL
      _ ≤ S.card * e := hinc
  have hmul : S.card * (L - e) ≤ L := by
    have hScard : S.card - 1 + 1 = S.card := by omega
    have hLsplit : e + (L - e) = L := by omega
    have hcancel : (S.card - 1) * (L - e) ≤ e := by
      apply Nat.le_of_add_le_add_left
      calc
        (S.card - 1) * e + (S.card - 1) * (L - e) =
            (S.card - 1) * (e + (L - e)) := by rw [mul_add]
        _ = (S.card - 1) * L := congrArg ((S.card - 1) * ·) hLsplit
        _ ≤ S.card * e := hscaled
        _ = (S.card - 1 + 1) * e := congrArg (· * e) hScard.symm
        _ = (S.card - 1) * e + e := by rw [add_mul, one_mul]
    calc
      S.card * (L - e) = (S.card - 1 + 1) * (L - e) := by
        rw [hScard]
      _ = (S.card - 1) * (L - e) + (L - e) := by
        rw [add_mul, one_mul]
      _ ≤ e + (L - e) := Nat.add_le_add_right hcancel _
      _ = L := hLsplit
  exact (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt heL)).2 hmul

end Internal

export Internal (eq_zero_of_weight_lt_distance affineLine_incidence_bound
  eq_of_agree_on jointSupport_card_le jointSupport_card_le_of_many
  affineLine_card_le_of_support_lower)

end AffineAgreement
