import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Shared coding-theory vocabulary

This module owns the word, support, weight, code, and minimum-distance
definitions shared by arbitrary-code agreement and Reed--Solomon codes.
-/

namespace CodingTheory

/-- A length-`n` word over the alphabet `F`. -/
abbrev Word (F : Type*) (n : ℕ) := Fin n → F

/-- A linear length-`n` code over `F`. -/
abbrev LinearCode (F : Type*) [Semiring F] (n : ℕ) :=
  Submodule F (Word F n)

section Support

variable {F : Type*} [Zero F] [DecidableEq F]

/-- Support of a word on a finite coordinate set. -/
def supportOn {n : ℕ} (U : Finset (Fin n)) (w : Word F n) : Finset (Fin n) :=
  U.filter fun i ↦ w i ≠ 0

@[simp] theorem mem_supportOn {n : ℕ} (U : Finset (Fin n))
    (w : Word F n) (i : Fin n) :
    i ∈ supportOn U w ↔ i ∈ U ∧ w i ≠ 0 := by
  simp [supportOn]

theorem supportOn_subset {n : ℕ} (U : Finset (Fin n)) (w : Word F n) :
    supportOn U w ⊆ U := by
  intro i hi
  exact (mem_supportOn U w i).mp hi |>.1

/-- Hamming weight. -/
def weight {n : ℕ} (w : Word F n) : ℕ :=
  (supportOn Finset.univ w).card

/-- The union of the supports of two words. -/
def jointSupport {n : ℕ} (x y : Word F n) : Finset (Fin n) :=
  supportOn Finset.univ x ∪ supportOn Finset.univ y

/-- A word's total weight is bounded by its support in a selected region plus
all coordinates outside that region. -/
theorem weight_le_supportOn_add_complement {n : ℕ}
    (U : Finset (Fin n)) (x : Word F n) :
    weight x ≤ (supportOn U x).card + (Finset.univ \ U).card := by
  have hsubset : supportOn Finset.univ x ⊆
      supportOn U x ∪ (Finset.univ \ U) := by
    intro i hi
    by_cases hU : i ∈ U
    · exact Finset.mem_union_left _
        ((mem_supportOn U x i).mpr
          ⟨hU, (mem_supportOn Finset.univ x i).mp hi |>.2⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hU⟩)
  exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)

end Support

section Agreement

variable {F : Type*} [DecidableEq F]

/-- Coordinates on which two words agree. -/
def agreementCoordinates {n : ℕ} (left right : Word F n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ left i = right i

@[simp] theorem mem_agreementCoordinates {n : ℕ}
    (left right : Word F n) (i : Fin n) :
    i ∈ agreementCoordinates left right ↔ left i = right i := by
  simp [agreementCoordinates]

end Agreement

section SemiringSupport

variable {F : Type*} [Semiring F] [DecidableEq F]

/-- `C` has minimum distance at least `d`. -/
structure HasMinimumDistanceAtLeast {n : ℕ} (C : LinearCode F n)
    (d : ℕ) : Prop where
  distance_le_length : d ≤ n
  weight_ge_distance : ∀ c : Word F n, c ∈ C → c ≠ 0 → d ≤ weight c

theorem supportOn_add_subset {n : ℕ} (U : Finset (Fin n)) (x y : Word F n) :
    supportOn U (x + y) ⊆ supportOn U x ∪ supportOn U y := by
  intro i hi
  have hiparts := (mem_supportOn U (x + y) i).mp hi
  by_cases hx : x i = 0
  · apply Finset.mem_union_right
    exact (mem_supportOn U y i).mpr
      ⟨hiparts.1, fun hy ↦ hiparts.2 (by simp [hx, hy])⟩
  · exact Finset.mem_union_left _
      ((mem_supportOn U x i).mpr ⟨hiparts.1, hx⟩)

theorem supportOn_add_card_le {n : ℕ} (U : Finset (Fin n)) (x y : Word F n) :
    (supportOn U (x + y)).card ≤
      (supportOn U x).card + (supportOn U y).card :=
  (Finset.card_le_card (supportOn_add_subset U x y)).trans
    (Finset.card_union_le _ _)

theorem weight_add_le {n : ℕ} (x y : Word F n) :
    weight (x + y) ≤ weight x + weight y :=
  supportOn_add_card_le Finset.univ x y

theorem supportOn_smul_subset {n : ℕ} (U : Finset (Fin n))
    (a : F) (x : Word F n) : supportOn U (a • x) ⊆ supportOn U x := by
  intro i hi
  have hiparts := (mem_supportOn U (a • x) i).mp hi
  apply (mem_supportOn U x i).mpr
  refine ⟨hiparts.1, ?_⟩
  intro hx
  exact hiparts.2 (by simp [hx])

theorem supportOn_smul_card_le {n : ℕ} (U : Finset (Fin n))
    (a : F) (x : Word F n) :
    (supportOn U (a • x)).card ≤ (supportOn U x).card :=
  Finset.card_le_card (supportOn_smul_subset U a x)

theorem weight_smul_le {n : ℕ} (a : F) (x : Word F n) :
    weight (a • x) ≤ weight x :=
  supportOn_smul_card_le Finset.univ a x

/-- A nonzero codeword has at least the minimum distance many nonzero
coordinates. -/
theorem eq_zero_of_weight_lt_distance {n d : ℕ} {C : LinearCode F n}
    (hmin : HasMinimumDistanceAtLeast C d)
    {c : Word F n} (hc : c ∈ C) (hweight : weight c < d) : c = 0 := by
  exact not_ne_iff.mp fun hne ↦
    (Nat.not_le_of_lt hweight) (hmin.weight_ge_distance c hc hne)

end SemiringSupport

section NegSupport

variable {F : Type*} [AddGroup F] [DecidableEq F]

@[simp] theorem supportOn_neg {n : ℕ} (U : Finset (Fin n)) (x : Word F n) :
    supportOn U (-x) = supportOn U x := by
  ext i
  simp [supportOn]

@[simp] theorem weight_neg {n : ℕ} (x : Word F n) : weight (-x) = weight x := by
  simp [weight]

end NegSupport

end CodingTheory
