import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Two independent masked linear fingerprints over an arbitrary finite field.
The original cells and the two dedicated mask cells are separate coordinates. -/
namespace WitnessSelection

open Finset
open scoped Classical

abbrev Candidate (F ι : Type) := (ι → F) × (F × F)
abbrev Coins (F ι : Type) := (ι → F) × (ι → F)

variable {F ι : Type} [Field F] [Fintype ι]

def dot (a v : ι → F) : F := ∑ i, a i * v i

def fingerprint (a : Coins F ι) (w : Candidate F ι) : F × F :=
  (w.2.1 + dot a.1 w.1, w.2.2 + dot a.2 w.1)

/-- These are exactly the affine rows appended to the backend statement. -/
theorem affine_rows_iff (a : Coins F ι) (w : Candidate F ι) (t : F × F) :
    (dot a.1 w.1 + w.2.1 - t.1 = 0 ∧ dot a.2 w.1 + w.2.2 - t.2 = 0) ↔
      fingerprint a w = t := by
  simp [fingerprint, Prod.ext_iff, sub_eq_zero, add_comm]

theorem dot_sub_left (a b d : ι → F) :
    dot (a-b) d = dot a d - dot b d := by
  simp [dot, sub_mul, sum_sub_distrib]

theorem dot_sub_right (a v w : ι → F) :
    dot a (v-w) = dot a v - dot a w := by
  simp [dot, mul_sub, sum_sub_distrib]

def splitCoordinate [DecidableEq ι] (p : ι) : (ι → F) ≃ F × ({i : ι // i ≠ p} → F) where
  toFun a := (a p, fun i => a i.1)
  invFun b i := if h : i = p then b.1 else b.2 ⟨i,h⟩
  left_inv a := by
    funext i
    by_cases h : i = p <;> simp [h]
  right_inv b := by
    apply Prod.ext
    · simp
    · funext i
      simp [i.2]

omit [Field F] in
theorem coins_card_split [Fintype F] [DecidableEq ι] (p : ι) :
    Fintype.card (Coins F ι) = Fintype.card F ^ 2 *
      Fintype.card ({i : ι // i ≠ p} → F) ^ 2 := by
  have h := Fintype.card_congr (splitCoordinate (F := F) p)
  simp only [Fintype.card_prod] at h
  simp only [Coins, Fintype.card_prod]
  rw [h]
  ring

theorem dot_eq_of_restriction [DecidableEq ι] (d : ι → F) (c : F) (p : ι) (hd : d p ≠ 0)
    {a b : ι → F} (ha : dot a d = c) (hb : dot b d = c)
    (hout : ∀ i, i ≠ p → a i = b i) : a = b := by
  have hs : (∑ i, (a i-b i)*d i) = (a p-b p)*d p := by
    apply sum_eq_single p
    · intro i _ hi
      simp [hout i hi]
    · intro hp
      simp at hp
  have hz : dot (a-b) d = 0 := by rw [dot_sub_left, ha, hb, sub_self]
  have hm : (a p-b p)*d p = 0 := by simpa [dot, hs] using hz
  have hab : a p = b p := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hd)
  funext i
  by_cases hi : i = p
  · simpa [hi] using hab
  · exact hout i hi

theorem collision_dot (a : Coins F ι) (x y : Candidate F ι)
    (h : fingerprint a x = fingerprint a y) :
    dot a.1 (x.1-y.1) = y.2.1-x.2.1 ∧
      dot a.2 (x.1-y.1) = y.2.2-x.2.2 := by
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [fingerprint] at h₁ h₂
  constructor
  · rw [dot_sub_right]
    linear_combination h₁
  · rw [dot_sub_right]
    linear_combination h₂

/-- Identical original cells cannot collide through different dedicated masks. -/
theorem same_data_collision (a : Coins F ι) (x y : Candidate F ι)
    (hdata : x.1 = y.1) (h : fingerprint a x = fingerprint a y) : x = y := by
  apply Prod.ext hdata
  apply Prod.ext
  · have h₁ := congrArg Prod.fst h
    simpa [fingerprint, hdata] using h₁
  · have h₂ := congrArg Prod.snd h
    simpa [fingerprint, hdata] using h₂

/-- Fixing a and the original witness translates the two fresh masks bijectively.
This is the response-hiding component, not a full commitment/ZK theorem. -/
def maskTranslation (a : Coins F ι) (w : ι → F) : (F × F) ≃ (F × F) where
  toFun m := fingerprint a (w,m)
  invFun t := (t.1-dot a.1 w, t.2-dot a.2 w)
  left_inv m := by simp [fingerprint]
  right_inv t := by simp [fingerprint]

end WitnessSelection
