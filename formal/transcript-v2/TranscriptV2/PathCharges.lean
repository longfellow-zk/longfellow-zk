import TranscriptV2.SharedCharging

/-! Nonnegative original-query charges and deterministic coverage along a
recovered ordered path. This module assumes no transcript seal construction. -/
namespace TranscriptV2
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical
variable {P Link C Out Parent Response : Type} [DecidableEq P] {R : ℕ}
namespace PathCharges
variable [Fintype Parent] [Fintype Response]
variable {parent : Parent → P} {child : Parent → Response → P}
variable {single : P → (P → Link × C) → (Link × C) → ℚ}
variable {pair : Parent → Response → (P → Link × C) → (Link × C) → (Link × C) → ℚ}

def charges {fuel : ℕ} (tree : Tree P (Link × C) Out fuel) (H : P → Link × C) : ℚ :=
  (∑ z ∈ seen tree H, single z H (H z)) +
    ∑ p, ∑ r, if firstOfTwo tree H (parent p) (child p r) = .left then
      pair p r H (H (parent p)) (H (child p r)) else 0

theorem charges_nonneg {fuel : ℕ} (tree : Tree P (Link × C) Out fuel) (H : P → Link × C)
    (hs : ∀ z H a, 0 ≤ single z H a) (hp : ∀ p r H a b, 0 ≤ pair p r H a b) :
    0 ≤ charges (parent := parent) (child := child) (single := single) (pair := pair) tree H := by
  apply add_nonneg
  · exact sum_nonneg (fun z _ => hs z H (H z))
  · apply sum_nonneg
    intro p _
    apply sum_nonneg
    intro r _
    split_ifs
    · exact hp p r H _ _
    · exact le_rfl

/-- The positive-charge argument needs only query membership and order on
an accepted path. It does not depend on how the transcript encodes parents. -/
theorem charges_of_cover {fuel : ℕ} (tree : Tree P (Link × C) Out fuel) (H : P → Link × C)
    (point : ℕ → P)
    (hqueries : ∀ n, n ≤ R → point n ∈ seen tree H)
    (horder : ∀ n, n < R → firstOfTwo tree H (point n) (point (n+1)) = .left)
    (hs : ∀ z H a, 0 ≤ single z H a) (hp : ∀ p r H a b, 0 ≤ pair p r H a b)
    (hcover : (∃ n < R, 1 ≤ single (point n) H (H (point n))) ∨
      (∃ n < R, ∃ p r, parent p = point n ∧ child p r = point (n+1) ∧
        1 ≤ pair p r H (H (parent p)) (H (child p r)))) :
    1 ≤ charges (parent := parent) (child := child) (single := single) (pair := pair) tree H := by
  let pairs := fun p => ∑ r, if firstOfTwo tree H (parent p) (child p r) = .left then
    pair p r H (H (parent p)) (H (child p r)) else 0
  have hpair p r : 0 ≤ (if firstOfTwo tree H (parent p) (child p r) = .left then
      pair p r H (H (parent p)) (H (child p r)) else 0) := by
    split_ifs
    · exact hp p r H _ _
    · exact le_rfl
  have hpairs p : 0 ≤ pairs p := sum_nonneg (fun r _ => hpair p r)
  rcases hcover with ⟨i,hi,hbad⟩ | ⟨i,hi,p,r,hpPoint,hcPoint,hbad⟩
  · have hsum := single_le_sum (fun z _ => hs z H (H z)) (hqueries i (by omega))
    exact (hbad.trans hsum).trans (le_add_of_nonneg_right (sum_nonneg (fun p _ => hpairs p)))
  · have hfirst : firstOfTwo tree H (parent p) (child p r) = .left := by
      rw [hpPoint, hcPoint]
      exact horder i hi
    have hinner := single_le_sum (fun r _ => hpair p r) (mem_univ r)
    rw [if_pos hfirst] at hinner
    have houter := single_le_sum (fun p _ => hpairs p) (mem_univ p)
    exact ((hbad.trans hinner).trans houter).trans
      (le_add_of_nonneg_left (sum_nonneg (fun z _ => hs z H (H z))))

end PathCharges
end TranscriptV2
