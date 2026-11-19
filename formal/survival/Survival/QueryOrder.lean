import Survival.History

/-! Chronological query order along a recovered protocol path. No cache or
completed oracle is constructed. -/
noncomputable section
namespace Survival.QueryOrder
open Merkle.RandomOracle TranscriptV2 Bcs.TotalOracle
open scoped Classical
variable {P A Out : Type} [DecidableEq P]

theorem before_of_first_left {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A)
    (parent child : P) (different : parent ≠ child) (queriedChild : child ∈ seen tree H)
    (ordered : firstOfTwo tree H parent child = .left) : parent ∈ before tree H child := by
  induction tree with
  | done _ => simp only [seen, queried_done, List.toFinset_nil, Finset.notMem_empty] at queriedChild
  | query point next ih =>
      by_cases hp : point = parent
      · subst point
        simp only [before, different, if_false, List.mem_cons, true_or]
      · by_cases hc : point = child
        · rw [firstOfTwo, if_neg hp, if_pos hc] at ordered
          cases ordered
        · have later : child ∈ seen (next (H point)) H := by
            simpa [seen, queried_query, Ne.symm hc] using queriedChild
          have orderTail : firstOfTwo (next (H point)) H parent child = .left := by
            simpa only [firstOfTwo, hp, hc, if_false] using ordered
          rw [before, if_neg hc]
          exact List.mem_cons_of_mem point (ih (H point) later orderTail)

theorem before_trans {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A)
    (first second third : P) (left : first ∈ before tree H second)
    (right : second ∈ before tree H third) : first ∈ before tree H third := by
  induction tree with
  | done _ => simp [before] at left
  | query point next ih =>
      by_cases ht : point = third
      · simp only [before, ht, if_true, List.not_mem_nil] at right
      · by_cases hs : point = second
        · simp only [before, hs, if_true, List.not_mem_nil] at left
        · by_cases hf : point = first
          · rw [before, if_neg ht]
            exact List.mem_cons.mpr (Or.inl hf.symm)
          · have leftTail : first ∈ before (next (H point)) H second := by
              simpa only [before, hs, if_false, List.mem_cons, Ne.symm hf, false_or] using left
            have rightTail : second ∈ before (next (H point)) H third := by
              simpa only [before, ht, if_false, List.mem_cons, Ne.symm hs, false_or] using right
            rw [before, if_neg ht]
            exact List.mem_cons_of_mem point (ih (H point) leftTail rightTail)

theorem earlier_path_before {fuel rounds : ℕ} (tree : Tree P A Out fuel) (H : P → A)
    (path : ℕ → P)
    (queriedPath : ∀ i ≤ rounds, path i ∈ seen tree H)
    (ordered : ∀ i < rounds, firstOfTwo tree H (path i) (path (i+1)) = .left)
    (different : ∀ i < rounds, path i ≠ path (i+1))
    (index : ℕ) (within : index ≤ rounds) : ∀ earlier < index, path earlier ∈ before tree H (path index) := by
  induction index with
  | zero => intro earlier impossible; omega
  | succ index ih =>
      have hi : index < rounds := by omega
      have last := before_of_first_left tree H (path index) (path (index+1)) (different index hi)
        (queriedPath (index+1) within) (ordered index hi)
      intro earlier bounded
      by_cases same : earlier = index
      · simpa only [same] using last
      · have old := ih (by omega) earlier (by omega)
        exact before_trans tree H (path earlier) (path index) (path (index+1)) old last

end Survival.QueryOrder
