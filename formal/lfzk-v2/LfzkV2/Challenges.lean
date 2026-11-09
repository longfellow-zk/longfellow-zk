import LfzkV2.Circuit
import SumcheckV2.Challenges

/-!
# Initial output and assertion challenges

Output tables are monomial coefficients. Folding a nonzero table to the zero
table costs at most one field challenge. For assertion batching, use the last
nonzero residual: the resulting linear test depends only on earlier assertion
challenges, even when there are many zero or duplicate assertion occurrences.
-/

namespace LfzkV2

open SumcheckV2 Classical

variable {F : Type} [Field F]

def BadLinear (offset slope z : F) : Prop := slope ≠ 0 ∧ offset + z * slope = 0

theorem bad_linear_card [Fintype F] (offset slope : F) :
    (Finset.univ.filter fun z => BadLinear offset slope z).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hs, hx⟩ := (Finset.mem_filter.mp hx).2
  have hy := (Finset.mem_filter.mp hy).2.2
  exact mul_right_cancel₀ hs (add_left_cancel (hx.trans hy.symm))

def BadFold {n : ℕ} (table : Cube (n + 1) → F) (z : F) : Prop :=
  table ≠ 0 ∧ fold table z = 0

theorem bad_fold_card [Fintype F] {n : ℕ} (table : Cube (n + 1) → F) :
    (Finset.univ.filter fun z => BadFold table z).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hnz, hx⟩ := (Finset.mem_filter.mp hx).2
  have hy := (Finset.mem_filter.mp hy).2.2
  by_cases hxy : x = y
  · exact hxy
  · exfalso
    apply hnz
    have hzero (i : Cube n) : even table i = 0 ∧ odd table i = 0 := by
      have hxi := congrFun hx i
      have hyi := congrFun hy i
      simp only [fold, bindPair, Pi.zero_apply] at hxi hyi
      have hprod : (x - y) * odd table i = 0 := by linear_combination hxi - hyi
      have ho := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hxy)
      exact ⟨by simpa [ho] using hxi, ho⟩
    funext i
    rcases i with ⟨bit, i⟩
    cases bit
    · exact (hzero i).1
    · exact (hzero i).2

def OutputBad : {n : ℕ} → (Cube n → F) → (Fin n → F) → Prop
  | 0, _, _ => False
  | _ + 1, table, point => BadFold table (point 0) ∨
      OutputBad (fold table (point 0)) (fun j => point j.succ)

/-- A nonzero output vector can evaluate to zero only after a bad fold.
The scalar case consumes no challenges and has no bad event. -/
theorem output_reduction {n : ℕ} (table : Cube n → F) (point : Fin n → F)
    (hnz : table ≠ 0) (heval : evaluate table point = 0) : OutputBad table point := by
  induction n with
  | zero =>
      apply hnz.elim
      funext i
      cases i
      exact heval
  | succ n ih =>
      by_cases hfold : fold table (point 0) = 0
      · exact Or.inl ⟨hnz, hfold⟩
      · exact Or.inr (ih _ _ hfold heval)

def assertionOffset {n : ℕ} (incoming claim : F) (beta values : Fin n → F) (i : Fin n) : F :=
  incoming - claim + ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), beta j * values j

/-- This event uses only the challenge prefix: the last nonzero residual is
selected from the committed witness, independently of the challenges. -/
def AssertionSlotBad {n : ℕ} (incoming claim : F) (beta values : Fin n → F) (i : Fin n) : Prop :=
  (∀ j, i < j → values j = 0) ∧
    BadLinear (assertionOffset incoming claim beta values i) (values i) (beta i)

def AssertionBad {n : ℕ} (incoming claim : F) (beta values : Fin n → F) : Prop :=
  ∃ i, AssertionSlotBad incoming claim beta values i

theorem assertion_dot_eq_prefix {n : ℕ} (beta values : Fin n → F) (i : Fin n)
    (hlast : ∀ j, i < j → values j = 0) :
    dot beta values =
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), beta j * values j) + beta i * values i := by
  unfold dot
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  congr 1
  symm
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_erase.mpr ⟨ne_of_lt (Finset.mem_filter.mp hj).2, Finset.mem_univ j⟩
  · intro j hj hnmem
    have hji := (Finset.mem_erase.mp hj).1
    have hnlt : ¬ j < i := by simpa using hnmem
    rw [hlast j (lt_of_le_of_ne (le_of_not_gt hnlt) hji.symm), mul_zero]

theorem assertion_reduction {n : ℕ} (incoming claim : F) (beta values : Fin n → F)
    (hbad : ∃ i, values i ≠ 0) (heq : claim = incoming + dot beta values) :
    AssertionBad incoming claim beta values := by
  let active := Finset.univ.filter fun i => values i ≠ 0
  have hn : active.Nonempty := by
    obtain ⟨j, hj⟩ := hbad
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  let i := active.max' hn
  have hi : values i ≠ 0 := (Finset.mem_filter.mp (active.max'_mem hn)).2
  have hlast (j : Fin n) (hij : i < j) : values j = 0 := by
    by_cases hz : values j = 0
    · exact hz
    · have hle : j ≤ i := active.le_max' j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hz⟩)
      exact (not_lt_of_ge hle hij).elim
  refine ⟨i, hlast, hi, ?_⟩
  have hsum := assertion_dot_eq_prefix beta values i hlast
  unfold assertionOffset
  rw [hsum] at heq
  linear_combination -heq

end LfzkV2
