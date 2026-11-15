import LfzkV2.ChallengeTests
import SumcheckV1.Grinding

/-! Prefix-local output and assertion tests shared by all circuit models. -/
namespace LfzkV2.OutputReplay
open SumcheckV2
variable {F : Type} [Field F]

noncomputable def dataAt : {n : ℕ} → (Cube n → F) → (i : Fin n) →
    (Fin i.val → F) → ChallengeTest F
  | 0, _ => fun i => Fin.elim0 i
  | n+1, table =>
      Fin.cases (motive := fun i : Fin (n+1) => (Fin i.val → F) → ChallengeTest F)
        (fun _ => .output table)
        (fun i pref => dataAt (fold table (pref ⟨0, Nat.succ_pos _⟩)) i (fun j => pref j.succ))

theorem dataAt_valid {n : ℕ} (table : Cube n → F) (i : Fin n) (pref : Fin i.val → F) :
    (dataAt table i pref).Valid := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ ?_ i pref
      · intro _; trivial
      · intro i pref; exact ih _ i _

theorem dataAt_budget {n : ℕ} (table : Cube n → F) (i : Fin n) (pref : Fin i.val → F) :
    (dataAt table i pref).budget = 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ ?_ i pref
      · intro _; rfl
      · intro i pref; exact ih _ i _

theorem outputTests_eq {n : ℕ} (table : Cube n → F) (point : Fin n → F) :
    outputTests table point = List.ofFn (fun i =>
      (dataAt table i (SumcheckV1.extract_prefix point i), point i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [outputTests, List.ofFn_succ, dataAt, Fin.cases_zero, Fin.cases_succ,
        SumcheckV1.extract_prefix]
      rw [ih]
      rfl

end LfzkV2.OutputReplay

namespace LfzkV2.AssertionReplay
open SumcheckV2 Finset
open scoped Classical
end LfzkV2.AssertionReplay
