import LfzkV2.Events
import SumcheckV1.Grinding

/-! Prefix-local replay of output folding and the selected assertion test. -/

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
variable {F : Type} [Field F]

def prefixBeta {n : ℕ} (i : Fin n) (pref : Fin i.val → F) (j : Fin n) : F :=
  if h : j.val < i.val then pref ⟨j.val,h⟩ else 0

def dataAt {n : ℕ} (incoming claim : F) (values : Fin n → F)
    (i : Fin n) (pref : Fin i.val → F) : ChallengeTest F :=
  .linear (assertionOffset incoming claim (prefixBeta i pref) values i) (values i)

theorem dataAt_eq {n : ℕ} (incoming claim : F) (beta values : Fin n → F) (i : Fin n) :
    dataAt incoming claim values i (SumcheckV1.extract_prefix beta i) =
      .linear (assertionOffset incoming claim beta values i) (values i) := by
  unfold dataAt
  congr 1
  unfold assertionOffset
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [prefixBeta, dif_pos (show j.val < i.val from (mem_filter.mp hj).2)]
  rfl

theorem assertionTests_eq (model : AssertedModel F) (claim : F) :
    assertionTests model claim = (assertionIndices model).toList.map (fun i =>
      (dataAt model.incoming claim model.residuals i (SumcheckV1.extract_prefix model.beta i),
        model.beta i)) := by
  unfold assertionTests
  apply List.map_congr_left
  intro i _
  rw [dataAt_eq]

/-- The selected assertion index is independent of output weights, assertion
challenges, and the later sumcheck point. -/
theorem indices_model_eq {Output : Type} [Fintype Output] {n a : ℕ}
    (layer : CircuitLayer Output (Cube n) (Fin a) F) (w : Cube n → F)
    (weights weights' : Output → F) (beta beta' : Fin a → F) (point point' : Fin n → F) :
    assertionIndices (layer.model weights beta w point) =
      assertionIndices (layer.model weights' beta' w point') := rfl

end LfzkV2.AssertionReplay
