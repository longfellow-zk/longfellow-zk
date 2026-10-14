import LigeroFamily.Protocol.Evaluation

/-! # Injectivity of committed base-row evaluations -/

namespace LigeroFamily.MultiplicativeCode

open CodingTheory
open LigeroFamily

variable {F : Type*} [Field F] {r w n : ℕ}

/-- A base evaluation row is determined by its committed codeword. -/
theorem baseRow_eq_of_codeword_eq
    (C : MultiplicativeCode F r w n)
    {left right : EvaluationRow F r w n}
    (hleft : left ∈ C.base) (hright : right ∈ C.base)
    (hcodeword : codeword left = codeword right) :
    left = right := by
  obtain ⟨J, _hJsubset, hJcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n)))
      (show C.k ≤ (Finset.univ : Finset (Fin n)).card by
        simpa using C.k_le_n)
  apply C.base_unique hleft hright (codePositions (r := r) (w := w) J)
  · simp [hJcard]
  · intro i hi
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hi
    exact congrFun hcodeword j

/-- A response evaluation row is determined by its committed codeword once
the committed block contains the `2k` positions required by
`response_unique`.  It gives uniqueness of an evaluation-form response row
from its committed response codeword. -/
theorem responseRow_eq_of_codeword_eq
    (C : MultiplicativeCode F r w n) (h2k : 2 * C.k ≤ n)
    {left right : EvaluationRow F r w n}
    (hleft : left ∈ C.response) (hright : right ∈ C.response)
    (hcodeword : codeword left = codeword right) :
    left = right := by
  obtain ⟨J, _hJsubset, hJcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n)))
      (show 2 * C.k ≤ (Finset.univ : Finset (Fin n)).card by
        simpa using h2k)
  apply C.response_unique hleft hright (codePositions (r := r) (w := w) J)
  · simp [hJcard]
  · intro i hi
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hi
    exact congrFun hcodeword j

end LigeroFamily.MultiplicativeCode
