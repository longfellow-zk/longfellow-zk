import LfzkV2.Current.Prefix

/-! A local failure test receives the fixed query prefix and one candidate
answer. Completing unavailable future answers with an arbitrary constant does
not give the test access to the oracle answer it is being charged against. -/
namespace LfzkV2.Current

def completeAnswers {C : Type} {cut : ℕ} (past : Fin cut → C)
    (current fallback : C) (j : ℕ) : C :=
  if h : j < cut then past ⟨j,h⟩ else if j = cut then current else fallback

theorem completeAnswers_agrees {C : Type} (answers : ℕ → C) (cut : ℕ) (fallback : C)
    (j : ℕ) (hj : j ≤ cut) :
    completeAnswers (fun i : Fin cut => answers i.val) (answers cut) fallback j = answers j := by
  by_cases h : j < cut
  · simp [completeAnswers, h]
  · have he : j = cut := by omega
    subst j
    simp [completeAnswers]

namespace Input
variable {roles : List Role} {Context Block Link Body C : Type}

def answersWith (point : Input roles Context Block Link Body)
    (H : Input roles Context Block Link Body → Link × C) (current fallback : C) : ℕ → C :=
  completeAnswers (point.priorAnswers H) current fallback

/-- The candidate answer is an explicit argument; all actual oracle reads
are strict ancestors. Changing the oracle at this query cannot alter the test's
completed tape. This is valid for adversarially constructed query preimages too. -/
theorem answersWith_off (point : Input roles Context Block Link Body)
    (H H' : Input roles Context Block Link Body → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (current fallback : C) :
    point.answersWith H current fallback = point.answersWith H' current fallback := by
  unfold answersWith
  rw [point.priorAnswers_off h]

end Input
end LfzkV2.Current
