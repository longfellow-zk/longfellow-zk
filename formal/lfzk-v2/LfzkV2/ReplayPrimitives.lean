import LfzkV2.Constraints

/-! Shared vector scheduling and symbolic round totality. -/
namespace LfzkV2.Replay
open SumcheckV2
variable {F Pad C : Type} [Field F]

def vectorSlots (n : ℕ) : ℕ := if n = 0 then 0 else 1

def outputPoint (decode : (n : ℕ) → C → Fin n → F) (out : ℕ) (answers : ℕ → C) : Fin out → F :=
  decode out (answers 0)

theorem rounds_total (claim : PadExpression Pad F) (messages : List (RoundPoly F × Pad × Pad))
    (challenges : List F) (hlen : messages.length = challenges.length) :
    ∃ terminal, claim.rounds messages challenges = some terminal := by
  induction messages generalizing claim challenges with
  | nil =>
      have hz : challenges = [] := List.length_eq_zero_iff.mp hlen.symm
      subst challenges
      exact ⟨claim,rfl⟩
  | cons message messages ih =>
      cases challenges with
      | nil => simp at hlen
      | cons z zs =>
          obtain ⟨m,p0,p1⟩ := message
          exact ih (claim.round m z p0 p1) zs (Nat.succ.inj hlen)

end LfzkV2.Replay
