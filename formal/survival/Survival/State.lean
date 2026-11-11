import Survival.Basic

/-! The deterministic archive invariant. Hash recovery must establish that
the parent was already archived. No hash-oracle freshness is assumed here.
-/
namespace Survival.State

variable {S M A : Type}

def Escape (rejecting : S → Prop) (next : S → M → A → S)
    (state : S) (message : M) (answer : A) : Prop :=
  rejecting state ∧ ¬rejecting (next state message answer)

inductive Archive (rejecting : S → Prop) (next : S → M → A → S) (initial : S) : List S → Prop
  | root : Archive rejecting next initial [initial]
  | extend {states : List S} (previous : Archive rejecting next initial states)
      (parent : S) (present : parent ∈ states) (message : M) (answer : A)
      (safe : ¬Escape rejecting next parent message answer) :
      Archive rejecting next initial (next parent message answer :: states)

/-- Induction is over node creation. Different branches may restore any
already archived parent; their creation need not follow one final proof path. -/
theorem rejecting_archive (rejecting : S → Prop) (next : S → M → A → S) (initial : S)
    (initial_rejects : rejecting initial) {states : List S}
    (built : Archive rejecting next initial states) : ∀ state ∈ states, rejecting state := by
  induction built with
  | root => simpa using initial_rejects
  | @extend states previous parent present message answer safe ih =>
      intro state member
      rcases List.mem_cons.mp member with same | old
      · subst state
        by_contra accepted
        exact safe ⟨ih parent present, accepted⟩
      · exact ih state old

end Survival.State
