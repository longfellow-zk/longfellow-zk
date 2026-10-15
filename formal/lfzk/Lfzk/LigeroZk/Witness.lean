import LigeroFamily.Protocol.Basic

-- Ported verbatim from `proofs/ligero/LigeroFamily/ZeroKnowledge/Witness.lean` (only the import paths are rewritten);
-- `formal/ligero/` must not change, so the module lives under `Lfzk.LigeroZk`.
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Canonical witnesses for unbounded zero-knowledge simulators -/

namespace LigeroFamily.ZeroKnowledge

open LigeroFamily

variable {F Equations : Type*} [CommSemiring F]
variable {nw nq w : ℕ}

/-- Canonical satisfying messages selected from a public statement.  The
false-statement branch only makes the function total. -/
noncomputable def referenceMessages
    (statement : ConstraintSystem F nw nq w Equations) :
    CoreMessages F nw nq w := by
  classical
  exact if hlanguage : statement.Language then Classical.choose hlanguage else 0

theorem referenceMessages_satisfies
    (statement : ConstraintSystem F nw nq w Equations)
    (hlanguage : statement.Language) :
    statement.Satisfies (referenceMessages statement) := by
  classical
  simp only [referenceMessages, hlanguage, dite_true]
  exact Classical.choose_spec hlanguage

end LigeroFamily.ZeroKnowledge
