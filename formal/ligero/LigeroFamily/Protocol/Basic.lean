import LigeroFamily.Protocol.Evaluation
import Mathlib.Tactic.DeriveFintype

/-!
# Shared constraint-system and response types

This is the corrected protocol from the design discussion, expressed entirely
with evaluation rows.  The code parameters are:

* `r`: both the random-padding length in every row and the number of queried
  committed columns;
* `w`: the number of witness values carried by every row;
* `n`: the number of committed codeword columns;
* `k = r + w`: the dimension of the base code;
* `nw`: the number of linear rows;
* `nq`: the number of quadratic rows; each has `left`, `right`, and `output`
  component rows.

The response interpolation dimension is `2*k`.

-/

namespace LigeroFamily

inductive CoreBlock
  | linear
  | left
  | right
  | output
  deriving DecidableEq, Fintype

/-- Number of rows in a core block.  Linear-tableau rows and quadratic-check
rows are independent protocol dimensions. -/
def CoreBlock.rowCount (nw nq : ℕ) : CoreBlock → ℕ
  | .linear => nw
  | .left | .right | .output => nq

abbrev CoreRow (nw nq : ℕ) :=
  (block : CoreBlock) × Fin (block.rowCount nw nq)

abbrev CoreMessages (F : Type*) (nw nq w : ℕ) :=
  (block : CoreBlock) → Fin (block.rowCount nw nq) → Fin w → F

structure ConstraintSystem (F : Type*) (nw nq w : ℕ) (Equations : Type*) where
  coefficient : Equations → (block : CoreBlock) →
    Fin (block.rowCount nw nq) → Fin w → F
  target : Equations → F

namespace ConstraintSystem

variable {F Equations : Type*} [CommSemiring F] [Fintype Equations]
variable {nw nq w : ℕ}

def linearValue (statement : ConstraintSystem F nw nq w Equations)
    (messages : CoreMessages F nw nq w) (equation : Equations) : F :=
  ∑ block : CoreBlock,
    ∑ row : Fin (block.rowCount nw nq), ∑ i : Fin w,
    statement.coefficient equation block row i * messages block row i

def Satisfies (statement : ConstraintSystem F nw nq w Equations)
    (messages : CoreMessages F nw nq w) : Prop :=
  (∀ equation, statement.linearValue messages equation = statement.target equation) ∧
  ∀ (row : Fin nq) i,
    messages .left row i * messages .right row i = messages .output row i

def Language (statement : ConstraintSystem F nw nq w Equations) : Prop :=
  ∃ messages, statement.Satisfies messages

/-- Rust's `a_full`: the challenge-weighted linear coefficient at one tableau
entry. -/
def A (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) (block : CoreBlock)
    (row : Fin (block.rowCount nw nq))
    (i : Fin w) : F :=
  ∑ equation, weights equation * statement.coefficient equation block row i

def combinedTarget (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) : F :=
  ∑ equation, weights equation * statement.target equation

end ConstraintSystem

namespace ConstraintSystem

variable {F Equations : Type*} [Field F]
variable {nw nq w : ℕ}

/-- **One message vector that fails the system has a nonzero residual.**

The per-vector form.  Note what it does *not* need: that the system is unsatisfiable.  Only the
vector in hand has to fail, which is what lets the soundness stack be driven by the hypothesis
"no member of the oracle's lift list satisfies the statement" rather than by
`¬statement.Language`.  Contraposing the former produces a witness *inside a type indexed by the
oracle alone*; contraposing the latter produces only an abstract existence claim. -/
theorem residual_of_not_satisfies
    (statement : ConstraintSystem F nw nq w Equations)
    (messages : CoreMessages F nw nq w) (hnotSatisfies : ¬statement.Satisfies messages) :
    (fun equation ↦ statement.linearValue messages equation -
      statement.target equation) ≠ 0 ∨
      ∃ i, (fun row ↦ messages .left row i * messages .right row i -
        messages .output row i) ≠ 0 := by
  rcases not_and_or.mp hnotSatisfies with hlinear | hquadratic
  · left
    intro hzero
    apply hlinear
    intro equation
    exact sub_eq_zero.mp (congrFun hzero equation)
  · right
    obtain ⟨row, hrow⟩ := not_forall.mp hquadratic
    obtain ⟨i, hnonzero⟩ := not_forall.mp hrow
    refine ⟨i, ?_⟩
    intro hzero
    exact hnonzero (sub_eq_zero.mp (congrFun hzero row))

end ConstraintSystem

structure Response (F : Type*) (r w n repetitions : ℕ) where
  proximity : Fin repetitions → EvaluationRow F r w n
  linear : Fin repetitions → EvaluationRow F r w n
  quadratic : Fin repetitions → EvaluationRow F r w n
  deriving DecidableEq

@[ext] theorem Response.ext {F : Type*} {r w n repetitions : ℕ}
    {first second : Response F r w n repetitions}
    (hproximity : first.proximity = second.proximity)
    (hlinear : first.linear = second.linear)
    (hquadratic : first.quadratic = second.quadratic) : first = second := by
  cases first
  cases second
  simp_all

namespace Verifier

open MultiplicativeCode

variable {F Equations : Type*} [Field F] [Fintype Equations]
variable {r w n nw nq : ℕ}

/-- Evaluation row for one challenge-weighted constraint coefficient. -/
noncomputable def coefficientRow
    (C : MultiplicativeCode F r w n)
    (statement : ConstraintSystem F nw nq w Equations) (weights : Equations → F)
    (block : CoreBlock) (row : Fin (block.rowCount nw nq)) :
    EvaluationRow F r w n :=
  C.encode 0 (statement.A weights block row)

/-- Mask-independent linear response contributed by the committed core. -/
noncomputable def linearCore
    (C : MultiplicativeCode F r w n)
    (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F)
    (core : (block : CoreBlock) → Fin (block.rowCount nw nq) →
      EvaluationRow F r w n) : EvaluationRow F r w n :=
  ∑ block : CoreBlock, ∑ row : Fin (block.rowCount nw nq),
    rowMul (coefficientRow C statement weights block row) (core block row)

/-- Mask-independent quadratic residual contributed by the committed core. -/
noncomputable def quadraticCore
    (weights : Fin nq → F)
    (core : (block : CoreBlock) → Fin (block.rowCount nw nq) →
      EvaluationRow F r w n) : EvaluationRow F r w n :=
  ∑ row : Fin nq, weights row •
    (rowMul (core .left row) (core .right row) - core .output row)

end Verifier

end LigeroFamily
