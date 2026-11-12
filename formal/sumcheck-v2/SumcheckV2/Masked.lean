import SumcheckV2.DotProduct

/-!
# Masked messages and symbolic constraints

This is the algebra of `sumcheck-v2/src/symbolic.rs`. Pads are subtracted from
messages and added back when interpreting the claim. Sparse affine terms are
lists, so repeated pad identifiers and zero coefficients retain their meaning.
The terminal product can be lowered to an affine row only when the committed
product slot is separately constrained to equal the product of the two pads.
-/

namespace SumcheckV2

variable {F Pad : Type} [Field F]

def mask (p pads : RoundPoly F) : RoundPoly F := ⟨p.c0 - pads.c0, p.c1 - pads.c1⟩
def unmask (m pads : RoundPoly F) : RoundPoly F := ⟨m.c0 + pads.c0, m.c1 + pads.c1⟩

@[simp] theorem unmask_mask (p pads : RoundPoly F) : unmask (mask p pads) pads = p := by
  cases p
  simp [mask, unmask]

structure PadExpression (Pad F : Type) where
  constant : F
  terms : List (Pad × F)

namespace PadExpression

def eval (e : PadExpression Pad F) (pads : Pad → F) : F :=
  e.constant + (e.terms.map fun t => t.2 * pads t.1).sum

def round (e : PadExpression Pad F) (m : RoundPoly F) (z : F) (p0 p1 : Pad) :
    PadExpression Pad F where
  constant := z ^ 2 * e.constant + (1 - z ^ 2) * m.c0 + z * m.c1
  terms := (e.terms.map fun t => (t.1, z ^ 2 * t.2)) ++ [(p0, 1 - z ^ 2), (p1, z)]

/-- Scaling the old pad terms and appending the two new ones evaluates to the clear round. -/
theorem eval_round (e : PadExpression Pad F) (m : RoundPoly F) (z : F)
    (p0 p1 : Pad) (pads : Pad → F) :
    (e.round m z p0 p1).eval pads =
      check_round (e.eval pads) (unmask m ⟨pads p0, pads p1⟩) z := by
  simp only [eval, round, List.map_append, List.sum_append, List.map_map,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_def,
    mul_assoc, List.sum_map_mul_left, check_round, RoundPoly.eval, unmask]
  ring

def subtractClaimProduct (e : PadExpression Pad F) (mA mB : F) (pA pB : Pad) :
    PadExpression Pad F where
  constant := e.constant - mA * mB
  terms := e.terms ++ [(pA, -mB), (pB, -mA)]

/-- The implicit pad-product term completes exactly the terminal product residual. -/
theorem eval_subtractClaimProduct (e : PadExpression Pad F) (mA mB : F)
    (pA pB : Pad) (pads : Pad → F) :
    (e.subtractClaimProduct mA mB pA pB).eval pads - pads pA * pads pB =
      e.eval pads - (mA + pads pA) * (mB + pads pB) := by
  simp only [eval, subtractClaimProduct, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- The product-slot consistency premise is required by the constraint compiler. -/
theorem lowered_terminal_iff (e : PadExpression Pad F) (mA mB productSlot : F)
    (pA pB : Pad) (pads : Pad → F) (hproduct : productSlot = pads pA * pads pB) :
    (e.subtractClaimProduct mA mB pA pB).eval pads - productSlot = 0 ↔
      e.eval pads = (mA + pads pA) * (mB + pads pB) := by
  rw [hproduct, eval_subtractClaimProduct, sub_eq_zero]

def claimNext (mA mB alpha : F) (pA pB : Pad) : PadExpression Pad F where
  constant := mA + alpha * mB
  terms := [(pA, 1), (pB, alpha)]

theorem eval_claimNext (mA mB alpha : F) (pA pB : Pad) (pads : Pad → F) :
    (claimNext mA mB alpha pA pB).eval pads =
      (mA + pads pA) + alpha * (mB + pads pB) := by
  simp only [eval, claimNext, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- Each message is accompanied by the two logical pad identifiers used by the builder. -/
def rounds (e : PadExpression Pad F) : List (RoundPoly F × Pad × Pad) → List F →
    Option (PadExpression Pad F)
  | [], [] => some e
  | (m, p0, p1) :: ms, z :: zs => rounds (e.round m z p0 p1) ms zs
  | _, _ => none

/-- Symbolic execution agrees with numerical execution for the entire round sequence. -/
theorem eval_rounds (e : PadExpression Pad F) (ms : List (RoundPoly F × Pad × Pad))
    (zs : List F) (pads : Pad → F) :
    ((e.rounds ms zs).map fun out => out.eval pads) =
      verify_multi_round (e.eval pads)
        (ms.map fun (m, p0, p1) => unmask m ⟨pads p0, pads p1⟩) zs := by
  induction ms generalizing e zs with
  | nil => cases zs <;> rfl
  | cons entry ms ih =>
      rcases entry with ⟨m, p0, p1⟩
      cases zs with
      | nil => rfl
      | cons z zs =>
          simp only [rounds, List.map_cons, verify_multi_round]
          rw [ih, eval_round]

/-- The compiler moves public input terms to the constant and emits negative private-input
coefficients. The sum type describes the public/private partition, not physical witness indices. -/
theorem input_constraint_eq {Public Private : Type} [Fintype Public] [Fintype Private]
    (e : PadExpression Pad F) (pads : Pad → F)
    (publicWeights publicInputs : Public → F) (privateWeights privateInputs : Private → F) :
    (e.constant - dot publicWeights publicInputs) +
        (e.terms.map fun t => t.2 * pads t.1).sum +
        dot (fun i => -privateWeights i) privateInputs =
      e.eval pads - dot (Sum.elim publicWeights privateWeights)
        (Sum.elim publicInputs privateInputs) := by
  simp only [eval, dot, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib]
  ring

/-- The compiled final-input row is zero exactly when the claim equals the full input sum. -/
theorem input_constraint_iff {Public Private : Type} [Fintype Public] [Fintype Private]
    (e : PadExpression Pad F) (pads : Pad → F)
    (publicWeights publicInputs : Public → F) (privateWeights privateInputs : Private → F) :
    (e.constant - dot publicWeights publicInputs) +
        (e.terms.map fun t => t.2 * pads t.1).sum +
        dot (fun i => -privateWeights i) privateInputs = 0 ↔
      e.eval pads = dot (Sum.elim publicWeights privateWeights)
        (Sum.elim publicInputs privateInputs) := by
  rw [input_constraint_eq, sub_eq_zero]

end PadExpression

end SumcheckV2
