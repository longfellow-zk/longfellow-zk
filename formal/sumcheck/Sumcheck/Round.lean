import Sumcheck.Interp

/-!
# One sumcheck round

The verifier's per-round step, and the single-round soundness reduction it rests on: from a
**false** incoming claim, either the outgoing claim is false too, or the prover was lucky at this
round's challenge.

`check_round_c` is the whole of the verifier's per-round work — test `p(0) + p(1) = claim`, then
carry `p(r)` forward.  Nothing here depends on `d` beyond the two pinned nodes, so a degree-3
copy round and a degree-2 hand round run the same code and the same proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Sumcheck

open Polynomial

variable {F : Type} [Field F] [DecidableEq F] {d : ℕ} [Interp F d]

/--
`check_round_c` formalizes `VerifierLayers::layer_c` (line 84 in `verifier_layers.h`).
It checks sum consistency `p(0) + p(1) == claim` and returns the next claim `p(r)`.
- **Code Reference**: `privacy/proofs/zk/lib/sumcheck/verifier_layers.h:L84-L98`
-/
def check_round_c (claim_in : F) (poly : RoundPoly F d) (r : F) : Option F :=
  if poly.eval0 + poly.eval1 == claim_in then
    some (poly.eval_lagrange r)
  else
    none

/--
Theorem: `check_round_c_consistency`
Proves that if `check_round_c` succeeds, the next claim is uniquely determined by `poly.eval_lagrange r`.
-/
theorem check_round_c_consistency (claim_in : F) (poly : RoundPoly F d) (r : F) (claim_out : F) :
    check_round_c claim_in poly r = some claim_out →
    claim_out = poly.eval_lagrange r ∧ poly.eval0 + poly.eval1 = claim_in := by
  intro h
  dsimp [check_round_c] at h
  split_ifs at h with h_eq
  injection h with h_out
  rw [beq_iff_eq] at h_eq
  exact ⟨h_out.symm, h_eq⟩


/-!
===============================================================================
Single-Round Schwartz-Zippel Soundness Bound
===============================================================================
Formalizes the fundamental single-round soundness lemma of sumcheck:
If an input claim `claim_in` is FALSE (i.e. `claim_in ≠ P_true 0 + P_true 1`),
a prover attempting to pass the round check `poly.eval0 + poly.eval1 == claim_in`
must submit a polynomial `poly` that differs from `P_true`.

By the Schwartz-Zippel Lemma, two distinct degree-`d` polynomials over field `F`
can agree at most at `d` points. Thus, the number of challenge points `r`
satisfying `poly.eval_lagrange r = P_true r` is at most `d`.
-/


omit [Interp F d] in
/--
Proves that if an input claim is false (`claim_in ≠ P_true 0 + P_true 1`) and the prover's
`RoundPoly` passes the sum-consistency check (`poly.eval0 + poly.eval1 = claim_in`), then
`poly` cannot be identical to `P_true` at both 0 and 1.
-/
theorem false_claim_implies_poly_mismatch (P_true : Polynomial F) (poly : RoundPoly F d) (claim_in : F)
    (h_false : claim_in ≠ P_true.eval 0 + P_true.eval 1)
    (h_check : poly.eval0 + poly.eval1 = claim_in) :
    poly.eval0 ≠ P_true.eval 0 ∨ poly.eval1 ≠ P_true.eval 1 := by
  by_contra h_contra
  push Not at h_contra
  have h_sum : poly.eval0 + poly.eval1 = P_true.eval 0 + P_true.eval 1 := by
    rw [h_contra.1, h_contra.2]
  rw [h_sum] at h_check
  exact h_false h_check.symm

theorem sumcheck_step_reduction {F : Type} [Field F] [DecidableEq F] {d : ℕ} [Interp F d]
    (P_true : Polynomial F) (poly : RoundPoly F d) (claim_in claim_out r : F)
    (h_check : check_round_c claim_in poly r = some claim_out)
    (h_false : claim_in ≠ P_true.eval 0 + P_true.eval 1) :
    claim_out ≠ P_true.eval r ∨ (poly.eval0 ≠ P_true.eval 0 ∨ poly.eval1 ≠ P_true.eval 1) ∧ (poly.eval_lagrange r = P_true.eval r) := by
  dsimp [check_round_c] at h_check
  split at h_check
  · next h_eq =>
    simp only [Option.some.injEq] at h_check
    have h_eq2 : poly.eval0 + poly.eval1 = claim_in := eq_of_beq h_eq
    have h_mismatch := false_claim_implies_poly_mismatch P_true poly claim_in h_false h_eq2
    by_cases h_out : claim_out = P_true.eval r
    · right
      constructor
      · exact h_mismatch
      · rw [h_check, h_out]
    · left
      exact h_out
  · next h_neq =>
    contradiction

def BadRoundEvent {F : Type} [Field F] {d : ℕ} [Interp F d] (P_true : Polynomial F) (poly : RoundPoly F d) (r : F) : Prop :=
  (poly.eval0 ≠ P_true.eval 0 ∨ poly.eval1 ≠ P_true.eval 1) ∧ poly.eval_lagrange r = P_true.eval r

end Sumcheck
