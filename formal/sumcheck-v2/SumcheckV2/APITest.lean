import SumcheckV2
import SumcheckV1
import Mathlib.Data.ZMod.Basic

/-!
API checks for both libraries together, the projective convention, scalar layers,
characteristic two, and the product-slot boundary. All examples are kernel-checked.
-/

namespace SumcheckV2.APITest

open Classical SumcheckV2

local instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩

-- The projective sum is 31; the affine endpoint sum would be 70.
example : check_round (31 : ZMod 101) ⟨10, 29⟩ 4 = 58 := by
  norm_num [check_round, RoundPoly.eval]
  decide

-- Coefficient transmission needs no third interpolation node, even over F₂.
example (P : Polynomial (ZMod 2)) (h : P.natDegree ≤ 2) :
    (RoundPoly.ofPoly P).toPoly (projectiveSum P) = P :=
  RoundPoly.toPoly_ofPoly P h

-- In F₂ the bound of two roots can be attained: a false claim repairs at both challenges.
example : BadRoundEvent (0 : Polynomial (ZMod 2)) ⟨0, 1⟩ 1 0 := by
  norm_num [BadRoundEvent, projectiveSum, check_round, RoundPoly.eval]

example : BadRoundEvent (0 : Polynomial (ZMod 2)) ⟨0, 1⟩ 1 1 := by
  norm_num [BadRoundEvent, projectiveSum, check_round, RoundPoly.eval]
  decide

example : BadCombineEvent (2 : ZMod 101) 3 5 7 75 := by
  norm_num [BadCombineEvent]
  decide

example : ¬ BadCombineEvent (2 : ZMod 101) 3 5 7 0 := by
  norm_num [BadCombineEvent]
  decide

section ArbitraryField

variable {F : Type} [Field F]

-- Rust subtracts the supplied claim: q = w = [1,0], false claim 0 gives [1,1].
-- Substituting the true dot product instead would give [1,0].
example : roundMessage (F := F) (ι := Unit)
    (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0) 0 = ⟨1, 1⟩ := by
  simp [roundMessage, dot, bindPair]

example : roundMessage (F := F) (ι := Unit)
    (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0) 1 = ⟨1, 0⟩ := by
  simp [roundMessage, dot, bindPair]

-- Scalar tables execute no rounds and still end in the terminal product.
example (q w : F) :
    verify_multi_round (q * w)
        (honestMessages (n := 0) (fun _ => q) (fun _ => w) Fin.elim0) [] =
      some (q * w) := rfl

-- Round/challenge count mismatches reject, in either direction.
example (claim z : F) : verify_multi_round claim [] [z] = none := rfl
example (claim : F) (p : RoundPoly F) : verify_multi_round claim [p] [] = none := rfl

-- The single-hand reduction combines the two claims on the same witness table.
example {n : ℕ} (K : Cube n → Cube n → F) (w : Cube n → F)
    (u : Fin n → F) (alpha : F) :
    evaluate w u + alpha * evaluate (bindRight K w) u =
      dot (nextWeights K (monomialWeights u) alpha) w :=
  (layer_completeness K w u alpha).2

-- Repeated pad names are meaningful: the sparse expression adds all their coefficients.
example (e : PadExpression Unit F) (m : RoundPoly F) (z pad : F) :
    (e.round m z () ()).eval (fun _ => pad) =
      check_round (e.eval (fun _ => pad)) (unmask m ⟨pad, pad⟩) z :=
  PadExpression.eval_round e m z () () (fun _ => pad)

-- Removing product consistency would make an affine row accept a false terminal product.
example :
    ((⟨0, []⟩ : PadExpression Unit F).subtractClaimProduct 0 0 () ()).eval
        (fun _ => 1) - 0 = 0 ∧
      ¬ (0 : F) = (0 + 1) * (0 + 1) := by
  simp [PadExpression.eval, PadExpression.subtractClaimProduct]

-- A round followed by a final-claim combination has budget 2 + 1, not 2 + 2.
example [Fintype F] [DecidableEq F]
    (strategy : LayerStrategy F ![ChallengeKind.round, ChallengeKind.combine])
    (hvalid : ∀ i pref, (strategy i pref).Valid) :
    (Finset.univ.filter fun cs : Fin 2 → F => layer_bad_event strategy cs).card ≤
      3 * Fintype.card F := by
  simpa [Fin.sum_univ_two, ChallengeKind.budget] using
    layer_tape_card_le ![ChallengeKind.round, ChallengeKind.combine] strategy hvalid

-- Round-only callers use the same strategy data as mixed layer tapes.
example [Fintype F] [DecidableEq F] (strategy : RoundStrategy F 2)
    (hvalid : ∀ i pref, ChallengeData.Valid (strategy i pref)) :
    (Finset.univ.filter fun cs : Fin 2 → F => layer_bad_event strategy cs).card ≤
      4 * Fintype.card F := by
  simpa using combinatorial_fiat_shamir strategy hvalid

end ArbitraryField

#guard_msgs (drop info) in #check Chained.ofRoundReplay
#guard_msgs (drop info) in #check Chained.failure_bound
#guard_msgs (drop info) in #check selected_round_bad_card_le

/--
info: 'SumcheckV2.Chained.ofRoundReplay' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Chained.ofRoundReplay
/--
info: 'SumcheckV2.Chained.failure_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Chained.failure_bound
/--
info: 'SumcheckV2.selected_round_bad_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms selected_round_bad_card_le

-- Both protocol namespaces coexist; v1 still carries its interpolation premise.
example {F : Type} [Field F] [DecidableEq F] [SumcheckV1.Interp F 2]
    (p : SumcheckV1.RoundPoly F 2) (z : F) :
    p.toPoly.eval z = p.eval_lagrange z := SumcheckV1.RoundPoly.eval_toPoly p z

-- Empty tapes have no bad events, including an execution with no circuit layers.
example {F : Type} [Field F] (strategy : LayerStrategy F (n := 0) Fin.elim0)
    (cs : Fin 0 → F) : ¬ layer_bad_event strategy cs := by
  rintro ⟨i, _⟩
  exact Fin.elim0 i

end SumcheckV2.APITest
