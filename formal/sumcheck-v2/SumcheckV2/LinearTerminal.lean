import SumcheckV2.Affine
import SumcheckV2.Masked

/-!
# The randomized affine terminal

The four cells `pA`, `pB`, `pAB`, and `pD` are committed before sumcheck.
The cross message precedes the nonzero scale; the two masked claims precede
the combining challenge. In soundness, `pAB` is an arbitrary committed cell.
Only completeness uses its honest value `pA * pB`.

This is the terminal used by Rust commit `21cb029`. The earlier product-slot
terminal remains available for the separate Step4 checkpoint.
-/

namespace SumcheckV2.LinearTerminal

open Classical Polynomial

variable {F Pad : Type} [Field F]

structure Pads (F : Type) where
  a : F
  b : F
  ab : F
  d : F

/-- Data fixed before the terminal scale is sampled. Neither final masked
claim occurs here: those messages may depend on the scale. -/
structure Data (F : Type) where
  claim : F
  trueA : F
  trueB : F
  cross : F
  pads : Pads F

def residual (claim cross scale messageA messageB : F) (pads : Pads F) : F :=
  claim + scale * (cross + pads.d) + scale ^ 2 * pads.ab - messageA * messageB

def clearA (message scale : F) (pads : Pads F) : F := message - scale * pads.a
def clearB (message scale : F) (pads : Pads F) : F := message - scale * pads.b

noncomputable def Data.error (data : Data F) : Polynomial F :=
  C (data.claim - data.trueA * data.trueB) +
    C (data.cross + data.pads.d - data.trueA * data.pads.b - data.trueB * data.pads.a) * X +
    C (data.pads.ab - data.pads.a * data.pads.b) * X ^ 2

theorem Data.eval_error (data : Data F) (scale : F) :
    data.error.eval scale =
      residual data.claim data.cross scale
        (data.trueA + scale * data.pads.a) (data.trueB + scale * data.pads.b) data.pads := by
  simp only [Data.error, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, residual]
  ring

theorem Data.error_natDegree (data : Data F) : data.error.natDegree ≤ 2 := by
  apply Polynomial.natDegree_le_iff_degree_le.mpr
  apply Polynomial.degree_add_le_of_degree_le
  · apply Polynomial.degree_add_le_of_degree_le
    · exact (Polynomial.degree_C_le).trans (by norm_num)
    · exact (Polynomial.degree_mul_le _ _).trans (by
        calc
          _ ≤ 0 + 1 := add_le_add Polynomial.degree_C_le (by simp)
          _ ≤ 2 := by norm_num)
  · exact (Polynomial.degree_mul_le _ _).trans (by
      calc
        _ ≤ 0 + 2 := add_le_add Polynomial.degree_C_le (by simp)
        _ ≤ 2 := by norm_num)

theorem Data.error_ne_zero (data : Data F) (hfalse : data.claim ≠ data.trueA * data.trueB) :
    data.error ≠ 0 := by
  intro h
  have hzero := congrArg (fun p : Polynomial F => p.eval 0) h
  exact hfalse (by simpa [Data.error, sub_eq_zero] using hzero)

/-- A false terminal claim is repaired at a root of a fixed quadratic. -/
def Data.Bad (data : Data F) (scale : F) : Prop :=
  data.claim ≠ data.trueA * data.trueB ∧ data.error.eval scale = 0

theorem Data.bad_roots [Fintype F] [DecidableEq F] (data : Data F) :
    (Finset.univ.filter data.Bad).card ≤ 2 := by
  by_cases hfalse : data.claim ≠ data.trueA * data.trueB
  · have hsubset : (Finset.univ.filter data.Bad) ⊆ data.error.roots.toFinset := by
      intro z hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (data.error_ne_zero hfalse)]
      exact (Finset.mem_filter.mp hz).2.2
    calc
      _ ≤ data.error.roots.toFinset.card := Finset.card_le_card hsubset
      _ ≤ data.error.roots.card := Multiset.toFinset_card_le _
      _ ≤ data.error.natDegree := Polynomial.card_roots' _
      _ ≤ 2 := data.error_natDegree
  · simp [Data.Bad, hfalse]

/-- Restricting the challenge to nonzero elements preserves the two-root bound.
The probability denominator is the size of this restricted challenge space. -/
theorem Data.bad_nonzero_roots [Fintype F] [DecidableEq F] (data : Data F) :
    (Finset.univ.filter fun scale : {z : F // z ≠ 0} => data.Bad scale.val).card ≤ 2 := by
  calc
    _ ≤ (Finset.univ.filter data.Bad).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro z hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
      · intro x _ y _ h
        exact Subtype.ext h
    _ ≤ 2 := data.bad_roots

/-- The authenticated terminal equation reduces either to the true product,
a terminal root event, or a wrong pair of recovered final claims. -/
theorem reduction (data : Data F) (scale messageA messageB : F)
    (hrow : residual data.claim data.cross scale messageA messageB data.pads = 0)
    (hfalse : data.claim ≠ data.trueA * data.trueB)
    (hpair : clearA messageA scale data.pads = data.trueA ∧
      clearB messageB scale data.pads = data.trueB) : data.Bad scale := by
  refine ⟨hfalse, ?_⟩
  rw [data.eval_error]
  have hA : messageA = data.trueA + scale * data.pads.a :=
    sub_eq_iff_eq_add.mp hpair.1
  have hB : messageB = data.trueB + scale * data.pads.b :=
    sub_eq_iff_eq_add.mp hpair.2
  simpa only [hA, hB] using hrow

theorem completeness (A B pA pB pD scale : F) :
    residual (A * B) (A * pB + B * pA - pD) scale
      (A + scale * pA) (B + scale * pB) ⟨pA, pB, pA * pB, pD⟩ = 0 := by
  unfold residual
  ring

/-- Affine rows contain the cross pad and candidate product as ordinary cells;
there is no product-constraint premise in their interpretation. -/
def row (claim : PadExpression Pad F) (cross scale messageA messageB : F)
    (pAB pD : Pad) : PadExpression Pad F where
  constant := claim.constant + scale * cross - messageA * messageB
  terms := claim.terms ++ [(pD, scale), (pAB, scale ^ 2)]

theorem eval_row (claim : PadExpression Pad F) (cross scale messageA messageB : F)
    (pA pB pAB pD : Pad) (pads : Pad → F) :
    (row claim cross scale messageA messageB pAB pD).eval pads =
      residual (claim.eval pads) cross scale messageA messageB
        ⟨pads pA, pads pB, pads pAB, pads pD⟩ := by
  simp only [row, PadExpression.eval, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, residual]
  ring

def nextClaim (messageA messageB scale alpha linear : F) (pA pB : Pad) :
    PadExpression Pad F where
  constant := messageA + alpha * messageB - alpha * linear
  terms := [(pA, -scale), (pB, -(alpha * scale))]

theorem eval_nextClaim (messageA messageB scale alpha linear : F)
    (pA pB pAB pD : Pad) (pads : Pad → F) :
    (nextClaim messageA messageB scale alpha linear pA pB).eval pads =
      clearA messageA scale ⟨pads pA, pads pB, pads pAB, pads pD⟩ +
        alpha * (clearB messageB scale ⟨pads pA, pads pB, pads pAB, pads pD⟩ - linear) := by
  simp only [nextClaim, PadExpression.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, clearA, clearB]
  ring

/-- False claims propagate through ordinary quadratic rounds, this randomized
terminal, and the existing linear combination. Public affine corrections are
included exactly as in the native circuit implementation. -/
theorem affine_layer_reduction {n : ℕ}
    (Q : Cube n → Cube n → F) (L w : Cube n → F) (K : F) (u : Fin n → F)
    (claim terminal cross scale messageA messageB alpha : F) (pads : Pads F)
    (messages : List (RoundPoly F))
    (hfalse : claim ≠ dot (bindRightAffine Q L w) w + K)
    (hrounds : verify_multi_round (claim - K) messages (List.ofFn u) = some terminal)
    (hrow : residual terminal cross scale messageA messageB pads = 0)
    (hnext : clearA messageA scale pads + alpha * (clearB messageB scale pads - evaluate L u) =
      dot (nextWeights Q (monomialWeights u) alpha) w) :
    multi_round_bad_event (claim - K) (truePolys (bindRightAffine Q L w) w u)
        messages (List.ofFn u) ∨
      (Data.mk terminal (evaluate w u) (evaluate (bindRightAffine Q L w) u) cross pads).Bad scale ∨
      BadCombineEvent (evaluate w u) (evaluate (bindRightAffine Q L w) u)
        (clearA messageA scale pads) (clearB messageB scale pads) alpha := by
  by_cases hpair : clearA messageA scale pads = evaluate w u ∧
      clearB messageB scale pads = evaluate (bindRightAffine Q L w) u
  · by_cases hterminal : terminal = evaluate w u * evaluate (bindRightAffine Q L w) u
    · left
      apply dot_product_reduction (bindRightAffine Q L w) w u (claim - K) messages
      · intro h
        exact hfalse (sub_eq_iff_eq_add.mp h)
      · simpa [hterminal, mul_comm] using hrounds
    · exact Or.inr (Or.inl (reduction _ _ _ _ hrow hterminal hpair))
  · right; right
    refine ⟨by tauto, ?_⟩
    rw [affine_nextWeights_correct Q L (monomialWeights u) w alpha] at hnext
    simp only [← evaluate_eq_dot] at hnext
    linear_combination hnext

end SumcheckV2.LinearTerminal
