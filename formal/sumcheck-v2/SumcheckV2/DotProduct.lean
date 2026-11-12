import SumcheckV2.Multi
import Mathlib.Tactic.LinearCombination

/-!
# Honest projective folding

Tables are monomial coefficients. The low bit splits a table into even and odd
coefficients, and binding it at `z` gives `even + z * odd`. Missing entries may
be represented by zero coefficients. No assumption on field characteristic is
needed, including for the scalar (zero-round) case.
-/

namespace SumcheckV2

variable {F : Type} [Field F]

def dot {ι : Type} [Fintype ι] (a b : ι → F) : F := ∑ i, a i * b i

def bindPair {ι : Type} (even odd : ι → F) (z : F) : ι → F :=
  fun i => even i + z * odd i

/-- `quad_round_poly` subtracts the supplied claim, including when that claim is false. -/
def roundMessage {ι : Type} [Fintype ι] (q0 q1 w0 w1 : ι → F) (claim : F) : RoundPoly F :=
  ⟨dot q0 w0, dot (bindPair q0 q1 1) (bindPair w0 w1 1) - claim⟩

theorem dot_bindPair {ι : Type} [Fintype ι] (q0 q1 w0 w1 : ι → F) (z : F) :
    check_round (dot q0 w0 + dot q1 w1)
        (roundMessage q0 q1 w0 w1 (dot q0 w0 + dot q1 w1)) z =
      dot (bindPair q0 q1 z) (bindPair w0 w1 z) := by
  simp only [check_round, RoundPoly.eval, roundMessage, dot, bindPair, one_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact update of the Rust coefficient constructor without assuming a correct incoming claim.
The discrepancy from the true folded dot product is `(z²-z) * (claim-truth)`. -/
theorem roundMessage_eval {ι : Type} [Fintype ι]
    (q0 q1 w0 w1 : ι → F) (claim z : F) :
    check_round claim (roundMessage q0 q1 w0 w1 claim) z =
      dot (bindPair q0 q1 z) (bindPair w0 w1 z) +
        (z ^ 2 - z) * (claim - (dot q0 w0 + dot q1 w1)) := by
  have h := dot_bindPair q0 q1 w0 w1 z
  simp only [check_round, RoundPoly.eval, roundMessage] at h ⊢
  linear_combination h

/-- Low bit first, matching the order in which dense arrays are folded. -/
def Cube : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × Cube n

instance cubeFintype : (n : ℕ) → Fintype (Cube n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 =>
      letI := cubeFintype n
      inferInstanceAs (Fintype (Bool × Cube n))

def even {n : ℕ} (q : Cube (n + 1) → F) : Cube n → F := fun i => q (false, i)
def odd {n : ℕ} (q : Cube (n + 1) → F) : Cube n → F := fun i => q (true, i)
def fold {n : ℕ} (q : Cube (n + 1) → F) (z : F) : Cube n → F :=
  bindPair (even q) (odd q) z

theorem dot_split {n : ℕ} (q w : Cube (n + 1) → F) :
    dot q w = dot (even q) (even w) + dot (odd q) (odd w) := by
  change (∑ i : Bool × Cube n, q i * w i) = _
  rw [Fintype.sum_prod_type]
  simp [dot, even, odd, add_comm]

def honestMessage {n : ℕ} (q w : Cube (n + 1) → F) : RoundPoly F :=
  roundMessage (even q) (odd q) (even w) (odd w) (dot q w)

/-- The runtime constructor specializes to the honest message under its incoming invariant. -/
theorem roundMessage_eq_honestMessage {n : ℕ} (q w : Cube (n + 1) → F) (claim : F)
    (hclaim : claim = dot q w) :
    roundMessage (even q) (odd q) (even w) (odd w) claim = honestMessage q w := by
  rw [hclaim]
  rfl

theorem honest_round {n : ℕ} (q w : Cube (n + 1) → F) (z : F) :
    check_round (dot q w) (honestMessage q w) z = dot (fold q z) (fold w z) := by
  unfold honestMessage
  rw [dot_split]
  exact dot_bindPair _ _ _ _ z

/-- Evaluate a monomial coefficient table by successive low-bit bindings. -/
def evaluate : {n : ℕ} → (Cube n → F) → (Fin n → F) → F
  | 0, q, _ => q ()
  | _ + 1, q, u => evaluate (fold q (u 0)) (fun j => u j.succ)

def monomialWeights : {n : ℕ} → (Fin n → F) → Cube n → F
  | 0, _, _ => 1
  | _ + 1, u, (bit, i) =>
      (if bit then u 0 else 1) * monomialWeights (fun j => u j.succ) i

theorem evaluate_eq_dot {n : ℕ} (q : Cube n → F) (u : Fin n → F) :
    evaluate q u = dot (monomialWeights u) q := by
  induction n with
  | zero => simp [evaluate, dot, Cube, monomialWeights]
  | succ n ih =>
      rw [evaluate, ih, dot_split]
      simp only [dot, even, odd, monomialWeights, Bool.false_eq_true, if_false,
        one_mul, if_true, fold, bindPair, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

def honestMessages : {n : ℕ} → (Cube n → F) → (Cube n → F) → (Fin n → F) →
    List (RoundPoly F)
  | 0, _, _, _ => []
  | _ + 1, q, w, u => honestMessage q w ::
      honestMessages (fold q (u 0)) (fold w (u 0)) (fun j => u j.succ)

/-- All honest rounds end in the product of the two folded scalars. -/
theorem honest_completeness {n : ℕ} (q w : Cube n → F) (u : Fin n → F) :
    verify_multi_round (dot q w) (honestMessages q w u) (List.ofFn u) =
      some (evaluate q u * evaluate w u) := by
  induction n with
  | zero => simp [honestMessages, dot, Cube, evaluate]
  | succ n ih =>
      rw [honestMessages, List.ofFn_succ, verify_multi_round, honest_round, ih]
      rfl

/-- True round polynomials for applying the deterministic soundness reduction. -/
noncomputable def truePolys : {n : ℕ} → (Cube n → F) → (Cube n → F) → (Fin n → F) →
    List (Polynomial F)
  | 0, _, _, _ => []
  | _ + 1, q, w, u => (honestMessage q w).toPoly (dot q w) ::
      truePolys (fold q (u 0)) (fold w (u 0)) (fun j => u j.succ)

theorem truePolys_consistent {n : ℕ} (q w : Cube n → F) (u : Fin n → F) :
    Consistent (dot q w) (truePolys q w u) (List.ofFn u) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      rw [truePolys, List.ofFn_succ, Consistent]
      constructor
      · exact RoundPoly.projectiveSum_toPoly _ _
      · rw [RoundPoly.eval_toPoly]
        change Consistent (check_round (dot q w) (honestMessage q w) (u 0)) _ _
        rw [honest_round]
        exact ih _ _ _

theorem truePolys_degree {n : ℕ} (q w : Cube n → F) (u : Fin n → F) :
    ∀ P ∈ truePolys q w u, P.natDegree ≤ 2 := by
  induction n with
  | zero => simp [truePolys]
  | succ n ih =>
      intro P hP
      rcases List.mem_cons.mp hP with rfl | hP
      · exact RoundPoly.toPoly_natDegree _ _
      · exact ih _ _ _ P hP

theorem truePolys_final {n : ℕ} (q w : Cube n → F) (u : Fin n → F) :
    true_final (dot q w) (truePolys q w u) (List.ofFn u) =
      some (evaluate q u * evaluate w u) := by
  induction n with
  | zero => simp [truePolys, true_final, dot, Cube, evaluate]
  | succ n ih =>
      rw [truePolys, List.ofFn_succ, true_final, RoundPoly.eval_toPoly]
      change true_final (check_round (dot q w) (honestMessage q w) (u 0)) _ _ = _
      rw [honest_round, ih]
      rfl

/-- A false dot-product claim cannot reach the true terminal product without a bad round. -/
theorem dot_product_reduction {n : ℕ} (q w : Cube n → F) (u : Fin n → F)
    (claim : F) (messages : List (RoundPoly F)) (hfalse : claim ≠ dot q w)
    (hverify : verify_multi_round claim messages (List.ofFn u) =
      some (evaluate q u * evaluate w u)) :
    multi_round_bad_event claim (truePolys q w u) messages (List.ofFn u) :=
  sumcheck_multi_reduction _ _ _ _ _ _ (truePolys_consistent q w u) hverify
    (truePolys_final q w u) hfalse

end SumcheckV2
