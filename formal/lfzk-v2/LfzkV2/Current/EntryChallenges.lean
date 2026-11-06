import LfzkV2.Layered.Entry
import LfzkV2.ChallengeBlocks
import SumcheckV2.LinearTerminal

/-! Local algebra for sampling entering outputs together with an existing
challenge block. The Rust layer assertion block samples entering output coefficients first,
then quadratic and linear assertion coefficients from the same answer.

Both blocks below are single affine tests of a full uniform coefficient
vector. All offsets and residuals must be fixed before that answer is read.
In particular, an earlier prover message cannot depend on an entry coefficient
that has not yet been sampled. -/
namespace LfzkV2.Current.EntryChallenges
open SumcheckV2 Finset
open scoped Classical

variable {F Old New Wire : Type} [Field F]
  [Fintype Old] [Fintype New] [Fintype Wire]

theorem dot_append {n m : ℕ} (a x : Fin n → F) (b y : Fin m → F) :
    dot (Fin.append a b) (Fin.append x y) = dot a x + dot b y := by
  simp [dot, Fin.sum_univ_add]

/-- Entering output residuals and all layer assertions form one linear check,
even when the entry maps overlap at the common input array. -/
theorem entry_assertion_truth {n m : ℕ}
    (e : Layered.Entry Old New n) (body : LfzkV2.Native.CircuitLayer New Wire (Fin m) F)
    (a : Old → F) (rho : Fin n → F) (beta : Fin m → F) (w : Wire → F) :
    dot (e.weights a rho) (body.outputs w) + dot beta (body.residuals w) =
      dot a (e.previous (body.outputs w)) +
        dot (Fin.append rho beta)
          (Fin.append (e.residuals (body.outputs w)) (body.residuals w)) := by
  rw [e.dot_weights, dot_append]
  ring

/-- A repaired false entry or assertion is charged to the combined block,
with no union over its two parts or over quad fragments. -/
theorem entry_assertion_reduction {n m : ℕ}
    (e : Layered.Entry Old New n) (body : LfzkV2.Native.CircuitLayer New Wire (Fin m) F)
    (a : Old → F) (rho : Fin n → F) (beta : Fin m → F) (w : Wire → F) (claim : F)
    (hfalse : (∃ i, e.residuals (body.outputs w) i ≠ 0) ∨
      (∃ i, body.residuals w i ≠ 0))
    (hclaim : claim = dot (e.weights a rho) (body.outputs w) + dot beta (body.residuals w)) :
    AssertionBad (dot a (e.previous (body.outputs w))) claim (Fin.append rho beta)
      (Fin.append (e.residuals (body.outputs w)) (body.residuals w)) := by
  apply assertion_reduction
  · rcases hfalse with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact ⟨i.castAdd m, by simpa using hi⟩
    · exact ⟨i.natAdd n, by simpa using hi⟩
  · exact hclaim.trans (entry_assertion_truth e body a rho beta w)

/-- Adding input-level entries to the last combine answer is also a single
affine check. The linear correction cancels before this identity is used. -/
theorem combine_entry_error {n : ℕ} (A B trueA trueB linear alpha : F)
    (rho values : Fin n → F) :
    (A + alpha*(B-linear)) - (trueA + alpha*(trueB-linear) + dot rho values) =
      (A-trueA) + dot (Fin.cons alpha rho)
        (Fin.cons (B-trueB) (fun i => -values i)) := by
  simp only [dot, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_neg,
    Finset.sum_neg_distrib]
  ring

theorem combine_entry_reduction {n : ℕ} (A B trueA trueB linear alpha : F)
    (rho values : Fin n → F)
    (hfalse : A ≠ trueA ∨ B ≠ trueB ∨ ∃ i, values i ≠ 0)
    (hnext : A + alpha*(B-linear) = trueA + alpha*(trueB-linear) + dot rho values) :
    AssertionBad (A-trueA) 0 (Fin.cons alpha rho)
      (Fin.cons (B-trueB) (fun i => -values i)) := by
  have heq := combine_entry_error A B trueA trueB linear alpha rho values
  rw [hnext, sub_self] at heq
  have hnonzero : ∃ i : Fin (n+1),
      (Fin.cons (B-trueB) (fun i : Fin n => -values i) : Fin (n+1) → F) i ≠ 0 := by
    by_contra h
    have hz : ∀ i : Fin (n+1),
        (Fin.cons (B-trueB) (fun i : Fin n => -values i) : Fin (n+1) → F) i = 0 := by
      simpa using h
    have hB : B = trueB := sub_eq_zero.mp (by simpa using hz 0)
    have hv : ∀ i, values i = 0 := by
      intro i
      exact neg_eq_zero.mp (by simpa using hz i.succ)
    have hA : A = trueA := by
      have ha : A-trueA = 0 := by simpa [dot, hz] using heq.symm
      exact sub_eq_zero.mp ha
    rcases hfalse with hA' | hB' | ⟨i, hi⟩
    · exact hA' hA
    · exact hB' hB
    · exact hi (hv i)
  exact assertion_reduction _ _ _ _ hnonzero heq

/-- The last actual layer and input-only output checks share one combine
answer. A false dot-product claim reaching an authenticated final input row
therefore needs a quadratic round root, a terminal root, or the single affine
combine/entry event above. Product pads remain arbitrary committed cells. -/
theorem last_layer_reduction {rounds n : ℕ}
    (Q : Cube rounds → Cube rounds → F) (L w : Cube rounds → F)
    (K : F) (u : Fin rounds → F)
    (claim terminal cross scale messageA messageB alpha : F)
    (pads : LinearTerminal.Pads F) (messages : List (RoundPoly F))
    (rho values : Fin n → F)
    (hfalse : claim ≠ dot (bindRightAffine Q L w) w + K)
    (hrounds : verify_multi_round (claim-K) messages (List.ofFn u) = some terminal)
    (hrow : LinearTerminal.residual terminal cross scale messageA messageB pads = 0)
    (hnext : LinearTerminal.clearA messageA scale pads +
        alpha * (LinearTerminal.clearB messageB scale pads - evaluate L u) =
      dot (nextWeights Q (monomialWeights u) alpha) w + dot rho values) :
    multi_round_bad_event (claim-K) (truePolys (bindRightAffine Q L w) w u)
        messages (List.ofFn u) ∨
      (LinearTerminal.Data.mk terminal (evaluate w u) (evaluate (bindRightAffine Q L w) u)
        cross pads).Bad scale ∨
      AssertionBad (LinearTerminal.clearA messageA scale pads - evaluate w u) 0
        (Fin.cons alpha rho)
        (Fin.cons (LinearTerminal.clearB messageB scale pads - evaluate (bindRightAffine Q L w) u)
          (fun i => -values i)) := by
  classical
  by_cases hpair : LinearTerminal.clearA messageA scale pads = evaluate w u ∧
      LinearTerminal.clearB messageB scale pads = evaluate (bindRightAffine Q L w) u ∧
      ∀ i, values i = 0
  · have hnext' : LinearTerminal.clearA messageA scale pads +
        alpha * (LinearTerminal.clearB messageB scale pads - evaluate L u) =
        dot (nextWeights Q (monomialWeights u) alpha) w := by
      simpa [dot, hpair.2.2] using hnext
    rcases LinearTerminal.affine_layer_reduction Q L w K u claim terminal cross scale
      messageA messageB alpha pads messages hfalse hrounds hrow hnext' with hr | ht | hc
    · exact Or.inl hr
    · exact Or.inr (Or.inl ht)
    · rcases hc.1 with hA | hB
      · exact (hA hpair.1).elim
      · exact (hB hpair.2.1).elim
  · apply Or.inr ∘ Or.inr
    apply combine_entry_reduction _ _ _ _ _ _ _ _ (by
      simpa only [not_and_or, not_forall] using hpair)
    rw [affine_nextWeights_correct Q L (monomialWeights u) w alpha] at hnext
    simpa only [← evaluate_eq_dot] using hnext

/-- One full block has error at most `1/|F|`. This raw count includes all
coordinates of the block, rather than charging their individual reads. -/
theorem block_bad_card_mul_le [Fintype F] [DecidableEq F] {n : ℕ}
    (incoming claim : F) (values : Fin n → F) :
    (univ.filter fun beta : Fin n → F => AssertionBad incoming claim beta values).card *
      Fintype.card F ≤ Fintype.card (Fin n → F) := by
  cases n with
  | zero => simp [AssertionBad]
  | succ n =>
      have h : (univ.filter fun beta : Fin (n+1) → F =>
          AssertionBad incoming claim beta values).card ≤ Fintype.card F ^ n := by
        simpa [Nat.min_eq_left (show 1 ≤ n+1 by omega)] using
          ChallengeBlocks.assertion_bad_card incoming claim values
      calc
        _ ≤ Fintype.card F ^ n * Fintype.card F := Nat.mul_le_mul_right _ h
        _ = _ := by simp [pow_succ]

/-- The retained compiler reduction exposes entry and assertion errors
separately. Both can still be counted at their one actual query: each is a
fixed affine hyperplane in that query's complete coefficient vector. -/
theorem sequential_entry_cover {n m : ℕ} (incoming claim : F)
    (rho entries : Fin n → F) (beta assertions : Fin m → F)
    (h : AssertionBad incoming claim rho entries ∨
      AssertionBad (incoming + dot rho entries) claim beta assertions) :
    AssertionBad incoming claim (Fin.append rho beta) (Fin.append entries 0) ∨
      AssertionBad incoming claim (Fin.append rho beta) (Fin.append entries assertions) := by
  rcases h with he | ha
  · apply Or.inl
    have heq := ChallengeBlocks.assertion_bad_equation _ _ _ _ he
    obtain ⟨i, _, hi, _⟩ := he
    apply assertion_reduction
    · exact ⟨i.castAdd m, by simpa using hi⟩
    · rw [dot_append]
      simp only [dot, Pi.zero_apply, mul_zero, sum_const_zero, add_zero]
      simp only [dot] at heq
      linear_combination -heq
  · apply Or.inr
    have heq := ChallengeBlocks.assertion_bad_equation _ _ _ _ ha
    obtain ⟨i, _, hi, _⟩ := ha
    apply assertion_reduction
    · exact ⟨i.natAdd n, by simpa using hi⟩
    · rw [dot_append]
      linear_combination -heq

/-- The compiler's old combine error and final input-entry error are also
two fixed hyperplanes in one actual answer. Both masked claims and the true
evaluations are fixed before the shared alpha/entry vector is sampled. -/
theorem sequential_combine_cover {n : ℕ} (A B trueA trueB linear alpha : F)
    (rho values : Fin n → F)
    (h : BadCombineEvent trueA trueB A B alpha ∨
      AssertionBad (trueA+alpha*(trueB-linear)) (A+alpha*(B-linear)) rho values) :
    AssertionBad (A-trueA) 0 (Fin.cons alpha rho) (Fin.cons (B-trueB) 0) ∨
      AssertionBad (A-trueA) 0 (Fin.cons alpha rho)
        (Fin.cons (B-trueB) (fun i => -values i)) := by
  rcases h with hc | he
  · apply Or.inl
    have hf : A ≠ trueA ∨ B ≠ trueB ∨ ∃ i, (0 : Fin n → F) i ≠ 0 := by
      rcases hc.1 with hA | hB
      · exact Or.inl hA
      · exact Or.inr (Or.inl hB)
    have hn : A+alpha*(B-linear) = trueA+alpha*(trueB-linear) + dot rho (0 : Fin n → F) := by
      simp only [dot, Pi.zero_apply, mul_zero, sum_const_zero, add_zero]
      linear_combination hc.2
    have hz : (fun i : Fin n => -(0 : Fin n → F) i) = 0 := by
      funext i
      simp
    simpa only [hz] using
      combine_entry_reduction A B trueA trueB linear alpha rho 0 hf hn
  · apply Or.inr
    have heq := ChallengeBlocks.assertion_bad_equation _ _ _ _ he
    obtain ⟨i, _, hi, _⟩ := he
    apply combine_entry_reduction _ _ _ _ _ _ _ _ (Or.inr (Or.inr ⟨i,hi⟩))
    linear_combination -heq

/-- Reusing the compiler's separate events costs at most `2/q` for their
shared answer, never one query per event or a factor for the circuit depth.
The direct combined cancellation event above has the sharper `1/q` bound. -/
theorem two_events_card_mul_le [Fintype F] [DecidableEq F] {n : ℕ}
    (incoming claim : F) (left right : Fin n → F) :
    (univ.filter fun beta : Fin n → F =>
      AssertionBad incoming claim beta left ∨ AssertionBad incoming claim beta right).card *
      Fintype.card F ≤ 2 * Fintype.card (Fin n → F) := by
  have hsub : (univ.filter fun beta : Fin n → F =>
      AssertionBad incoming claim beta left ∨ AssertionBad incoming claim beta right) ⊆
      (univ.filter fun beta => AssertionBad incoming claim beta left) ∪
        (univ.filter fun beta => AssertionBad incoming claim beta right) := by
    intro beta h
    simpa using h
  calc
    _ ≤ ((univ.filter fun beta => AssertionBad incoming claim beta left).card +
        (univ.filter fun beta => AssertionBad incoming claim beta right).card) *
          Fintype.card F :=
      Nat.mul_le_mul_right _ ((card_le_card hsub).trans (card_union_le _ _))
    _ = _ := Nat.add_mul _ _ _
    _ ≤ Fintype.card (Fin n → F) + Fintype.card (Fin n → F) :=
      Nat.add_le_add (block_bad_card_mul_le incoming claim left)
        (block_bad_card_mul_le incoming claim right)
    _ = _ := by omega

end LfzkV2.Current.EntryChallenges
