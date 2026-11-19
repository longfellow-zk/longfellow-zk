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
