import LfzkV2.ChallengeTests
import SumcheckV1.Grinding

/-!
# Prefix-local replay of V2 sumcheck rounds

The test at round i uses the first i challenges and the messages through i.
This gives the actual round tests used by `Circuit.tests` a causal presentation
for the Fiat–Shamir transcript interface, without a future-challenge hypothesis.
-/

namespace LfzkV2.RoundReplay

open SumcheckV2
open scoped Classical

variable {F : Type} [Field F]

noncomputable def dataAt : {n : ℕ} → (Cube n → F) → (Cube n → F) →
    (Fin n → RoundPoly F) → F → (i : Fin n) → (Fin i.val → F) → RoundData F
  | 0, _, _, _, _ => fun i => Fin.elim0 i
  | n + 1, q, w, messages, claim =>
      Fin.cases (motive := fun i : Fin (n + 1) => (Fin i.val → F) → RoundData F)
        (fun _ => ⟨(honestMessage q w).toPoly (dot q w), messages 0, claim⟩)
        (fun i pref => dataAt (fold q (pref ⟨0, Nat.succ_pos _⟩)) (fold w (pref ⟨0, Nat.succ_pos _⟩))
          (fun j => messages j.succ) (check_round claim (messages 0) (pref ⟨0, Nat.succ_pos _⟩)) i
          (fun j => pref j.succ))

theorem dataAt_valid {n : ℕ} (q w : Cube n → F) (messages : Fin n → RoundPoly F)
    (claim : F) (i : Fin n) (pref : Fin i.val → F) :
    (dataAt q w messages claim i pref).truth.natDegree ≤ 2 := by
  induction n generalizing claim with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ ?_ i pref
      · intro _
        exact (honestMessage q w).toPoly_natDegree (dot q w)
      · intro i pref
        exact ih _ _ _ _ i _

/-- Enumerating the prefix-local tests reproduces the numerical soundness
tests exactly, including the incoming claim at every round. -/
theorem roundTests_eq {n : ℕ} (q w : Cube n → F) (messages : Fin n → RoundPoly F)
    (claim : F) (point : Fin n → F) :
    roundTests claim (truePolys q w point) (List.ofFn messages) (List.ofFn point) =
      List.ofFn (fun i =>
        (ChallengeTest.round (dataAt q w messages claim i (SumcheckV1.extract_prefix point i)),
          point i)) := by
  induction n generalizing claim with
  | zero => simp [roundTests, truePolys]
  | succ n ih =>
      simp only [truePolys, List.ofFn_succ, roundTests, dataAt, Fin.cases_zero,
        Fin.cases_succ, SumcheckV1.extract_prefix]
      rw [ih]
      rfl

theorem round_bad_iff {n : ℕ} (q w : Cube n → F) (messages : Fin n → RoundPoly F)
    (claim : F) (point : Fin n → F) :
    multi_round_bad_event claim (truePolys q w point) (List.ofFn messages) (List.ofFn point) ↔
      ∃ i, (ChallengeTest.round (dataAt q w messages claim i
        (SumcheckV1.extract_prefix point i))).Bad (point i) := by
  rw [← roundTests_bad, roundTests_eq]
  simp [Tests.Bad]

theorem bad_card_le [Fintype F] [DecidableEq F] {n : ℕ} (q w : Cube n → F)
    (messages : Fin n → RoundPoly F) (claim : F) (i : Fin n) (pref : Fin i.val → F) :
    (Finset.univ.filter fun z =>
      (ChallengeTest.round (dataAt q w messages claim i pref)).Bad z).card ≤ 2 := by
  exact bad_round_roots _ _ _ (dataAt_valid q w messages claim i pref)

/-- Later proof messages cannot change the test at the current hash point. -/
theorem dataAt_eq_of_message_prefix {n : ℕ} (q w : Cube n → F)
    (first second : Fin n → RoundPoly F) (claim : F) (i : Fin n)
    (pref : Fin i.val → F) (hmessages : ∀ j, j ≤ i → first j = second j) :
    dataAt q w first claim i pref = dataAt q w second claim i pref := by
  induction n generalizing claim with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
        simp only [dataAt, Fin.cases_zero]
        rw [hmessages 0 (Fin.zero_le _)]
      | succ i =>
        simp only [dataAt, Fin.cases_succ]
        rw [hmessages 0 (Fin.zero_le _)]
        apply ih
        intro j hj
        exact hmessages j.succ (Nat.succ_le_succ hj)

end LfzkV2.RoundReplay
