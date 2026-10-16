import Bcs.TotalOracle
import Merkle.TwoOracle

/-!
# A fixed verifier path in a finite random oracle

If the prover's output has been fixed before the transcript oracle is sampled,
the verifier's distinct hash inputs are fixed coordinates of a uniformly
random function.  Splitting those coordinates from the rest of the function
identifies their answers with an ordinary independent verifier tape.  This is
the finite counting bridge needed by the zero-query Fiat--Shamir case.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Finset
open scoped Classical

variable {Q C : Type} [Fintype Q] [DecidableEq Q] [Fintype C]

/-- Hash-input coordinates outside a fixed verifier path. -/
abbrev AwayFromPath {T : ℕ} (point : Fin T → Q) :=
  { q : Q // ∀ i, point i ≠ q }

/-- A random oracle is equivalent to its answers along a fixed injective
verifier path together with all answers outside that path. -/
noncomputable def splitFixedPath {T : ℕ} (point : Fin T → Q)
    (hinj : Function.Injective point) :
    (Q → C) ≃ ((Fin T → C) × (AwayFromPath point → C)) where
  toFun H := (fun i => H (point i), fun q => H q.1)
  invFun p q :=
    if h : ∃ i, point i = q then p.1 (Classical.choose h)
    else p.2 ⟨q, by
      intro i hi
      exact h ⟨i, hi⟩⟩
  left_inv H := by
    funext q
    by_cases h : ∃ i, point i = q
    · simp only [dif_pos h]
      exact congrArg H (Classical.choose_spec h)
    · simp only [dif_neg h]
  right_inv p := by
    rcases p with ⟨tape, off⟩
    apply Prod.ext
    · funext i
      simp only [dif_pos (show ∃ j, point j = point i from ⟨i, rfl⟩)]
      exact congrArg tape (hinj (Classical.choose_spec
        (show ∃ j, point j = point i from ⟨i, rfl⟩)))
    · funext q
      have h : ¬ ∃ i, point i = q.1 := by
        rintro ⟨i, hi⟩
        exact q.2 i hi
      simp only [dif_neg h]

/-- Counting form of the fixed-path projection. Every verifier tape has the
same number of extensions to a total random oracle. -/
theorem fixedPath_card_filter {T : ℕ} (point : Fin T → Q)
    (hinj : Function.Injective point) (E : (Fin T → C) → Prop) :
    (univ.filter fun H : Q → C => E (fun i => H (point i))).card =
      (univ.filter E).card * Fintype.card (AwayFromPath point → C) := by
  classical
  rw [Finset.card_filter]
  calc
    (∑ H : Q → C, if E (fun i => H (point i)) then 1 else 0) =
        ∑ p : (Fin T → C) × (AwayFromPath point → C),
          if E p.1 then 1 else 0 := by
            exact Fintype.sum_equiv (splitFixedPath point hinj) _ _
              (by intro H; rfl)
    _ = ∑ tape : Fin T → C, ∑ _off : AwayFromPath point → C,
          if E tape then 1 else 0 := by rw [Fintype.sum_prod_type]
    _ = (univ.filter E).card * Fintype.card (AwayFromPath point → C) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Finset.card_filter]
          rw [← Finset.mul_sum]
          exact Nat.mul_comm _ _

/-- Sampling a uniformly random total oracle and reading it along a fixed
injective path has exactly the distribution of a uniform verifier tape.  The
statement also covers an event depending jointly on all tape answers. -/
theorem fixedPath_ratio_eq [Nonempty C] {T : ℕ} (point : Fin T → Q)
    (hinj : Function.Injective point) (E : (Fin T → C) → Prop) :
    ((univ.filter fun H : Q → C => E (fun i => H (point i))).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q =
      ((univ.filter E).card : ℚ) / (Fintype.card C : ℚ) ^ T := by
  classical
  let Off := AwayFromPath point
  have hnum := fixedPath_card_filter point hinj E
  have hcard : Fintype.card C ^ Fintype.card Q =
      Fintype.card C ^ T * Fintype.card (Off → C) := by
    calc
      Fintype.card C ^ Fintype.card Q = Fintype.card (Q → C) := by simp
      _ = Fintype.card ((Fin T → C) × (Off → C)) :=
        Fintype.card_congr (splitFixedPath point hinj)
      _ = Fintype.card C ^ T * Fintype.card (Off → C) := by simp
  have hcardq : (Fintype.card C : ℚ) ^ Fintype.card Q =
      (Fintype.card C : ℚ) ^ T * Fintype.card (Off → C) := by
    exact_mod_cast hcard
  have hC : (0 : ℚ) < (Fintype.card C : ℚ) ^ T := by
    exact pow_pos (by exact_mod_cast Fintype.card_pos) _
  have hOff : (0 : ℚ) < (Fintype.card (Off → C) : ℚ) := by
    exact_mod_cast Fintype.card_pos
  rw [hcardq, hnum]
  push_cast
  apply (div_eq_div_iff (mul_ne_zero (ne_of_gt hC) (ne_of_gt hOff))
    (ne_of_gt hC)).2
  ring

/-- With no transcript-oracle calls by the prover, fixing the Merkle tape
fixes its output. If the verifier's hash inputs for that output are distinct,
its Fiat--Shamir challenge sequence has exactly the interactive uniform-tape
distribution. This is an identity for arbitrary tape events, not a union
bound or a per-round estimate. -/
theorem zeroQuery_fixedPath_ratio_eq
    [Nonempty C] {QL DL Out : Type} [DecidableEq QL]
    {TL leftFuel T : ℕ}
    (leftTape : Fin TL → DL) (leftDefault : DL)
    (body : Merkle.RandomOracle.TwoOracleTree QL DL Q C Out leftFuel 0)
    (seenLeft : List QL) (dummy : Q → C)
    (point : Out → Fin T → Q)
    (hinj : ∀ out, Function.Injective (point out))
    (E : Out → (Fin T → C) → Prop) :
    let out := ((Merkle.RandomOracle.TwoOracleTree.fixLeft
      leftTape leftDefault body seenLeft).run dummy).1
    ((univ.filter fun H : Q → C =>
        E ((Merkle.RandomOracle.TwoOracleTree.fixLeft
          leftTape leftDefault body seenLeft).run H).1
          (fun i => H (point
            ((Merkle.RandomOracle.TwoOracleTree.fixLeft
              leftTape leftDefault body seenLeft).run H).1 i))).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q =
      ((univ.filter fun tape : Fin T → C => E out tape).card : ℚ) /
        (Fintype.card C : ℚ) ^ T := by
  classical
  let tree := Merkle.RandomOracle.TwoOracleTree.fixLeft
    leftTape leftDefault body seenLeft
  let out := (tree.run dummy).1
  have hfixed (H : Q → C) : (tree.run H).1 = out := by
    exact congrArg Prod.fst
      (Merkle.RandomOracle.TwoOracleTree.fixLeft_zero_run_eq
        leftTape leftDefault body seenLeft H dummy)
  have hcount :
      (univ.filter fun H : Q → C =>
        E (tree.run H).1 (fun i => H (point (tree.run H).1 i))).card =
      (univ.filter fun H : Q → C =>
        E out (fun i => H (point out i))).card := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro H _
    simp only [hfixed H]
  dsimp only [tree, out]
  rw [hcount]
  exact fixedPath_ratio_eq (point out) (hinj out) (E out)

end Bcs.TotalOracle
