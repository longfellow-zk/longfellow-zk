import Bcs.Soundness

/-!
# One coin space, two projections

`Bcs.Soundness` counts over `(Fin T → D) × (Challenge × Query)`: the hash tape, then the verifier's
challenge and its query, as **independent** coordinates.  That is right for an interactive protocol
and wrong for a Fiat--Shamir one, where both are derived from a single hash tape and so are functions
of one coordinate.

This file is the same two counts over `(Fin T → D) × Coins` for an arbitrary coin space with two
projections.  Nothing about the argument changes — it was always "slice on the coins, apply
`Merkle.MH.mh_extract_rom_card_le` per slice, sum" — and the product case is recovered at
`Coins := Challenge × Query` with `Prod.fst` and `Prod.snd`.

## Why this is the whole of the Fiat--Shamir Merkle step

`Bcs.Compiler` needs no change.  Its `indices : Query → Finset (Fin n)` reads the *query*, and under
Fiat--Shamir the query is the tape-derived column set — so `Query` stays the real query type and
`queryOf` is the tape's query decoder.  What could not be expressed before is that the same coin
draws the challenge *and* the query: setting `Query := Unit` would make the opened columns constant,
and `Challenge := Unit` would make the prover's response blind to its own challenge, and both are
restrictions on the adversary rather than abstractions of it.  A coin space with two projections is
the least change that avoids both.

`drop_explains_ratio_le` is stated in exactly the shape `Lfzk.Nizk.nizk_ratio_le` takes as
`hmerkle`, so that hypothesis becomes a theorem at `Coins := Fin L → C`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open Finset LigeroFamily Merkle Merkle.MH Merkle.RandomOracle

variable {Statement Oracle Challenge Response Query Coins : Type*}
variable {Opening : Query → Type*}
variable {Enc D Salt M Aux Aux' : Type*}
variable {n commitFuel respondFuel revealFuel T : ℕ}

open scoped Classical in
/-- **The Merkle half, over an arbitrary coin space.**  `merkle_card_le` at
`Coins := Challenge × Query`. -/
theorem merkle_card_le_coins
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    [Fintype Coins] [DecidableEq Coins]
    {C : Codec Salt M D Enc} (dec : RoleDecoders C)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (challengeOf : Coins → Challenge) (queryOf : Coins → Query)
    (statement : (Fin T → D) × Coins → Statement) (ht₁ : commitFuel ≤ T)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ T) :
    (univ.filter fun omega : (Fin T → D) × Coins ↦
        CompiledAccepts K A C (statement omega) (challengeOf omega.2) (queryOf omega.2) omega.1 ∧
          ¬ ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
            (A.openingStage (challengeOf omega.2) (queryOf omega.2)) omega.1).card ≤
      Fintype.card Coins * (merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1)) := by
  classical
  rw [card_filter_prod_snd]
  have hslice : ∀ coins : Coins,
      (univ.filter fun answers : Fin T → D ↦
          CompiledAccepts K A C (statement (answers, coins))
              (challengeOf coins) (queryOf coins) answers ∧
            ¬ ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
              (A.openingStage (challengeOf coins) (queryOf coins)) answers).card ≤
        merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1) := by
    intro coins
    refine le_trans (Finset.card_le_card ?_)
      (mh_extract_rom_card_le C dec n commitFuel (revealFuel + respondFuel) T A.commit
        (A.openingStage (challengeOf coins) (queryOf coins)) ht₁ hT)
    intro answers hanswers
    simp only [mem_filter, mem_univ, true_and] at hanswers ⊢
    refine ⟨?_, hanswers.2⟩
    have hacc := hanswers.1.2.1
    rwa [← A.commitRoot_eq C (challengeOf coins) (queryOf coins) answers] at hacc
  calc ∑ coins : Coins,
        (univ.filter fun answers : Fin T → D ↦
          CompiledAccepts K A C (statement (answers, coins))
              (challengeOf coins) (queryOf coins) answers ∧
            ¬ ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
              (A.openingStage (challengeOf coins) (queryOf coins)) answers).card
      ≤ ∑ _coins : Coins, merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1) :=
        Finset.sum_le_sum fun coins _ ↦ hslice coins
    _ = Fintype.card Coins * (merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

open scoped Classical in
/-- **Dropping the extraction hypothesis, over an arbitrary coin space.**  Whatever else a count over
this sample space asks for, the `ExtractionExplains` conjunct may be removed for
`merkleNumerator · |D|^(T-1)` per coin. -/
theorem drop_explains_card_le_coins
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    [Fintype Coins] [DecidableEq Coins]
    {C : Codec Salt M D Enc} (dec : RoleDecoders C)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (challengeOf : Coins → Challenge) (queryOf : Coins → Query)
    (statement : (Fin T → D) × Coins → Statement)
    (P : (Fin T → D) × Coins → Prop)
    (ht₁ : commitFuel ≤ T)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ T) :
    (univ.filter fun omega : (Fin T → D) × Coins ↦
        CompiledAccepts K A C (statement omega) (challengeOf omega.2) (queryOf omega.2) omega.1 ∧
          P omega).card ≤
      (univ.filter fun omega : (Fin T → D) × Coins ↦
          (CompiledAccepts K A C (statement omega)
              (challengeOf omega.2) (queryOf omega.2) omega.1 ∧
            ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
              (A.openingStage (challengeOf omega.2) (queryOf omega.2)) omega.1) ∧ P omega).card +
        Fintype.card Coins * (merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1)) := by
  classical
  refine le_trans (le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _))
    (Nat.add_le_add_left
      (merkle_card_le_coins dec K A challengeOf queryOf statement ht₁ hT) _)
  intro omega homega
  simp only [mem_filter, mem_univ, true_and] at homega
  by_cases hexp : ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
      (A.openingStage (challengeOf omega.2) (queryOf omega.2)) omega.1
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, ⟨homega.1, hexp⟩, homega.2⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, homega.1, hexp⟩)

open scoped Classical in
/--
**The price of the compilation, as a probability.**

```
Pr[ the compiled verifier accepts ∧ P ]
    ≤  Pr[ the compiled verifier accepts ∧ the extraction explains it ∧ P ]
       +  merkleNumerator(t₁, T) / |D|
```

This is exactly the shape `Lfzk.Nizk.nizk_ratio_le` takes as `hmerkle`, with the second event being
the one the round-by-round argument bounds — the *oracle* protocol's acceptance — and the first the
one a real verifier decides.
-/
theorem drop_explains_ratio_le
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    {C : Codec Salt M D Enc} (dec : RoleDecoders C)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (challengeOf : Coins → Challenge) (queryOf : Coins → Query)
    (statement : (Fin T → D) × Coins → Statement)
    (P : (Fin T → D) × Coins → Prop)
    (ht₁ : commitFuel ≤ T)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ T) (hT1 : 1 ≤ T) :
    ((univ.filter fun omega : (Fin T → D) × Coins ↦
        CompiledAccepts K A C (statement omega) (challengeOf omega.2) (queryOf omega.2) omega.1 ∧
          P omega).card : ℚ)
        / ((Fintype.card D : ℚ) ^ T * Fintype.card Coins)
      ≤ ((univ.filter fun omega : (Fin T → D) × Coins ↦
            (CompiledAccepts K A C (statement omega)
                (challengeOf omega.2) (queryOf omega.2) omega.1 ∧
              ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
                (A.openingStage (challengeOf omega.2) (queryOf omega.2)) omega.1) ∧
            P omega).card : ℚ)
          / ((Fintype.card D : ℚ) ^ T * Fintype.card Coins)
        + (merkleNumerator commitFuel T : ℚ) / (Fintype.card D : ℚ) := by
  classical
  have hDq : (0 : ℚ) < (Fintype.card D : ℚ) := by
    have : 0 < Fintype.card D := Fintype.card_pos
    exact_mod_cast this
  have hCq : (0 : ℚ) < (Fintype.card Coins : ℚ) := by
    have : 0 < Fintype.card Coins := Fintype.card_pos
    exact_mod_cast this
  have hpos : (0 : ℚ) < (Fintype.card D : ℚ) ^ T * Fintype.card Coins :=
    mul_pos (pow_pos hDq T) hCq
  have hpow : (Fintype.card D : ℚ) ^ T
      = (Fintype.card D : ℚ) ^ (T - 1) * (Fintype.card D : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  have hnat := drop_explains_card_le_coins dec K A challengeOf queryOf statement P ht₁ hT
  have hcast : ((univ.filter fun omega : (Fin T → D) × Coins ↦
        CompiledAccepts K A C (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ P omega).card : ℚ)
      ≤ ((univ.filter fun omega : (Fin T → D) × Coins ↦
            (CompiledAccepts K A C (statement omega)
                (challengeOf omega.2) (queryOf omega.2) omega.1 ∧
              ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
                (A.openingStage (challengeOf omega.2) (queryOf omega.2)) omega.1) ∧
            P omega).card : ℚ)
        + (Fintype.card Coins : ℚ) *
          ((merkleNumerator commitFuel T : ℚ) * (Fintype.card D : ℚ) ^ (T - 1)) := by
    exact_mod_cast hnat
  have hterm : ((Fintype.card Coins : ℚ) *
        ((merkleNumerator commitFuel T : ℚ) * (Fintype.card D : ℚ) ^ (T - 1)))
      / ((Fintype.card D : ℚ) ^ T * Fintype.card Coins)
      = (merkleNumerator commitFuel T : ℚ) / (Fintype.card D : ℚ) := by
    rw [hpow]
    field_simp
  calc ((univ.filter fun omega : (Fin T → D) × Coins ↦
        CompiledAccepts K A C (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ P omega).card : ℚ)
        / ((Fintype.card D : ℚ) ^ T * Fintype.card Coins)
      ≤ (((univ.filter fun omega : (Fin T → D) × Coins ↦
            (CompiledAccepts K A C (statement omega)
                (challengeOf omega.2) (queryOf omega.2) omega.1 ∧
              ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
                (A.openingStage (challengeOf omega.2) (queryOf omega.2)) omega.1) ∧
            P omega).card : ℚ)
          + (Fintype.card Coins : ℚ) *
            ((merkleNumerator commitFuel T : ℚ) * (Fintype.card D : ℚ) ^ (T - 1)))
          / ((Fintype.card D : ℚ) ^ T * Fintype.card Coins) := by gcongr
    _ = _ := by rw [add_div, hterm]

end Bcs
