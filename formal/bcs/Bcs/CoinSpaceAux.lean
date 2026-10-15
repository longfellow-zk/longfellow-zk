import Bcs.CoinSpace

/-!
# One coin space, read after the commitment

`Bcs.CoinSpace` counts over `(Fin T → D) × Coins` with the verifier's challenge and query given by
projections `challengeOf : Coins → Challenge` and `queryOf : Coins → Query` of the coins alone.  For
a Fiat–Shamir adversary that is too little: the challenge the verifier recomputes is the oracle's
answer at points the adversary chose, and an adversary that has committed chooses its points
*knowing its commitment*.  So the challenge is a function of the coins **and of the commit stage's
private state**.

This file is `Bcs.CoinSpace`'s three theorems with `challengeOf, queryOf : Aux → Coins → _`, read at
`A.auxOf answers`, the private state the commit stage leaves on the hash tape.  The argument is the
same — slice on the coins, apply `Merkle.MH.mh_extract_rom_card_le` per slice, sum — and the only new
fact is that the per-slice opening stage may read the private state it resumes from:
`fun aux => A.openingStage (challengeOf aux coins) (queryOf aux coins) aux` is an opening stage like
any other, and on each tape it runs exactly the opening stage `CompiledAccepts` evaluates
(`lazyRun_extractionRun_congr`).

What is *not* allowed, and is not needed: the challenge reading the hash tape directly.  The private
state is a function of the commit stage's own queries, which is what keeps the extraction argument
sound.  An adversary that wants its root in hand stores it in `Aux`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open Finset LigeroFamily Merkle Merkle.MH Merkle.RandomOracle

variable {Statement Oracle Challenge Response Query Coins : Type*}
variable {Opening : Query → Type*}
variable {Enc D Salt M Aux Aux' : Type*}
variable {n commitFuel respondFuel revealFuel T : ℕ}

namespace Adversary

/-- The commit stage's private state on a tape. -/
def auxOf [Inhabited D] [DecidableEq Enc]
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel) (answers : Fin T → D) : Aux :=
  (lazyRun answers default A.commit []).1.2

end Adversary

/-! ## The experiment reads its opening stage at one private state -/

/-- A bound execution reads its continuation only at the first phase's output. -/
theorem lazyRun_bind_congr {Q A B : Type*} [DecidableEq Q] {T : ℕ} (tape : Fin T → D) (dflt : D)
    {f₁ f₂ : ℕ} (c : Tree Q D A f₁) (k₁ k₂ : A → Tree Q D B f₂) (seen : List Q)
    (h : k₁ (lazyRun tape dflt c seen).1 = k₂ (lazyRun tape dflt c seen).1) :
    lazyRun tape dflt (c.bind k₁) seen = lazyRun tape dflt (c.bind k₂) seen := by
  rw [lazyRun_bind, lazyRun_bind, h]


section Congr

variable [Inhabited D] [DecidableEq Enc] (C : Codec Salt M D Enc) (n t₁ t₂ T : ℕ)
  {Aux : Type*} (commit : Tree Enc D (D × Aux) t₁)

/-- Two opening stages that agree at the commit stage's private state give the same lazy
experiment. -/
theorem lazyRun_extractionRun_congr
    (op₁ op₂ : Aux → Tree Enc D (OpeningClaim n Salt M D) t₂) (answers : Fin T → D)
    (h : op₁ (lazyRun answers default commit []).1.2
      = op₂ (lazyRun answers default commit []).1.2) :
    lazyRun answers default (extractionRun C n t₁ t₂ commit op₁) [] =
      lazyRun answers default (extractionRun C n t₁ t₂ commit op₂) [] := by
  unfold extractionRun
  exact lazyRun_bind_congr answers default commit _ _ [] (by simp only [h])

variable {C n t₁ t₂ T commit}

theorem extractionOracle_congr
    {op₁ op₂ : Aux → Tree Enc D (OpeningClaim n Salt M D) t₂} {answers : Fin T → D}
    (h : op₁ (lazyRun answers default commit []).1.2
      = op₂ (lazyRun answers default commit []).1.2) :
    extractionOracle C n t₁ t₂ T commit op₁ answers =
      extractionOracle C n t₁ t₂ T commit op₂ answers := by
  funext x
  unfold extractionOracle runOracle runSlots
  rw [lazyRun_extractionRun_congr C n t₁ t₂ T commit op₁ op₂ answers h]

theorem commitRoot_congr
    {op₁ op₂ : Aux → Tree Enc D (OpeningClaim n Salt M D) t₂} {answers : Fin T → D}
    (h : op₁ (lazyRun answers default commit []).1.2
      = op₂ (lazyRun answers default commit []).1.2) :
    commitRoot C n t₁ t₂ T commit op₁ answers = commitRoot C n t₁ t₂ T commit op₂ answers := by
  unfold commitRoot
  rw [extractionOracle_congr h]

theorem commitTrace_congr
    {op₁ op₂ : Aux → Tree Enc D (OpeningClaim n Salt M D) t₂} {answers : Fin T → D}
    (h : op₁ (lazyRun answers default commit []).1.2
      = op₂ (lazyRun answers default commit []).1.2) :
    commitTrace C n t₁ t₂ T commit op₁ answers = commitTrace C n t₁ t₂ T commit op₂ answers := by
  unfold commitTrace
  rw [extractionOracle_congr h]

theorem openingClaim_congr
    {op₁ op₂ : Aux → Tree Enc D (OpeningClaim n Salt M D) t₂} {answers : Fin T → D}
    (h : op₁ (lazyRun answers default commit []).1.2
      = op₂ (lazyRun answers default commit []).1.2) :
    openingClaim C n t₁ t₂ T commit op₁ answers = openingClaim C n t₁ t₂ T commit op₂ answers := by
  unfold openingClaim
  rw [extractionOracle_congr h, commitRun_eq, h]

theorem extractionExplains_congr [DecidableEq D] [Inhabited Salt] [Inhabited M]
    (dec : RoleDecoders C)
    {op₁ op₂ : Aux → Tree Enc D (OpeningClaim n Salt M D) t₂} {answers : Fin T → D}
    (h : op₁ (lazyRun answers default commit []).1.2
      = op₂ (lazyRun answers default commit []).1.2) :
    ExtractionExplains C dec n t₁ t₂ T commit op₁ answers ↔
      ExtractionExplains C dec n t₁ t₂ T commit op₂ answers := by
  unfold ExtractionExplains
  rw [commitRoot_congr h, commitTrace_congr h, openingClaim_congr h]

end Congr

/-! ## The three counts -/

open scoped Classical in
/-- **The Merkle half, with coins read after the commitment.**  `merkle_card_le_coins` at
`challengeOf, queryOf : Aux → Coins → _`. -/
theorem merkle_card_le_coins_aux
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    [Fintype Coins] [DecidableEq Coins]
    {C : Codec Salt M D Enc} (dec : RoleDecoders C)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (challengeOf : Aux → Coins → Challenge) (queryOf : Aux → Coins → Query)
    (statement : (Fin T → D) × Coins → Statement) (ht₁ : commitFuel ≤ T)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ T) :
    (univ.filter fun omega : (Fin T → D) × Coins ↦
        CompiledAccepts K A C (statement omega) (challengeOf (A.auxOf omega.1) omega.2)
            (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          ¬ ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
            (A.openingStage (challengeOf (A.auxOf omega.1) omega.2)
              (queryOf (A.auxOf omega.1) omega.2)) omega.1).card ≤
      Fintype.card Coins * (merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1)) := by
  classical
  rw [card_filter_prod_snd]
  have hslice : ∀ coins : Coins,
      (univ.filter fun answers : Fin T → D ↦
          CompiledAccepts K A C (statement (answers, coins))
              (challengeOf (A.auxOf answers) coins) (queryOf (A.auxOf answers) coins) answers ∧
            ¬ ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
              (A.openingStage (challengeOf (A.auxOf answers) coins)
                (queryOf (A.auxOf answers) coins)) answers).card ≤
        merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1) := by
    intro coins
    -- the per-slice opening stage reads the private state it resumes from
    let op : Aux → Tree Enc D (OpeningClaim n Salt M D) (revealFuel + respondFuel) :=
      fun aux ↦ A.openingStage (challengeOf aux coins) (queryOf aux coins) aux
    refine le_trans (Finset.card_le_card ?_)
      (mh_extract_rom_card_le C dec n commitFuel (revealFuel + respondFuel) T A.commit op ht₁ hT)
    intro answers hanswers
    simp only [mem_filter, mem_univ, true_and] at hanswers ⊢
    have h : A.openingStage (challengeOf (A.auxOf answers) coins) (queryOf (A.auxOf answers) coins)
        (lazyRun answers default A.commit []).1.2 = op (lazyRun answers default A.commit []).1.2 :=
      rfl
    refine ⟨?_, fun hexp ↦ hanswers.2 ((extractionExplains_congr dec h).mpr hexp)⟩
    have hacc := hanswers.1.2.1
    rw [← A.commitRoot_eq C (challengeOf (A.auxOf answers) coins)
      (queryOf (A.auxOf answers) coins) answers, commitRoot_congr h,
      extractionOracle_congr h, openingClaim_congr h] at hacc
    exact hacc
  calc ∑ coins : Coins,
        (univ.filter fun answers : Fin T → D ↦
          CompiledAccepts K A C (statement (answers, coins))
              (challengeOf (A.auxOf answers) coins) (queryOf (A.auxOf answers) coins) answers ∧
            ¬ ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
              (A.openingStage (challengeOf (A.auxOf answers) coins)
                (queryOf (A.auxOf answers) coins)) answers).card
      ≤ ∑ _coins : Coins, merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1) :=
        Finset.sum_le_sum fun coins _ ↦ hslice coins
    _ = Fintype.card Coins * (merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

open scoped Classical in
/-- **Dropping the extraction hypothesis, with coins read after the commitment.** -/
theorem drop_explains_card_le_coins_aux
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    [Fintype Coins] [DecidableEq Coins]
    {C : Codec Salt M D Enc} (dec : RoleDecoders C)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (challengeOf : Aux → Coins → Challenge) (queryOf : Aux → Coins → Query)
    (statement : (Fin T → D) × Coins → Statement)
    (P : (Fin T → D) × Coins → Prop)
    (ht₁ : commitFuel ≤ T)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ T) :
    (univ.filter fun omega : (Fin T → D) × Coins ↦
        CompiledAccepts K A C (statement omega) (challengeOf (A.auxOf omega.1) omega.2)
            (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧ P omega).card ≤
      (univ.filter fun omega : (Fin T → D) × Coins ↦
          (CompiledAccepts K A C (statement omega) (challengeOf (A.auxOf omega.1) omega.2)
              (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
            ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
              (A.openingStage (challengeOf (A.auxOf omega.1) omega.2)
                (queryOf (A.auxOf omega.1) omega.2)) omega.1) ∧ P omega).card +
        Fintype.card Coins * (merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1)) := by
  classical
  refine le_trans (le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _))
    (Nat.add_le_add_left
      (merkle_card_le_coins_aux dec K A challengeOf queryOf statement ht₁ hT) _)
  intro omega homega
  simp only [mem_filter, mem_univ, true_and] at homega
  by_cases hexp : ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
      (A.openingStage (challengeOf (A.auxOf omega.1) omega.2)
        (queryOf (A.auxOf omega.1) omega.2)) omega.1
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, ⟨homega.1, hexp⟩, homega.2⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, homega.1, hexp⟩)

open scoped Classical in
/--
**The price of the compilation, with coins read after the commitment.**

```
Pr[ the compiled verifier accepts ∧ P ]
    ≤  Pr[ the compiled verifier accepts ∧ the extraction explains it ∧ P ]
       +  merkleNumerator(t₁, T) / |D|
```

`drop_explains_ratio_le` with the challenge and query allowed to depend on the commit stage's
private state, which is what a Fiat–Shamir adversary's recomputed challenges do.
-/
theorem drop_explains_ratio_le_aux
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    {C : Codec Salt M D Enc} (dec : RoleDecoders C)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (challengeOf : Aux → Coins → Challenge) (queryOf : Aux → Coins → Query)
    (statement : (Fin T → D) × Coins → Statement)
    (P : (Fin T → D) × Coins → Prop)
    (ht₁ : commitFuel ≤ T)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ T) (hT1 : 1 ≤ T) :
    ((univ.filter fun omega : (Fin T → D) × Coins ↦
        CompiledAccepts K A C (statement omega) (challengeOf (A.auxOf omega.1) omega.2)
            (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧ P omega).card : ℚ)
        / ((Fintype.card D : ℚ) ^ T * Fintype.card Coins)
      ≤ ((univ.filter fun omega : (Fin T → D) × Coins ↦
            (CompiledAccepts K A C (statement omega) (challengeOf (A.auxOf omega.1) omega.2)
                (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
              ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
                (A.openingStage (challengeOf (A.auxOf omega.1) omega.2)
                  (queryOf (A.auxOf omega.1) omega.2)) omega.1) ∧
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
  have hpow : (Fintype.card D : ℚ) ^ T
      = (Fintype.card D : ℚ) ^ (T - 1) * (Fintype.card D : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  have hpos : (0 : ℚ) < (Fintype.card D : ℚ) ^ T * Fintype.card Coins :=
    mul_pos (pow_pos hDq T) hCq
  have hnat := drop_explains_card_le_coins_aux dec K A challengeOf queryOf statement P ht₁ hT
  have hcast : ((univ.filter fun omega : (Fin T → D) × Coins ↦
        CompiledAccepts K A C (statement omega) (challengeOf (A.auxOf omega.1) omega.2)
            (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧ P omega).card : ℚ)
      ≤ ((univ.filter fun omega : (Fin T → D) × Coins ↦
            (CompiledAccepts K A C (statement omega) (challengeOf (A.auxOf omega.1) omega.2)
                (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
              ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
                (A.openingStage (challengeOf (A.auxOf omega.1) omega.2)
                  (queryOf (A.auxOf omega.1) omega.2)) omega.1) ∧
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
        CompiledAccepts K A C (statement omega) (challengeOf (A.auxOf omega.1) omega.2)
            (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧ P omega).card : ℚ)
        / ((Fintype.card D : ℚ) ^ T * Fintype.card Coins)
      ≤ (((univ.filter fun omega : (Fin T → D) × Coins ↦
            (CompiledAccepts K A C (statement omega) (challengeOf (A.auxOf omega.1) omega.2)
                (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
              ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
                (A.openingStage (challengeOf (A.auxOf omega.1) omega.2)
                  (queryOf (A.auxOf omega.1) omega.2)) omega.1) ∧
            P omega).card : ℚ)
          + (Fintype.card Coins : ℚ) *
            ((merkleNumerator commitFuel T : ℚ) * (Fintype.card D : ℚ) ^ (T - 1)))
          / ((Fintype.card D : ℚ) ^ T * Fintype.card Coins) := by gcongr
    _ = _ := by rw [add_div, hterm]

end Bcs
