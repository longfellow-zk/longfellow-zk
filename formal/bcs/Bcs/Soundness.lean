import Bcs.Counting
import Bcs.Extractor

/-!
# Knowledge soundness of the compiled argument

The sample space is

```
Ω = (Fin T → D) × (Challenge × Query)
```

— the hash tape, then the verifier's coins, drawn externally.  A compiled adversary fails to be
explained by the extractor only on

```
merkleNumerator · |D|^(T-1) · |coins|   +   ε_IOP · |D|^T · |coins|
```

of the `|D|^T · |coins|` points, where `ε_IOP` is whatever error the underlying oracle protocol
carries.  Dividing, `ε_ARG ≤ ε_IOP + merkleNumerator / |D|`, which is BCS Theorem 25.2.1 with
`ε_sr` replaced by plain soundness — legitimate here because the coins are external, so no
state-restoration game appears.

The proof is one double count, and each half is already a theorem elsewhere:

* **fix the coins.**  The adversary specialises to a two-stage Merkle experiment
  (`Adversary.run`), so `mh_extract_rom_card_le` applies unchanged;
* **fix the tape.**  `protocol_accepts_of_compiled` turns the compiled acceptance into an
  acceptance of the underlying IPCP by a prover whose commitment is the extracted oracle, so the
  IOP's own bound applies.

The extractor is the same on both sides — it reads the commitment trace, which the coins do not
touch — which is what lets the two halves be added.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open Finset LigeroFamily Merkle Merkle.MH Merkle.RandomOracle

/-- `Merkle`'s single-commitment extraction numerator: the sharp birthday term for the commitment
stage, plus one fresh-hit term per slot per candidate label. -/
def merkleNumerator (commitFuel T : ℕ) : ℕ :=
  commitFuel * (commitFuel - 1) / 2 + T * (2 * commitFuel + 1)

/-- The actual eligible range for one commitment, opening program, and Merkle check. -/
def merkleExtractionNumerator (n commitFuel openingCheckFuel : ℕ) : ℕ :=
  merkleNumerator commitFuel (2 * n + openingCheckFuel + commitFuel)

theorem merkleExtractionNumerator_le_tape (n commitFuel openingCheckFuel T : ℕ)
    (hT : 2 * n + openingCheckFuel + commitFuel ≤ T) :
    merkleExtractionNumerator n commitFuel openingCheckFuel ≤ merkleNumerator commitFuel T := by
  unfold merkleExtractionNumerator merkleNumerator
  gcongr

variable {Statement Oracle Challenge Response Query Witness : Type*}
variable {Opening : Query → Type*}
variable {Enc D Salt M Aux Aux' : Type*}
variable {n commitFuel respondFuel revealFuel T L : ℕ}

open scoped Classical in
/-- **The Merkle half, on its own.**  Over the whole sample space, a compiled acceptance that the
commitment-stage extraction fails to explain costs one `mh_extract_rom_card_le` per coin pair.

Factored out of `compiled_card_le` because it is what a *caller* needs: any count over this sample
space may drop an `ExtractionExplains` conjunct at this price, whatever else it is counting
(`drop_explains_card_le`). -/
theorem merkle_card_le
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    [Fintype Challenge] [DecidableEq Challenge] [Fintype Query] [DecidableEq Query]
    {C : Codec Salt M D Enc} (dec : RoleDecoders C)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (statement : (Fin T → D) × (Challenge × Query) → Statement) (ht₁ : commitFuel ≤ T)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ T) :
    (univ.filter fun omega : (Fin T → D) × (Challenge × Query) ↦
        CompiledAccepts K A C (statement omega) omega.2.1 omega.2.2 omega.1 ∧
          ¬ ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
            (A.openingStage omega.2.1 omega.2.2) omega.1).card ≤
      (Fintype.card Challenge * Fintype.card Query) *
        (merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1)) := by
  classical
  rw [card_filter_prod_snd]
  have hslice : ∀ coins : Challenge × Query,
      (univ.filter fun answers : Fin T → D ↦
          CompiledAccepts K A C (statement (answers, coins)) coins.1 coins.2 answers ∧
            ¬ ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
              (A.openingStage coins.1 coins.2) answers).card ≤
        merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1) := by
    intro coins
    refine le_trans (Finset.card_le_card ?_)
      (mh_extract_rom_card_le C dec n commitFuel (revealFuel + respondFuel) T A.commit
        (A.openingStage coins.1 coins.2) ht₁ hT)
    intro answers hanswers
    simp only [mem_filter, mem_univ, true_and] at hanswers ⊢
    refine ⟨?_, hanswers.2⟩
    have hacc := hanswers.1.2.1
    rwa [← A.commitRoot_eq C coins.1 coins.2 answers] at hacc
  calc ∑ coins : Challenge × Query,
        (univ.filter fun answers : Fin T → D ↦
          CompiledAccepts K A C (statement (answers, coins)) coins.1 coins.2 answers ∧
            ¬ ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
              (A.openingStage coins.1 coins.2) answers).card
      ≤ ∑ _coins : Challenge × Query,
          merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1) :=
        Finset.sum_le_sum fun coins _ ↦ hslice coins
    _ = (Fintype.card Challenge * Fintype.card Query) *
          (merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul]

open scoped Classical in
/-- **Dropping the extraction hypothesis, at a price.**  Whatever else a count over this sample
space asks for, the `ExtractionExplains` conjunct may be removed for `merkleNumerator · |D|^(T-1)`
per coin pair.

This is the form a *composed* development consumes: `lfzk` counts a Longfellow bad event alongside
the Ligero one, and needs to know what its own theorem costs once the oracle is a Merkle root. -/
theorem drop_explains_card_le
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    [Fintype Challenge] [DecidableEq Challenge] [Fintype Query] [DecidableEq Query]
    {C : Codec Salt M D Enc} (dec : RoleDecoders C)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (statement : (Fin T → D) × (Challenge × Query) → Statement)
    (P : (Fin T → D) × (Challenge × Query) → Prop)
    (ht₁ : commitFuel ≤ T)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ T) :
    (univ.filter fun omega : (Fin T → D) × (Challenge × Query) ↦
        CompiledAccepts K A C (statement omega) omega.2.1 omega.2.2 omega.1 ∧ P omega).card ≤
      (univ.filter fun omega : (Fin T → D) × (Challenge × Query) ↦
          (CompiledAccepts K A C (statement omega) omega.2.1 omega.2.2 omega.1 ∧
            ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
              (A.openingStage omega.2.1 omega.2.2) omega.1) ∧ P omega).card +
        (Fintype.card Challenge * Fintype.card Query) *
          (merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1)) := by
  classical
  refine le_trans (le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _))
    (Nat.add_le_add_left (merkle_card_le dec K A statement ht₁ hT) _)
  intro omega homega
  simp only [mem_filter, mem_univ, true_and] at homega
  by_cases hexp : ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
      (A.openingStage omega.2.1 omega.2.2) omega.1
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, ⟨homega.1, hexp⟩, homega.2⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, homega.1, hexp⟩)

open scoped Classical in
/-- **Knowledge soundness of the compiled argument, counted.**

`hExt` is the oracle protocol's own guarantee in contrapositive form: an extractor that reads the
committed oracle and nothing else, and a bound on the acceptance rate of any prover whose
commitment it fails on.  `Ligero.V3.witness_extractor` produces exactly this. -/
theorem compiled_card_le
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    [Fintype Challenge] [DecidableEq Challenge] [Nonempty Challenge]
    [Fintype Query] [DecidableEq Query] [Nonempty Query]
    {C : Codec Salt M D Enc} (dec : RoleDecoders C)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (statement : Statement) (rel : Statement → Witness → Prop)
    (Ext : Oracle → Fin L → Witness) (ε : ℚ) (hε : 0 ≤ ε)
    (hExt : ∀ prover : IPCPProver Statement Oracle Challenge Response,
      (∀ i, ¬ rel statement (Ext (prover.commit statement) i)) →
      K.protocol.acceptanceRate prover statement ≤ ε)
    (ht₁ : commitFuel ≤ T)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ T) :
    ((univ.filter fun omega : (Fin T → D) × (Challenge × Query) ↦
        CompiledAccepts K A C statement omega.2.1 omega.2.2 omega.1 ∧
          ∀ i, ¬ rel statement (Ext (extractedOracle dec K A omega.1) i)).card : ℚ)
      ≤ (merkleNumerator commitFuel T : ℚ) * (Fintype.card D : ℚ) ^ (T - 1) *
            (Fintype.card Challenge * Fintype.card Query : ℕ)
        + ε * (Fintype.card D : ℚ) ^ T * (Fintype.card Challenge * Fintype.card Query : ℕ) := by
  classical
  -- the two bad events
  set badMerkle : Finset ((Fin T → D) × (Challenge × Query)) :=
    univ.filter (fun omega ↦
      CompiledAccepts K A C statement omega.2.1 omega.2.2 omega.1 ∧
        ¬ ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
          (A.openingStage omega.2.1 omega.2.2) omega.1) with hbadMerkle
  set badIOP : Finset ((Fin T → D) × (Challenge × Query)) :=
    univ.filter (fun omega ↦
      (∀ i, ¬ rel statement (Ext (extractedOracle dec K A omega.1) i)) ∧
        K.protocol.accepts (K.prover (extractedOracle dec K A omega.1)
          (fun c ↦ A.responseOf c omega.1)) statement omega.2 = true) with hbadIOP
  have hsplit : (univ.filter fun omega : (Fin T → D) × (Challenge × Query) ↦
      CompiledAccepts K A C statement omega.2.1 omega.2.2 omega.1 ∧
        ∀ i, ¬ rel statement (Ext (extractedOracle dec K A omega.1) i)) ⊆
      badMerkle ∪ badIOP := by
    intro omega homega
    simp only [mem_filter, mem_univ, true_and] at homega
    by_cases hexp : ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
        (A.openingStage omega.2.1 omega.2.2) omega.1
    · refine mem_union_right _ ?_
      have haccepts := protocol_accepts_of_compiled dec K A statement omega.2.1 omega.2.2
        omega.1 hexp homega.1
      rw [Prod.mk.eta] at haccepts
      exact mem_filter.mpr ⟨mem_univ _, homega.2, haccepts⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, homega.1, hexp⟩)
  -- the Merkle half: fix the coins, count tapes
  have hMerkle : badMerkle.card ≤
      (Fintype.card Challenge * Fintype.card Query) *
        (merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1)) := by
    rw [hbadMerkle]
    exact merkle_card_le dec K A (fun _ ↦ statement) ht₁ hT
  -- the IOP half: fix the tape, count coins
  have hprodPos : (0 : ℚ) < (Fintype.card (Challenge × Query) : ℚ) := by
    have hpos : 0 < Fintype.card (Challenge × Query) := Fintype.card_pos
    exact_mod_cast hpos
  have hIOP : (badIOP.card : ℚ) ≤
      (Fintype.card D : ℚ) ^ T * (ε * (Fintype.card (Challenge × Query) : ℚ)) := by
    rw [hbadIOP, card_filter_prod_fst]
    have hslice : ∀ answers : Fin T → D,
        ((univ.filter fun coins : Challenge × Query ↦
            (∀ i, ¬ rel statement (Ext (extractedOracle dec K A answers) i)) ∧
              K.protocol.accepts (K.prover (extractedOracle dec K A answers)
                (fun c ↦ A.responseOf c answers)) statement coins = true).card : ℚ) ≤
          ε * (Fintype.card (Challenge × Query) : ℚ) := by
      intro answers
      by_cases hrel : ∀ i, ¬ rel statement (Ext (extractedOracle dec K A answers) i)
      · have hrate := hExt (K.prover (extractedOracle dec K A answers)
          fun c ↦ A.responseOf c answers) hrel
        rw [PublicCoinIPCP.acceptanceRate, finiteProtocolAcceptanceRate,
          div_le_iff₀ hprodPos] at hrate
        refine le_trans ?_ hrate
        have hsub : (univ.filter fun coins : Challenge × Query ↦
            (∀ i, ¬ rel statement (Ext (extractedOracle dec K A answers) i)) ∧
              K.protocol.accepts (K.prover (extractedOracle dec K A answers)
                (fun c ↦ A.responseOf c answers)) statement coins = true) ⊆
            univ.filter fun coins : Challenge × Query ↦
              K.protocol.accepts (K.prover (extractedOracle dec K A answers)
                (fun c ↦ A.responseOf c answers)) statement coins = true := by
          intro coins hcoins
          simp only [mem_filter, mem_univ, true_and] at hcoins ⊢
          exact hcoins.2
        exact_mod_cast Finset.card_le_card hsub
      · have hempty : (univ.filter fun coins : Challenge × Query ↦
            (∀ i, ¬ rel statement (Ext (extractedOracle dec K A answers) i)) ∧
              K.protocol.accepts (K.prover (extractedOracle dec K A answers)
                (fun c ↦ A.responseOf c answers)) statement coins = true) = ∅ :=
          Finset.filter_false_of_mem fun coins _ hmem ↦ hrel hmem.1
        rw [hempty]
        simpa using mul_nonneg hε (le_of_lt hprodPos)
    calc ((∑ answers : Fin T → D,
          (univ.filter fun coins : Challenge × Query ↦
            (∀ i, ¬ rel statement (Ext (extractedOracle dec K A answers) i)) ∧
              K.protocol.accepts (K.prover (extractedOracle dec K A answers)
                (fun c ↦ A.responseOf c answers)) statement coins = true).card : ℕ) : ℚ)
        = ∑ answers : Fin T → D,
            ((univ.filter fun coins : Challenge × Query ↦
              (∀ i, ¬ rel statement (Ext (extractedOracle dec K A answers) i)) ∧
                K.protocol.accepts (K.prover (extractedOracle dec K A answers)
                  (fun c ↦ A.responseOf c answers)) statement coins = true).card : ℚ) := by
          push_cast
          rfl
      _ ≤ ∑ _answers : Fin T → D, ε * (Fintype.card (Challenge × Query) : ℚ) :=
          Finset.sum_le_sum fun answers _ ↦ hslice answers
      _ = (Fintype.card D : ℚ) ^ T * (ε * (Fintype.card (Challenge × Query) : ℚ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  -- combine
  have hcard := Finset.card_le_card hsplit
  have hunion := Finset.card_union_le badMerkle badIOP
  have hle : ((univ.filter fun omega : (Fin T → D) × (Challenge × Query) ↦
      CompiledAccepts K A C statement omega.2.1 omega.2.2 omega.1 ∧
        ∀ i, ¬ rel statement (Ext (extractedOracle dec K A omega.1) i)).card : ℚ)
      ≤ (badMerkle.card : ℚ) + (badIOP.card : ℚ) := by
    exact_mod_cast le_trans hcard hunion
  refine le_trans hle (add_le_add ?_ ?_)
  · have hcast : (badMerkle.card : ℚ) ≤
        ((Fintype.card Challenge * Fintype.card Query) *
          (merkleNumerator commitFuel T * (Fintype.card D) ^ (T - 1)) : ℕ) := by
      exact_mod_cast hMerkle
    refine le_trans hcast (le_of_eq ?_)
    push_cast
    ring
  · refine le_trans hIOP (le_of_eq ?_)
    rw [Fintype.card_prod]
    push_cast
    ring

open scoped Classical in
/-- **The same statement as a probability.**  Over the uniform sample space — the hash tape times
the verifier's coins — a compiled adversary defeats the extractor with probability at most

```
ε_IOP  +  merkleNumerator / |D|
```

which is the BCS shape: the oracle protocol's own error, plus one commitment's extraction cost. -/
theorem compiled_ratio_le
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    [Fintype Challenge] [DecidableEq Challenge] [Nonempty Challenge]
    [Fintype Query] [DecidableEq Query] [Nonempty Query]
    {C : Codec Salt M D Enc} (dec : RoleDecoders C)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (statement : Statement) (rel : Statement → Witness → Prop)
    (Ext : Oracle → Fin L → Witness) (ε : ℚ) (hε : 0 ≤ ε)
    (hExt : ∀ prover : IPCPProver Statement Oracle Challenge Response,
      (∀ i, ¬ rel statement (Ext (prover.commit statement) i)) →
      K.protocol.acceptanceRate prover statement ≤ ε)
    (ht₁ : commitFuel ≤ T)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ T) (hT1 : 1 ≤ T) :
    ((univ.filter fun omega : (Fin T → D) × (Challenge × Query) ↦
        CompiledAccepts K A C statement omega.2.1 omega.2.2 omega.1 ∧
          ∀ i, ¬ rel statement (Ext (extractedOracle dec K A omega.1) i)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ T * (Fintype.card Challenge * Fintype.card Query : ℕ))
      ≤ (merkleNumerator commitFuel T : ℚ) / (Fintype.card D : ℚ) + ε := by
  classical
  have hDpos : (0 : ℚ) < (Fintype.card D : ℚ) := by
    have hpos : 0 < Fintype.card D := Fintype.card_pos
    exact_mod_cast hpos
  have hcoinsPos : (0 : ℚ) < (Fintype.card Challenge * Fintype.card Query : ℕ) := by
    have hpos : 0 < Fintype.card Challenge * Fintype.card Query :=
      Nat.mul_pos Fintype.card_pos Fintype.card_pos
    exact_mod_cast hpos
  have hpos : (0 : ℚ) < (Fintype.card D : ℚ) ^ T *
      (Fintype.card Challenge * Fintype.card Query : ℕ) :=
    mul_pos (pow_pos hDpos T) hcoinsPos
  rw [div_le_iff₀ hpos]
  have hpow : (Fintype.card D : ℚ) ^ T =
      (Fintype.card D : ℚ) ^ (T - 1) * (Fintype.card D : ℚ) := by
    rw [← pow_succ]
    congr 1
    omega
  have heq : ((merkleNumerator commitFuel T : ℚ) / (Fintype.card D : ℚ) + ε) *
      ((Fintype.card D : ℚ) ^ T * (Fintype.card Challenge * Fintype.card Query : ℕ))
      = (merkleNumerator commitFuel T : ℚ) * (Fintype.card D : ℚ) ^ (T - 1) *
          (Fintype.card Challenge * Fintype.card Query : ℕ)
        + ε * (Fintype.card D : ℚ) ^ T *
          (Fintype.card Challenge * Fintype.card Query : ℕ) := by
    rw [hpow]
    field_simp
  rw [heq]
  exact compiled_card_le dec K A statement rel Ext ε hε hExt ht₁ hT

end Bcs
