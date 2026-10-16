import Lfzk.RbrZkFlatSide
import Bcs.Counting

/-!
# Flat extraction accounting for two fixed Longfellow sides

The key answer may select the public statement seen by both sides.  Once
that answer is fixed, each side has its own independent verifier tape.
Failure of the pair extractor is covered by the key MAC event or by one
accepted side having no satisfying committed lift.  The resulting error is
the sum of the three conditional bounds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrZkFlat

open Finset Lfzk.NizkZk Lfzk.NizkZkTwoField Lfzk.RbrZkSplit
  Lfzk.RbrLayerStepS Lfzk.CertifiedV1
open scoped Classical

variable {R₁ R₂ : Lfzk.CertifiedV1.Row} {logv₁ logv₂ : ℕ}
variable {C Sig : Type} [Fintype C] [Nonempty C]
variable {F₁ X₁ Q₁ Msg₁ Witness₁ : Type} [Field F₁] [Fintype F₁]
  [DecidableEq F₁] [SumcheckInterp F₁] [Fintype X₁] [DecidableEq X₁]
  [Fintype Q₁] [DecidableEq Q₁]
variable {F₂ X₂ Q₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂]
  [DecidableEq F₂] [SumcheckInterp F₂] [Fintype X₂] [DecidableEq X₂]
  [Fintype Q₂] [DecidableEq Q₂]
variable {M₁ ninp₁ logw₁ logc₁ M₂ ninp₂ logw₂ logc₂ : ℕ}

/-- The ordinary round-by-round side remains available for the signature
half while the hash half uses a sharper flat terminal-pair certificate. -/
theorem ZkSide.accepted_ratio_le_core [DecidableEq C]
    {R : Lfzk.CertifiedV1.Row} {logv : ℕ}
    {F X Q Msg Witness : Type} [Field F] [Fintype F] [DecidableEq F]
    [SumcheckInterp F] [Fintype X] [DecidableEq X]
    [Fintype Q] [DecidableEq Q]
    {M ninp logw logc : ℕ}
    (S : ZkSide R logv Sig C F X Q Msg Witness M ninp logw logc)
    (hF : Fintype.card F = R.params.row.fieldSize)
    (σ : Sig) (ms : ℕ → Msg)
    (hfalse : ZkFails S.Sat σ) :
    ((univ.filter fun tape : Fin
      (Rounds.Role.length R.params.nl R.params.rounds) → C =>
        ZkLayerStepAccepts .accepted .start
          (steps (nl := R.params.nl) (w := R.params.rounds)
            (S.V σ) (S.LD σ) ms) tape).card : ℚ) /
      Fintype.card (Fin
        (Rounds.Role.length R.params.nl R.params.rounds) → C) ≤
      zkCoreAt R logv R.cardCand := by
  classical
  let bp := zkPairBudget (Fintype.card C) R.params.row.fieldSize logv
  let br := pairBudget (Fintype.card C) R.params.row.fieldSize
  let bi := inBudget (Fintype.card C) R.params.row.fieldSize
  let bl := ligBudget R.params.row (Fintype.card C)
  let bq := queryBudget R.params.row (Fintype.card C)
  have hraw := ZkFieldData.ratio_le (S.FD σ) (S.LD σ)
    (S.budgets hF σ) ms
    (Acc := fun tape => ZkLayerStepAccepts .accepted .start
      (steps (nl := R.params.nl) (w := R.params.rounds)
        (S.V σ) (S.LD σ) ms) tape)
    (Fails := ZkFails S.Sat σ)
    (fun hf => hf)
    (by intro tape; exact id)
    (by dsimp [Rounds.Role.length]; omega)
  have hraw' :
      ((univ.filter fun tape : Fin
        (Rounds.Role.length R.params.nl R.params.rounds) → C =>
          ZkLayerStepAccepts .accepted .start
            (steps (nl := R.params.nl) (w := R.params.rounds)
              (S.V σ) (S.LD σ) ms) tape).card : ℚ) /
        Fintype.card (Fin
          (Rounds.Role.length R.params.nl R.params.rounds) → C) ≤
      ((Fintype.card (S.Lift σ) *
          (R.params.nl * bp +
            (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * br + bi)
          + bl + bq : ℕ) : ℚ) / Fintype.card C := by
    simpa only [hfalse, and_true, Fintype.card_fun, Fintype.card_fin,
      Nat.cast_pow, bp, br, bi, bl, bq] using hraw
  have hnum : Fintype.card (S.Lift σ) *
      (R.params.nl * bp +
        (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * br + bi) + bl + bq ≤
      R.cardCand *
      (R.params.nl * bp +
        (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * br + bi) + bl + bq := by
    exact Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (S.hcand σ)) _) _
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hcore := budgets_le_zkCore R logv
    (cardC := Fintype.card C) (cardCand := R.cardCand)
    Fintype.card_pos (by rw [← hF]; exact Fintype.card_pos)
  calc
    _ ≤ ((Fintype.card (S.Lift σ) *
          (R.params.nl * bp +
            (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * br + bi)
          + bl + bq : ℕ) : ℚ) / Fintype.card C := hraw'
    _ ≤ ((R.cardCand *
          (R.params.nl * bp +
            (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * br + bi)
          + bl + bq : ℕ) : ℚ) / Fintype.card C :=
        div_le_div_of_nonneg_right (by exact_mod_cast hnum) (le_of_lt hC)
    _ ≤ zkCoreAt R logv R.cardCand := hcore

/-- Fixed-path extraction failure is bounded by one key event and one
accepted, no-satisfying-lift event per side.  No side's candidate count is
charged to the other side's error. -/
theorem twoField_fixedTape_extraction_ratio_le
    (S₁ : ZkSide R₁ logv₁ Sig C F₁ X₁ Q₁ Msg₁ Witness₁
      M₁ ninp₁ logw₁ logc₁)
    (S₂ : ZkSide R₂ logv₂ Sig C F₂ X₂ Q₂ Msg₂ Witness₂
      M₂ ninp₂ logw₂ logc₂)
    (σ : C → Sig) (ms₁ : C → ℕ → Msg₁) (ms₂ : C → ℕ → Msg₂)
    {W : Type}
    (Acc : C →
      (Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C) →
      (Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C) → Prop)
    (extract : C →
      (Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C) →
      (Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C) → Option W)
    (keyBad : C → Prop)
    (keyBound side₁Bound side₂Bound : ℚ)
    (hside₁Nonneg : 0 ≤ side₁Bound) (hside₂Nonneg : 0 ≤ side₂Bound)
    (hkeyCount : ((univ.filter keyBad).card : ℚ) /
      Fintype.card C ≤ keyBound)
    (hside₁Count : ∀ key, ZkFails S₁.Sat (σ key) →
      ((univ.filter fun tape : Fin
        (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C =>
          ZkLayerStepAccepts .accepted .start
            (steps (nl := R₁.params.nl) (w := R₁.params.rounds)
              (S₁.V (σ key)) (S₁.LD (σ key)) (ms₁ key)) tape).card : ℚ) /
        Fintype.card (Fin
          (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C) ≤ side₁Bound)
    (hside₂Count : ∀ key, ZkFails S₂.Sat (σ key) →
      ((univ.filter fun tape : Fin
        (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C =>
          ZkLayerStepAccepts .accepted .start
            (steps (nl := R₂.params.nl) (w := R₂.params.rounds)
              (S₂.V (σ key)) (S₂.LD (σ key)) (ms₂ key)) tape).card : ℚ) /
        Fintype.card (Fin
          (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C) ≤ side₂Bound)
    (hacc₁ : ∀ key tape₁ tape₂, Acc key tape₁ tape₂ →
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₁.params.nl) (w := R₁.params.rounds)
          (S₁.V (σ key)) (S₁.LD (σ key)) (ms₁ key)) tape₁)
    (hacc₂ : ∀ key tape₁ tape₂, Acc key tape₁ tape₂ →
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₂.params.nl) (w := R₂.params.rounds)
          (S₂.V (σ key)) (S₂.LD (σ key)) (ms₂ key)) tape₂)
    (hkey : ∀ key tape₁ tape₂,
      Acc key tape₁ tape₂ → extract key tape₁ tape₂ = none →
      ¬ ZkFails S₁.Sat (σ key) → ¬ ZkFails S₂.Sat (σ key) →
      keyBad key) :
    ((univ.filter fun p : C ×
        ((Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C) ×
         (Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C)) =>
      Acc p.1 p.2.1 p.2.2 ∧ extract p.1 p.2.1 p.2.2 = none).card : ℚ) /
      Fintype.card (C ×
        ((Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C) ×
         (Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C))) ≤
      keyBound + side₁Bound + side₂Bound := by
  classical
  let bad₁ (key : C) (tape : Fin
      (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C) : Prop :=
    ZkFails S₁.Sat (σ key) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₁.params.nl) (w := R₁.params.rounds)
          (S₁.V (σ key)) (S₁.LD (σ key)) (ms₁ key)) tape
  let bad₂ (key : C) (tape : Fin
      (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C) : Prop :=
    ZkFails S₂.Sat (σ key) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₂.params.nl) (w := R₂.params.rounds)
          (S₂.V (σ key)) (S₂.LD (σ key)) (ms₂ key)) tape
  have hb₁ : ∀ key, ((univ.filter (bad₁ key)).card : ℚ) /
      Fintype.card (Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C) ≤
      side₁Bound := by
    intro key
    by_cases hf : ZkFails S₁.Sat (σ key)
    · have heq : (univ.filter (bad₁ key)).card =
          (univ.filter fun tape : Fin
            (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C =>
            ZkLayerStepAccepts .accepted .start
              (steps (nl := R₁.params.nl) (w := R₁.params.rounds)
                (S₁.V (σ key)) (S₁.LD (σ key)) (ms₁ key)) tape).card := by
        congr 1
        ext tape
        simp [bad₁, hf]
      rw [heq]
      exact hside₁Count key hf
    · have hempty : (univ.filter (bad₁ key)) = ∅ := by
        ext tape
        simp [bad₁, hf]
      rw [hempty]
      simpa using hside₁Nonneg
  have hb₂ : ∀ key, ((univ.filter (bad₂ key)).card : ℚ) /
      Fintype.card (Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C) ≤
      side₂Bound := by
    intro key
    by_cases hf : ZkFails S₂.Sat (σ key)
    · have heq : (univ.filter (bad₂ key)).card =
          (univ.filter fun tape : Fin
            (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C =>
            ZkLayerStepAccepts .accepted .start
              (steps (nl := R₂.params.nl) (w := R₂.params.rounds)
                (S₂.V (σ key)) (S₂.LD (σ key)) (ms₂ key)) tape).card := by
        congr 1
        ext tape
        simp [bad₂, hf]
      rw [heq]
      exact hside₂Count key hf
    · have hempty : (univ.filter (bad₂ key)) = ∅ := by
        ext tape
        simp [bad₂, hf]
      rw [hempty]
      simpa using hside₂Nonneg
  have hsub : (univ.filter fun p : C ×
        ((Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C) ×
         (Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C)) =>
        Acc p.1 p.2.1 p.2.2 ∧ extract p.1 p.2.1 p.2.2 = none) ⊆
      (univ.filter fun p =>
        keyBad p.1 ∨ bad₁ p.1 p.2.1 ∨ bad₂ p.1 p.2.2) := by
    intro p hp
    obtain ⟨ha, hx⟩ := (mem_filter.mp hp).2
    by_cases hf₁ : ZkFails S₁.Sat (σ p.1)
    · exact mem_filter.mpr ⟨mem_univ _, Or.inr (Or.inl ⟨hf₁,
        hacc₁ p.1 p.2.1 p.2.2 ha⟩)⟩
    by_cases hf₂ : ZkFails S₂.Sat (σ p.1)
    · exact mem_filter.mpr ⟨mem_univ _, Or.inr (Or.inr ⟨hf₂,
        hacc₂ p.1 p.2.1 p.2.2 ha⟩)⟩
    exact mem_filter.mpr ⟨mem_univ _, Or.inl
      (hkey p.1 p.2.1 p.2.2 ha hx hf₁ hf₂)⟩
  have hpos : (0 : ℚ) < Fintype.card (C ×
      ((Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C) ×
       (Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C))) := by
    exact_mod_cast Fintype.card_pos
  calc
    ((univ.filter fun p : C ×
        ((Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C) ×
         (Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C)) =>
        Acc p.1 p.2.1 p.2.2 ∧ extract p.1 p.2.1 p.2.2 = none).card : ℚ) /
        Fintype.card _
        ≤ ((univ.filter fun p : C ×
          ((Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C) ×
           (Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C)) =>
          keyBad p.1 ∨ bad₁ p.1 p.2.1 ∨ bad₂ p.1 p.2.2).card : ℚ) /
            Fintype.card _ :=
          div_le_div_of_nonneg_right
            (by exact_mod_cast Finset.card_le_card hsub) (le_of_lt hpos)
    _ ≤ keyBound + side₁Bound + side₂Bound :=
      Bcs.key_two_sides_ratio_le keyBad bad₁ bad₂
        keyBound side₁Bound side₂Bound hkeyCount hb₁ hb₂

end Lfzk.RbrZkFlat
