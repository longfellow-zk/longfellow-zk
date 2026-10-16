import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Slicing a product sample space

The compiled experiment's sample space is `(Fin T → D) × (Challenge × Query)`: the hash tape, then
the verifier's external coins.  The two error terms are counted along the two different slicings —
`Merkle`'s bound is per coin pair, over tapes; the IOP's is per tape, over coins — so both are
needed, and they are the same lemma up to `Finset.sum_comm`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open Finset

/-- Count a product event by slicing on the first coordinate.

Stated with the predicate applied to a *pair* rather than curried, so that `rw` unifies it
first-order against a filter that is already there. -/
theorem card_filter_prod_fst {α β : Type*} [Fintype α] [Fintype β]
    (P : α × β → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ a : α, (univ.filter fun b ↦ P (a, b)).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type]

/-- Count a product event by slicing on the second coordinate. -/
theorem card_filter_prod_snd {α β : Type*} [Fintype α] [Fintype β]
    (P : α × β → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ b : β, (univ.filter fun a ↦ P (a, b)).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- A uniform probability bound on every second-coordinate fiber remains
valid after adjoining an independent first coordinate. -/
theorem product_ratio_le_of_fst_fiber
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (event : α → β → Prop) [∀ a, DecidablePred (event a)]
    (epsilon : ℚ)
    (hfiber : ∀ a, ((univ.filter (event a)).card : ℚ) /
      Fintype.card β ≤ epsilon) :
    ((univ.filter fun value : α × β ↦ event value.1 value.2).card : ℚ) /
        Fintype.card (α × β) ≤ epsilon := by
  classical
  have hα : (0 : ℚ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  have hβ : (0 : ℚ) < Fintype.card β := by
    exact_mod_cast Fintype.card_pos
  rw [card_filter_prod_fst, Fintype.card_prod]
  push_cast
  rw [div_le_iff₀ (mul_pos hα hβ)]
  calc
    (∑ a : α, ((univ.filter (event a)).card : ℚ))
        ≤ ∑ _a : α, epsilon * Fintype.card β := by
          apply Finset.sum_le_sum
          intro a _
          exact (div_le_iff₀ hβ).mp (hfiber a)
    _ = epsilon * (Fintype.card α * Fintype.card β) := by
      simp
      ring

/-- Symmetric product-space averaging, slicing on the second coordinate. -/
theorem product_ratio_le_of_snd_fiber
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (event : α → β → Prop) [∀ b, DecidablePred (fun a ↦ event a b)]
    (epsilon : ℚ)
    (hfiber : ∀ b, ((univ.filter fun a ↦ event a b).card : ℚ) /
      Fintype.card α ≤ epsilon) :
    ((univ.filter fun value : α × β ↦ event value.1 value.2).card : ℚ) /
        Fintype.card (α × β) ≤ epsilon := by
  classical
  have hα : (0 : ℚ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  have hβ : (0 : ℚ) < Fintype.card β := by
    exact_mod_cast Fintype.card_pos
  rw [card_filter_prod_snd, Fintype.card_prod]
  push_cast
  rw [div_le_iff₀ (mul_pos hα hβ)]
  calc
    (∑ b : β, ((univ.filter fun a : α ↦ event a b).card : ℚ))
        ≤ ∑ _b : β, epsilon * Fintype.card α := by
          apply Finset.sum_le_sum
          intro b _
          exact (div_le_iff₀ hα).mp (hfiber b)
    _ = epsilon * (Fintype.card α * Fintype.card β) := by
      simp
      ring

/-- A fixed prefix can be charged either to an earlier field-round escape
or to one joint terminal experiment.  A uniform bound on the terminal
fiber is averaged over prefixes without taking a maximum over challenge
answers or splitting the terminal pair into two independent charges. -/
theorem prefix_or_terminal_ratio_le
    {Prefix Pair : Type*} [Fintype Prefix] [Fintype Pair]
    [Nonempty Prefix] [Nonempty Pair]
    (fieldEscape : Prefix → Prop)
    (terminal : Prefix → Pair → Prop)
    [DecidablePred fieldEscape] [∀ pref, DecidablePred (terminal pref)]
    (fieldBound terminalBound : ℚ)
    (hfield : ((univ.filter fieldEscape).card : ℚ) /
      Fintype.card Prefix ≤ fieldBound)
    (hterminal : ∀ pref,
      ((univ.filter (terminal pref)).card : ℚ) /
        Fintype.card Pair ≤ terminalBound) :
    ((univ.filter fun p : Prefix × Pair =>
      fieldEscape p.1 ∨ terminal p.1 p.2).card : ℚ) /
        Fintype.card (Prefix × Pair) ≤ fieldBound + terminalBound := by
  classical
  let fieldSet : Finset (Prefix × Pair) :=
    univ.filter fun p => fieldEscape p.1
  let terminalSet : Finset (Prefix × Pair) :=
    univ.filter fun p => terminal p.1 p.2
  have hfield' : (fieldSet.card : ℚ) /
      Fintype.card (Prefix × Pair) ≤ fieldBound := by
    exact product_ratio_le_of_snd_fiber
      (fun pref (_ : Pair) => fieldEscape pref) fieldBound
      (by intro _; exact hfield)
  have hterminal' : (terminalSet.card : ℚ) /
      Fintype.card (Prefix × Pair) ≤ terminalBound := by
    exact product_ratio_le_of_fst_fiber terminal terminalBound hterminal
  have hsub :
      (univ.filter fun p : Prefix × Pair =>
        fieldEscape p.1 ∨ terminal p.1 p.2) ⊆
          fieldSet ∪ terminalSet := by
    intro p hp
    obtain ⟨_, hp⟩ := Finset.mem_filter.mp hp
    rcases hp with hp | hp
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨mem_univ _, hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨mem_univ _, hp⟩)
  have hcard :
      (univ.filter fun p : Prefix × Pair =>
        fieldEscape p.1 ∨ terminal p.1 p.2).card ≤
          fieldSet.card + terminalSet.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hden : (0 : ℚ) < Fintype.card (Prefix × Pair) := by
    exact_mod_cast Fintype.card_pos
  calc
    ((univ.filter fun p : Prefix × Pair =>
      fieldEscape p.1 ∨ terminal p.1 p.2).card : ℚ) /
        Fintype.card (Prefix × Pair)
        ≤ ((fieldSet.card : ℚ) + terminalSet.card) /
            Fintype.card (Prefix × Pair) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt hden)
    _ = (fieldSet.card : ℚ) / Fintype.card (Prefix × Pair) +
        (terminalSet.card : ℚ) / Fintype.card (Prefix × Pair) := by ring
    _ ≤ fieldBound + terminalBound := add_le_add hfield' hterminal'

/-- Three sequentially exposed independent answer blocks can be charged
separately when the first event uses only the first block, the second may
also use the first, and the third may use the first but not the second.  In
particular, a fixed key can select both side verifiers without multiplying
either side's extraction error by the other's candidate-list size. -/
theorem key_two_sides_ratio_le
    {Key Side₁ Side₂ : Type*}
    [Fintype Key] [Fintype Side₁] [Fintype Side₂]
    [Nonempty Key] [Nonempty Side₁] [Nonempty Side₂]
    (keyBad : Key → Prop)
    (side₁Bad : Key → Side₁ → Prop)
    (side₂Bad : Key → Side₂ → Prop)
    [DecidablePred keyBad]
    [∀ key, DecidablePred (side₁Bad key)]
    [∀ key, DecidablePred (side₂Bad key)]
    (keyBound side₁Bound side₂Bound : ℚ)
    (hkey : ((univ.filter keyBad).card : ℚ) /
      Fintype.card Key ≤ keyBound)
    (hside₁ : ∀ key, ((univ.filter (side₁Bad key)).card : ℚ) /
      Fintype.card Side₁ ≤ side₁Bound)
    (hside₂ : ∀ key, ((univ.filter (side₂Bad key)).card : ℚ) /
      Fintype.card Side₂ ≤ side₂Bound) :
    ((univ.filter fun p : Key × (Side₁ × Side₂) =>
      keyBad p.1 ∨ side₁Bad p.1 p.2.1 ∨ side₂Bad p.1 p.2.2).card : ℚ) /
        Fintype.card (Key × (Side₁ × Side₂)) ≤
      keyBound + side₁Bound + side₂Bound := by
  classical
  have hsides (key : Key) :
      ((univ.filter fun p : Side₁ × Side₂ =>
        side₁Bad key p.1 ∨ side₂Bad key p.2).card : ℚ) /
          Fintype.card (Side₁ × Side₂) ≤ side₁Bound + side₂Bound := by
    exact prefix_or_terminal_ratio_le (Prefix := Side₁) (Pair := Side₂)
      (side₁Bad key)
      (fun _ side₂ => side₂Bad key side₂) side₁Bound side₂Bound
      (hside₁ key) (by intro _; exact hside₂ key)
  simpa only [add_assoc] using
    (prefix_or_terminal_ratio_le (Prefix := Key) (Pair := Side₁ × Side₂) keyBad
      (fun key p => side₁Bad key p.1 ∨ side₂Bad key p.2)
      keyBound (side₁Bound + side₂Bound) hkey hsides)

/-- Splitting a uniformly sampled indexed tape into two consecutive blocks. -/
noncomputable def splitTape (C : Type*) (m n : ℕ) :
    (Fin (m + n) → C) ≃ (Fin m → C) × (Fin n → C) :=
  ((Equiv.piCongrLeft (fun _ : Fin (m + n) => C)
    (finSumFinEquiv (m := m) (n := n))).symm).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) C)

/-- The verifier's key answer and its two side tapes are three independent
blocks of one uniformly sampled indexed tape. -/
noncomputable def threeBlockTapeEquiv (C : Type*) (a b : ℕ) :
    (Fin (1 + a + b) → C) ≃ C × ((Fin a → C) × (Fin b → C)) :=
  (splitTape C (1 + a) b).trans
    ((Equiv.prodCongr (splitTape C 1 a) (Equiv.refl _)).trans
      ((Equiv.prodAssoc (Fin 1 → C) (Fin a → C) (Fin b → C)).trans
        (Equiv.prodCongr (Equiv.funUnique (Fin 1) C) (Equiv.refl _))))

@[simp] theorem threeBlockTapeEquiv_key {C : Type*} {a b : ℕ}
    (tape : Fin (1 + a + b) → C) :
    (threeBlockTapeEquiv C a b tape).1 = tape ⟨0, by omega⟩ := by
  rfl

@[simp] theorem threeBlockTapeEquiv_side₁ {C : Type*} {a b : ℕ}
    (tape : Fin (1 + a + b) → C) (j : Fin a) :
    (threeBlockTapeEquiv C a b tape).2.1 j =
      tape ⟨1 + j.val, by omega⟩ := by
  rfl

@[simp] theorem threeBlockTapeEquiv_side₂ {C : Type*} {a b : ℕ}
    (tape : Fin (1 + a + b) → C) (j : Fin b) :
    (threeBlockTapeEquiv C a b tape).2.2 j =
      tape ⟨1 + a + j.val, by omega⟩ := by
  rfl

/-- Transfer an already proved bound on a key-and-two-sides event to any
covered event on the merged verifier tape.  This is the interface between a
fixed-tape extraction theorem and the zero-query Fiat--Shamir sampler. -/
theorem three_block_tape_ratio_le_of_product_bound
    {C : Type*} [Fintype C] [Nonempty C] {a b : ℕ}
    (event : (Fin (1 + a + b) → C) → Prop)
    (productEvent : C × ((Fin a → C) × (Fin b → C)) → Prop)
    [DecidablePred event] [DecidablePred productEvent]
    (bound : ℚ)
    (hcover : ∀ tape, event tape →
      productEvent (threeBlockTapeEquiv C a b tape))
    (hproduct : ((univ.filter productEvent).card : ℚ) /
      Fintype.card (C × ((Fin a → C) × (Fin b → C))) ≤ bound) :
    ((univ.filter event).card : ℚ) /
      Fintype.card (Fin (1 + a + b) → C) ≤ bound := by
  classical
  let e := threeBlockTapeEquiv C a b
  have hsub : univ.filter event ⊆
      univ.filter (fun tape => productEvent (e tape)) := by
    intro tape ht
    exact mem_filter.mpr ⟨mem_univ _, hcover tape (mem_filter.mp ht).2⟩
  have hcard := Finset.card_le_card hsub
  have himage : (univ.filter (fun tape => productEvent (e tape))).card =
      (univ.filter productEvent).card :=
    Finset.card_equiv e (fun _ => by simp)
  have hden : Fintype.card (Fin (1 + a + b) → C) =
      Fintype.card (C × ((Fin a → C) × (Fin b → C))) :=
    Fintype.card_congr e
  have hpos : (0 : ℚ) < Fintype.card (Fin (1 + a + b) → C) := by
    exact_mod_cast Fintype.card_pos
  calc
    ((univ.filter event).card : ℚ) /
        Fintype.card (Fin (1 + a + b) → C)
      ≤ ((univ.filter (fun tape => productEvent (e tape))).card : ℚ) /
          Fintype.card (Fin (1 + a + b) → C) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt hpos)
    _ = ((univ.filter productEvent).card : ℚ) /
        Fintype.card (C × ((Fin a → C) × (Fin b → C))) := by
      rw [himage, hden]
    _ ≤ bound := hproduct

/-- A covered event on the merged tape inherits the sum of a key bound and
two conditional side bounds, with no extra factor for their ordering. -/
theorem three_block_tape_ratio_le
    {C : Type*} [Fintype C] [Nonempty C]
    {a b : ℕ}
    (event : (Fin (1 + a + b) → C) → Prop)
    (keyBad : C → Prop)
    (side₁Bad : C → (Fin a → C) → Prop)
    (side₂Bad : C → (Fin b → C) → Prop)
    [DecidablePred event] [DecidablePred keyBad]
    [∀ key, DecidablePred (side₁Bad key)]
    [∀ key, DecidablePred (side₂Bad key)]
    (keyBound side₁Bound side₂Bound : ℚ)
    (hcover : ∀ tape, event tape →
      let p := threeBlockTapeEquiv C a b tape
      keyBad p.1 ∨ side₁Bad p.1 p.2.1 ∨ side₂Bad p.1 p.2.2)
    (hkey : ((univ.filter keyBad).card : ℚ) / Fintype.card C ≤ keyBound)
    (hside₁ : ∀ key, ((univ.filter (side₁Bad key)).card : ℚ) /
      Fintype.card (Fin a → C) ≤ side₁Bound)
    (hside₂ : ∀ key, ((univ.filter (side₂Bad key)).card : ℚ) /
      Fintype.card (Fin b → C) ≤ side₂Bound) :
    ((univ.filter event).card : ℚ) / Fintype.card (Fin (1 + a + b) → C) ≤
      keyBound + side₁Bound + side₂Bound := by
  classical
  let e := threeBlockTapeEquiv C a b
  let bad : C × ((Fin a → C) × (Fin b → C)) → Prop := fun p =>
    keyBad p.1 ∨ side₁Bad p.1 p.2.1 ∨ side₂Bad p.1 p.2.2
  have hsub : univ.filter event ⊆ univ.filter (fun tape => bad (e tape)) := by
    intro tape ht
    exact mem_filter.mpr ⟨mem_univ _, hcover tape (mem_filter.mp ht).2⟩
  have hcard := Finset.card_le_card hsub
  have himage : (univ.filter (fun tape => bad (e tape))).card =
      (univ.filter bad).card := Finset.card_equiv e (fun _ => by simp)
  have hden : Fintype.card (Fin (1 + a + b) → C) =
      Fintype.card (C × ((Fin a → C) × (Fin b → C))) :=
    Fintype.card_congr e
  have hpos : (0 : ℚ) < Fintype.card (Fin (1 + a + b) → C) := by
    exact_mod_cast Fintype.card_pos
  calc
    ((univ.filter event).card : ℚ) / Fintype.card (Fin (1 + a + b) → C)
        ≤ ((univ.filter (fun tape => bad (e tape))).card : ℚ) /
            Fintype.card (Fin (1 + a + b) → C) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt hpos)
    _ = ((univ.filter bad).card : ℚ) /
          Fintype.card (C × ((Fin a → C) × (Fin b → C))) := by
        rw [himage, hden]
    _ ≤ keyBound + side₁Bound + side₂Bound :=
      key_two_sides_ratio_le keyBad side₁Bad side₂Bad
        keyBound side₁Bound side₂Bound hkey hside₁ hside₂

end Bcs
