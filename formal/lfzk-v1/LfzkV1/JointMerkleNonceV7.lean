import LfzkV1.JointMerkleHidingV7
import Bcs.TotalOracle
import Bcs.StatisticalDistance

/-! A single post-proof nonce charge across the two typed v7 trees. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LfzkV1.JointMerkleHidingV7

open Finset Merkle.MH Merkle.RandomOracle Bcs.TotalOracle SumcheckV1
open scoped Classical

section Counting

variable {Index Salt Enc D Out : Type}

/-- This oracle takes salts only for the actual disclosed leaves. -/
def openedOracle (address : Index → Salt → Enc) (opened : Finset Index)
    (H : Enc → D) (leaves : Index → D) (revealed : opened → Salt) : Enc → D :=
  program (fun i : opened => address i.val (revealed i)) (fun _ => True) H (leaves ∘ Subtype.val)

private theorem openedOracle_eq (address : Index → Salt → Enc) (opened : Finset Index)
    (H : Enc → D) (leaves : Index → D) (salts : Index → Salt)
    (unique : Function.Injective (fun i => address i (salts i))) :
    openedOracle address opened H leaves (fun i => salts i.val) =
      program (fun i => address i (salts i)) (fun i => i ∈ opened) H leaves := by
  funext raw
  by_cases present : ∃ i : opened, address i.val (salts i.val) = raw
  · obtain ⟨i, rfl⟩ := present
    have injective : Function.Injective (fun j : opened => address j.val (salts j.val)) :=
      fun _ _ h => Subtype.ext (unique h)
    unfold openedOracle
    rw [program_at _ _ _ _ injective i trivial, program_at _ _ _ _ unique i.val i.property]
    rfl
  · unfold openedOracle
    rw [program_off _ _ _ _ _ (fun i _ h => present ⟨i, h⟩),
      program_off _ _ _ _ _ (fun i hi h => present ⟨⟨i, hi⟩, h⟩)]

variable [Fintype Index] [DecidableEq Index] [Fintype Salt]

private def guesses (decode : Enc → Option (Index × Salt)) (queries : List Enc)
    (i : Index) : Finset Salt :=
  (((queries.filterMap decode).toFinset).filter fun p => p.1 = i).image Prod.snd

omit [Fintype Salt] in
private theorem guesses_sum_le (decode : Enc → Option (Index × Salt)) (queries : List Enc) :
    ∑ i : Index, (guesses decode queries i).card ≤ queries.length := by
  let pairs := (queries.filterMap decode).toFinset
  calc
    _ ≤ ∑ i : Index, (pairs.filter fun p => p.1 = i).card :=
      sum_le_sum fun _ _ => card_image_le
    _ = pairs.card := (card_eq_sum_card_fiberwise
      (f := Prod.fst) (s := pairs) (t := univ) (fun _ _ => mem_univ _)).symm
    _ ≤ (queries.filterMap decode).length := List.toFinset_card_le _
    _ ≤ queries.length := List.length_filterMap_le _ _

variable (decode : Enc → Option (Index × Salt)) (opened : Finset Index)
variable (later : (opened → Salt) → List Enc)

private def bad (i : Index) (salts : Index → Salt) (salt : Salt) : Prop :=
  i ∉ opened ∧ salt ∈ guesses decode (later (fun j => salts j.val)) i

omit [Fintype Index] [Fintype Salt] in
private theorem bad_off (i : Index) (s t : Index → Salt) (off : AgreeOff i s t) (salt : Salt)
    (hb : bad decode opened later i s salt) : bad decode opened later i t salt := by
  have hs : (fun j : opened => s j.val) = fun j => t j.val :=
    funext fun j => off j.val (fun he => hb.1 (he ▸ j.property))
  exact ⟨hb.1, hs ▸ hb.2⟩

omit [Fintype Index] in
private theorem bad_local (i : Index) (s : Index → Salt) :
    (univ.filter (bad decode opened later i s)).card ≤
      (guesses decode (later (fun j => s j.val)) i).card := by
  apply card_le_card
  intro salt ha
  exact (mem_filter.mp ha).2.2

/-- There is one guess per observer query, across both trees. Once the
disclosures are fixed, the later trace reads no hidden nonce. -/
private theorem salt_hits_card_mul_le (Q : ℕ) (bounded : ∀ revealed, (later revealed).length ≤ Q) :
    (univ.filter fun salts : Index → Salt =>
      ∃ i, bad decode opened later i salts (salts i)).card * Fintype.card Salt ≤
      Q * Fintype.card Salt ^ Fintype.card Index := by
  exact card_exists_coord_le
    (bad decode opened later) (bad_off decode opened later)
    (fun i salts => (guesses decode (later (fun j => salts j.val)) i).card)
    (bad_local decode opened later) Q
    (fun salts => (guesses_sum_le decode _).trans (bounded (fun j => salts j.val)))

variable {Q : ℕ}

/-- On fixed public coins and injective payloads, couple any adaptive
observer to the opened-only simulation. Its full trace is included. -/
theorem fixed_observer_close [Nonempty Salt]
    (address : Index → Salt → Enc)
    (injective : Function.Injective (Function.uncurry address))
    (H : Enc → D) (leaves : Index → D)
    (observer : (opened → Salt) → Tree Enc D Out Q) :
    StatClose ((Q : ℚ) / Fintype.card Salt)
      (fun s : Index → Salt => (observer (fun j => s j.val)).run
        (swapEquiv (fun i => address i (s i)) (H, leaves)).1)
      (fun s : Index → Salt => (observer (fun j => s j.val)).run
        (openedOracle address opened H leaves (fun j => s j.val))) := by
  let decode := Function.partialInv (Function.uncurry address)
  have decoded (i : Index) (s : Salt) : decode (address i s) = some (i, s) :=
    Function.partialInv_left injective (i, s)
  have unique (s : Index → Salt) : Function.Injective (fun i => address i (s i)) :=
    fun i j eq => congrArg Prod.fst (@injective (i, s i) (j, s j) eq)
  let publicTrace (shown : opened → Salt) :=
    ((observer shown).run (openedOracle address opened H leaves shown)).2.map Prod.fst
  let hit (s : Index → Salt) := ∃ i, bad decode opened publicTrace i s (s i)
  have hcount := salt_hits_card_mul_le decode opened publicTrace Q
    (fun shown => queried_length_le (observer shown) _)
  have hpos : (0 : ℚ) < Fintype.card Salt := by exact_mod_cast Fintype.card_pos
  have hratio : ((univ.filter hit).card : ℚ) / Fintype.card (Index → Salt) ≤
      (Q : ℚ) / Fintype.card Salt := by
    rw [Fintype.card_fun, Nat.cast_pow, div_le_div_iff₀ (pow_pos hpos _) hpos]
    exact_mod_cast hcount
  apply StatClose.mono hratio
  apply zkClose_statClose
  refine ⟨Equiv.refl _, card_le_card ?_⟩
  intro s hs
  simp only [Equiv.refl_apply, mem_filter, mem_univ, true_and] at hs ⊢
  by_contra miss
  apply hs
  symm
  rw [swap_oracle_of_injective _ (unique s), openedOracle_eq address opened H leaves s (unique s)]
  refine run_program_eq_of_no_hidden_hit _ _ H leaves (unique s) _ ?_
  intro qa hqa i hidden he
  apply miss
  have actual : qa.1 ∈ publicTrace (fun j => s j.val) := by
    unfold publicTrace
    rw [openedOracle_eq address opened H leaves s (unique s)]
    exact List.mem_map.mpr ⟨qa, hqa, rfl⟩
  refine ⟨i, hidden, mem_image.mpr ⟨(i, s i), mem_filter.mpr ⟨?_, rfl⟩, rfl⟩⟩
  apply List.mem_toFinset.mpr
  exact List.mem_filterMap.mpr ⟨qa.1, actual, he ▸ decoded i (s i)⟩

end Counting

private theorem prob_bounds {R V : Type} [Fintype R] (f : R → V) (P : V → Prop) :
    0 ≤ probOf f P ∧ probOf f P ≤ 1 := by
  unfold probOf
  constructor
  · positivity
  · rcases Nat.eq_zero_or_pos (Fintype.card R) with hR | hR
    · simp [hR]
    · have hRq : (0 : ℚ) < Fintype.card R := by exact_mod_cast hR
      apply (div_le_iff₀ hRq).2
      rw [one_mul]
      exact_mod_cast (Finset.card_filter_le (s := (univ : Finset R)) (fun r => P (f r)))

/-- Condition on a uniform shared coin. The good fibres contribute their
common statistical bound, and all remaining fibres contribute at most one. -/
theorem statClose_mix_bad {A R S V : Type} [Fintype A] [Fintype R] [Fintype S]
    (good : A → Prop) (e : ℚ) (he : 0 ≤ e) (real : A → R → V) (sim : A → S → V)
    (close : ∀ a, good a → StatClose e (real a) (sim a)) :
    StatClose (e + probOf (id : A → A) (fun a => ¬ good a))
      (fun p : A × R => real p.1 p.2) (fun p : A × S => sim p.1 p.2) := by
  intro P
  rw [probOf_prod real P, probOf_prod sim P]
  rcases Nat.eq_zero_or_pos (Fintype.card A) with hA | hA
  · simp [hA, he, probOf]
  have hAq : (0 : ℚ) < Fintype.card A := by exact_mod_cast hA
  let bump (a : A) : ℚ := if good a then 0 else 1
  have hb : ∑ a : A, bump a = ((univ.filter fun a : A => ¬ good a).card : ℚ) := by
    rw [card_filter, Nat.cast_sum]
    apply sum_congr rfl
    intro a _
    by_cases hg : good a <;> simp [bump, hg]
  have hlocal (a : A) : |probOf (real a) P - probOf (sim a) P| ≤ e + bump a := by
    by_cases hg : good a
    · simpa only [bump, if_pos hg, add_zero] using close a hg P
    · obtain ⟨hr0, hr1⟩ := prob_bounds (real a) P
      obtain ⟨hs0, hs1⟩ := prob_bounds (sim a) P
      simp only [bump, if_neg hg, abs_le]
      constructor <;> linarith
  rw [div_sub_div_same, ← sum_sub_distrib, abs_div, abs_of_pos hAq]
  calc
    _ ≤ (∑ a : A, |probOf (real a) P - probOf (sim a) P|) / Fintype.card A :=
      div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hAq.le
    _ ≤ (∑ a : A, (e + bump a)) / Fintype.card A :=
      div_le_div_of_nonneg_right (sum_le_sum fun a _ => hlocal a) hAq.le
    _ = _ := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, card_univ, hb, add_div,
        mul_div_cancel_left₀ _ hAq.ne', probOf]
      apply congrArg (fun n : ℕ => e + (n : ℚ) / Fintype.card A)
      apply congrArg Finset.card
      ext a
      simp only [mem_filter, mem_univ, true_and, id_eq]

end LfzkV1.JointMerkleHidingV7
