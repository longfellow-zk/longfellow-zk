import Bcs.FirstPairQuery
import Bcs.PotentialOracle
import Bcs.TwoFreshCoordinates
import LfzkV1.NizkDeployedHash
import LfzkV1.NizkZk

/-!
# A canonical continuation's opening query

Once the initial point has been queried, the canonical continuation can
determine at most one terminal response for a secondary lift. When the
initial point was queried before the corresponding opening point, that
opening costs its fresh probability, even if it is later queried adaptively.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.CanonicalOpening125

open Bcs.TotalOracle Finset Merkle.RandomOracle
attribute [local instance 10000] Classical.propDecidable

variable {Q C Out : Type} [Fintype Q] [DecidableEq Q] [Fintype C]
variable {fuel : ℕ}

omit [Fintype Q] [Fintype C] in
/-- The selected opening may be appended after the adversary stops. An
observed initial input still determines an order for the pair. -/
theorem firstOfTwo_of_initial_observed (tree : Tree Q C Out fuel) (H : Q → C)
    (init opening : Q) (h : init ∈ queried tree H) :
    firstOfTwo tree H init opening = .left ∨ firstOfTwo tree H init opening = .right := by
  induction tree with
  | done _ => simp at h
  | query q next ih =>
    by_cases hi : q = init
    · exact Or.inl (by simp only [firstOfTwo, if_pos hi])
    · by_cases hj : q = opening
      · exact Or.inr (by simp only [firstOfTwo, if_neg hi, if_pos hj])
      · have hm := (List.mem_cons.mp (by simpa only [queried_query] using h)).resolve_left (Ne.symm hi)
        simpa only [firstOfTwo, if_neg hi, if_neg hj] using ih (H q) hm

omit [Fintype Q] [Fintype C] in
/-- Two points naming the same cut can both be held out when the cut is
independent of each point's own answer. -/
theorem cut_eq_of_off_pair {Key Cut : Type} (key : Q → Key) (cut : (Q → C) → Key → Cut)
    (one : ∀ z H H', AgreeOff z H H' → cut H (key z) = cut H' (key z))
    (x y : Q) (hkey : key x = key y) (H H' : Q → C)
    (off : ∀ z, z ≠ x → z ≠ y → H z = H' z) :
    cut H (key x) = cut H' (key x) := by
  let mid := Function.update H x (H' x)
  have h₁ : AgreeOff x H mid := agreeOff_update x H (H' x)
  have h₂ : AgreeOff y mid H' := by
    intro z hz
    by_cases h : z = x
    · subst z
      exact Function.update_self x (H' x) H
    · exact (Function.update_of_ne h (H' x) H).trans (off z h hz)
  exact (one x H mid h₁).trans (by rw [hkey]; exact one y mid H' h₂)

section ParentFirst

variable {P R : Type} [Fintype P] [Fintype R]

private theorem sum_opening_le
    (child : P → R → Q) (active : P → R → (Q → C) → Prop)
    (ready : P → (Q → C) → Prop) (good : P → R → (Q → C) → C → Prop)
    (ρ : ℚ) (hρ : 0 ≤ ρ)
    (hactive : ∀ p r H H', AgreeOff (child p r) H H' →
      (active p r H ↔ active p r H'))
    (hgood : ∀ p r H H', AgreeOff (child p r) H H' → active p r H →
      ∀ c, (good p r H c ↔ good p r H' c))
    (hlocal : ∀ p r H, active p r H →
      ∑ c : C, (if good p r H c then (1 : ℚ) else 0) ≤ Fintype.card C * ρ)
    (hunique : ∀ p H, (univ.filter fun r => active p r H).card ≤ 1)
    (hready : ∀ p r H, active p r H → ready p H)
    (hq : (0 : ℚ) < Fintype.card C) :
    (∑ H : Q → C, ∑ p : P, ∑ r : R,
      if active p r H ∧ good p r H (H (child p r)) then (1 : ℚ) else 0) ≤
      ρ * ∑ H : Q → C, ∑ p : P, if ready p H then (1 : ℚ) else 0 := by
  let weight (p : P) (r : R) (H : Q → C) (c : C) : ℚ :=
    if active p r H ∧ good p r H c then 1 else 0
  have fiber (p : P) (r : R) :
      (∑ H : Q → C, weight p r H (H (child p r))) ≤
        ∑ H : Q → C, if active p r H then ρ else 0 := by
    apply le_of_mul_le_mul_right ?_ hq
    rw [sum_coord_mul_rat (child p r) (weight p r), Finset.sum_mul]
    · apply Finset.sum_le_sum
      intro H _
      by_cases h : active p r H
      · simpa [weight, h, mul_comm] using hlocal p r H h
      · simp [weight, h]
    · intro H H' hoff c
      by_cases h : active p r H
      · simp only [weight, h, (hactive p r H H' hoff).mp h, true_and,
          hgood p r H H' hoff h c]
      · simp [weight, h, (hactive p r H H' hoff).not.mp h]
  have hsum (p : P) (H : Q → C) :
      (∑ r : R, if active p r H then ρ else 0) ≤
        ρ * (if ready p H then (1 : ℚ) else 0) := by
    by_cases h : ready p H
    · rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, h, if_true, mul_one]
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hunique p H) hρ).trans_eq
        (one_mul _)
    · have hn (r : R) : ¬ active p r H := fun ha => h (hready p r H ha)
      simp [hn, h]
  change (∑ H : Q → C, ∑ p : P, ∑ r : R, weight p r H (H (child p r))) ≤ _
  calc
    _ = ∑ p : P, ∑ r : R, ∑ H : Q → C, weight p r H (H (child p r)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ ≤ ∑ p : P, ∑ r : R, ∑ H : Q → C, if active p r H then ρ else 0 :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun r _ => fiber p r
    _ = ∑ H : Q → C, ∑ p : P, ∑ r : R, if active p r H then ρ else 0 := by
      symm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ ≤ _ := by
      simp only [Finset.mul_sum]
      exact Finset.sum_le_sum fun H _ => Finset.sum_le_sum fun p _ => hsum p H

/-- Relative bound for the parent-first case. The right side retains the
original initial-escape charge so that it can be combined with the other
uses of the same adaptive query counter. -/
theorem parentFirst_sum_le [Nonempty C]
    (tree : Tree Q C Out fuel) (initial : P → Q) (child : P → R → Q)
    (select : P → (Q → C) → Option R)
    (escape : P → (Q → C) → C → Prop) (good : P → R → (Q → C) → C → Prop)
    (ρ : ℚ) (hρ : 0 ≤ ρ) (hne : ∀ p r, child p r ≠ initial p)
    (hselect : ∀ p r H H', AgreeOff (child p r) H H' →
      firstOfTwo tree H (initial p) (child p r) = .left → select p H = select p H')
    (hescape : ∀ p r H H', AgreeOff (child p r) H H' →
      firstOfTwo tree H (initial p) (child p r) = .left → ∀ a, (escape p H a ↔ escape p H' a))
    (hgood : ∀ p r H H', AgreeOff (child p r) H H' →
      firstOfTwo tree H (initial p) (child p r) = .left → select p H = some r →
      ∀ c, (good p r H c ↔ good p r H' c))
    (hlocal : ∀ p r H, firstOfTwo tree H (initial p) (child p r) = .left → select p H = some r →
      ∑ c : C, (if good p r H c then (1 : ℚ) else 0) ≤ Fintype.card C * ρ) :
    (∑ H : Q → C, ∑ p : P, ∑ r : R,
      if (firstOfTwo tree H (initial p) (child p r) = .left ∧ select p H = some r ∧
        escape p H (H (initial p))) ∧ good p r H (H (child p r)) then (1 : ℚ) else 0) ≤
      ρ * ∑ H : Q → C, ∑ p : P,
        if initial p ∈ queried tree H ∧ escape p H (H (initial p)) then (1 : ℚ) else 0 := by
  refine sum_opening_le child
    (fun p r H => firstOfTwo tree H (initial p) (child p r) = .left ∧ select p H = some r ∧
      escape p H (H (initial p)))
    (fun p H => initial p ∈ queried tree H ∧ escape p H (H (initial p))) good ρ hρ ?_ ?_ ?_ ?_ ?_
    (by exact_mod_cast Fintype.card_pos)
  · intro p r H H' hoff
    have hf := firstOfTwo_congr_off tree H H' (initial p) (child p r) (fun q _ hq => hoff q hq)
    have hp := hoff (initial p) (hne p r).symm
    constructor
    · rintro ⟨hfirst, hs, he⟩
      exact ⟨hf ▸ hfirst, (hselect p r H H' hoff hfirst) ▸ hs,
        hp ▸ (hescape p r H H' hoff hfirst _).mp he⟩
    · rintro ⟨hfirst', hs, he⟩
      have hfirst := hf.symm ▸ hfirst'
      exact ⟨hfirst, (hselect p r H H' hoff hfirst).symm ▸ hs,
        (hescape p r H H' hoff hfirst _).mpr (hp.symm ▸ he)⟩
  · rintro p r H H' hoff ⟨hfirst, hs, _⟩
    exact hgood p r H H' hoff hfirst hs
  · rintro p r H ⟨hfirst, hs, _⟩
    exact hlocal p r H hfirst hs
  · intro p H
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact Option.some.inj ((mem_filter.mp ha).2.2.1.symm.trans (mem_filter.mp hb).2.2.1)
  · rintro p r H ⟨hfirst, _, he⟩
    exact ⟨firstOfTwo_left_mem tree H (initial p) (child p r) hfirst, he⟩

/-- The canonical opening can be specified by a relation. Its uniqueness
and invariance under reprogramming imply the selector premises. -/
theorem parentFirst_relation_sum_le [Nonempty C]
    (tree : Tree Q C Out fuel) (initial : P → Q) (child : P → R → Q)
    (eligible : P → R → (Q → C) → Prop)
    (escape : P → (Q → C) → C → Prop) (good : P → R → (Q → C) → C → Prop)
    (ρ : ℚ) (hρ : 0 ≤ ρ) (hne : ∀ p r, child p r ≠ initial p)
    (hunique : ∀ p H r s, eligible p r H → eligible p s H → r = s)
    (hstable : ∀ p r H H', AgreeOff (child p r) H H' →
      firstOfTwo tree H (initial p) (child p r) = .left →
      ∀ s, eligible p s H ↔ eligible p s H')
    (hescape : ∀ p r H H', AgreeOff (child p r) H H' →
      firstOfTwo tree H (initial p) (child p r) = .left → ∀ a, (escape p H a ↔ escape p H' a))
    (hgood : ∀ p r H H', AgreeOff (child p r) H H' →
      firstOfTwo tree H (initial p) (child p r) = .left → eligible p r H →
      ∀ c, (good p r H c ↔ good p r H' c))
    (hlocal : ∀ p r H, firstOfTwo tree H (initial p) (child p r) = .left → eligible p r H →
      ∑ c : C, (if good p r H c then (1 : ℚ) else 0) ≤ Fintype.card C * ρ) :
    (∑ H : Q → C, ∑ p : P, ∑ r : R,
      if (firstOfTwo tree H (initial p) (child p r) = .left ∧ eligible p r H ∧
        escape p H (H (initial p))) ∧ good p r H (H (child p r)) then (1 : ℚ) else 0) ≤
      ρ * ∑ H : Q → C, ∑ p : P,
        if initial p ∈ queried tree H ∧ escape p H (H (initial p)) then (1 : ℚ) else 0 := by
  let select (p : P) (H : Q → C) : Option R :=
    if he : ∃ r, eligible p r H then some he.choose else none
  have hselect (p : P) (H : Q → C) (r : R) : select p H = some r ↔ eligible p r H := by
    by_cases he : ∃ r, eligible p r H
    · rw [show select p H = some he.choose by simp only [select, dif_pos he], Option.some.injEq]
      constructor
      · rintro rfl
        exact he.choose_spec
      · exact hunique p H _ _ he.choose_spec
    · simp only [select, dif_neg he, reduceCtorEq, false_iff]
      exact fun hr => he ⟨r, hr⟩
  have hstab (p : P) (r : R) (H H' : Q → C) (hoff : AgreeOff (child p r) H H')
      (hfirst : firstOfTwo tree H (initial p) (child p r) = .left) : select p H = select p H' := by
    cases hs : select p H with
    | none =>
      cases hs' : select p H' with
      | none => rfl
      | some s =>
        have he := (hstable p r H H' hoff hfirst s).mpr ((hselect p H' s).mp hs')
        exact False.elim (by simpa only [hs, reduceCtorEq] using (hselect p H s).mpr he)
    | some s =>
      exact ((hselect p H' s).mpr ((hstable p r H H' hoff hfirst s).mp
        ((hselect p H s).mp hs))).symm
  simpa only [hselect] using parentFirst_sum_le tree initial child select escape good ρ hρ hne
    hstab hescape (fun p r H H' hoff hfirst hs => hgood p r H H' hoff hfirst ((hselect p H r).mp hs))
    (fun p r H hf hs => hlocal p r H hf ((hselect p H r).mp hs))

end ParentFirst

/-- A causal event retains the exact expected count of its eligible inputs
for the shared role counter. Eligibility cannot read the input's answer. -/
theorem causal_sum_le {P : Type} [Fintype P] [Nonempty C]
    (point : P → Q) (charge : P → (Q → C) → Prop)
    (hcharge : ∀ p H H', AgreeOff (point p) H H' → (charge p H ↔ charge p H'))
    (event : P → (Q → C) → C → Prop) (η : ℚ)
    (hoff : ∀ p H H', AgreeOff (point p) H H' → ∀ a, event p H a ↔ event p H' a)
    (hlocal : ∀ p H, ∑ a : C, (if event p H a then (1 : ℚ) else 0) ≤ Fintype.card C * η) :
    (∑ H : Q → C, ∑ p : P,
      if charge p H ∧ event p H (H (point p)) then (1 : ℚ) else 0) ≤
      η * ∑ H : Q → C, ∑ p : P, if charge p H then (1 : ℚ) else 0 := by
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_comm, Finset.sum_comm (f := fun H p =>
    if charge p H then (1 : ℚ) else 0), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  let f (H : Q → C) (a : C) :=
    if charge p H ∧ event p H a then (1 : ℚ) else 0
  change (∑ H : Q → C, f H (H (point p))) ≤ η * _
  apply le_of_mul_le_mul_right ?_ hC
  rw [sum_coord_mul_rat (point p) f, Finset.mul_sum, Finset.sum_mul]
  · apply Finset.sum_le_sum
    intro H _
    by_cases hs : charge p H
    · simpa only [f, hs, true_and, if_true, mul_one, mul_comm] using hlocal p H
    · simp [f, hs]
  · intro H H' h a
    simp only [f, hcharge p H H' h, hoff p H H' h a]

/-- Conditioning at an observed query preserves the original expected
query count. -/
theorem observed_local_sum_le {P : Type} [Fintype P] [Nonempty C]
    (tree : Tree Q C Out fuel) (point : P → Q)
    (event : P → (Q → C) → C → Prop) (η : ℚ)
    (hoff : ∀ p H H', AgreeOff (point p) H H' → ∀ a, event p H a ↔ event p H' a)
    (hlocal : ∀ p H, ∑ a : C, (if event p H a then (1 : ℚ) else 0) ≤ Fintype.card C * η) :
    (∑ H : Q → C, ∑ p : P,
      if point p ∈ queried tree H ∧ event p H (H (point p)) then (1 : ℚ) else 0) ≤
      η * ∑ H : Q → C, ∑ p : P, if point p ∈ queried tree H then (1 : ℚ) else 0 :=
  causal_sum_le point (fun p H => point p ∈ queried tree H)
    (fun p _ _ h => mem_queried_iff tree (point p) h) event η hoff hlocal

/-- One selected point may be appended to the observed inputs. If it
was missing from search, reprogramming its answer preserves the output. -/
theorem selected_local_sum_le {P : Type} [Fintype P] [Nonempty C]
    (tree : Tree Q C Out fuel) (point : P → Q) (selected : Out → P)
    (event : P → (Q → C) → C → Prop) (η : ℚ) (hη : 0 ≤ η)
    (hoff : ∀ p H H', AgreeOff (point p) H H' → ∀ a, event p H a ↔ event p H' a)
    (hlocal : ∀ p H, ∑ a : C, (if event p H a then (1 : ℚ) else 0) ≤ Fintype.card C * η) :
    (∑ H : Q → C,
      if event (selected (tree.run H).1) H (H (point (selected (tree.run H).1))) then (1 : ℚ) else 0) ≤
      η * ∑ H : Q → C, ((∑ p : P, if point p ∈ queried tree H then (1 : ℚ) else 0) + 1) := by
  let charge (p : P) (H : Q → C) := point p ∈ queried tree H ∨ selected (tree.run H).1 = p
  have hcharge (p : P) (H H' : Q → C) (h : AgreeOff (point p) H H') : charge p H ↔ charge p H' := by
    have hm := mem_queried_iff tree (point p) h
    by_cases hs : point p ∈ queried tree H
    · simp [charge, hs, hm.mp hs]
    · simp [charge, hs, hm.not.mp hs, run_eq_of_not_mem tree (point p) h hs]
  have hh := causal_sum_le point charge hcharge event η hoff hlocal
  refine le_trans (Finset.sum_le_sum ?_) (hh.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) hη))
  · intro H _
    let p := selected (tree.run H).1
    exact (by simp [p, charge] :
      (if event p H (H (point p)) then (1 : ℚ) else 0) =
        (if charge p H ∧ event p H (H (point p)) then (1 : ℚ) else 0)).le.trans
        (Finset.single_le_sum (f := fun r =>
          if charge r H ∧ event r H (H (point r)) then (1 : ℚ) else 0)
          (fun _ _ => by split <;> positivity) (Finset.mem_univ p))
  · intro H _
    calc
      _ ≤ ∑ p : P, ((if point p ∈ queried tree H then (1 : ℚ) else 0) +
          (if selected (tree.run H).1 = p then (1 : ℚ) else 0)) := by
        apply Finset.sum_le_sum
        intro p _
        by_cases ha : point p ∈ queried tree H <;> by_cases hb : selected (tree.run H).1 = p <;>
          simp [charge, ha, hb]
      _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- If the opening fixes the initial prefix and was queried first, freeze
everything outside those two points. The bad initial draw and the small
opening tail then multiply. The right side keeps the number of selected
opening queries for combination with the common query budget. -/
theorem openingFirst_sum_le {I : Type} [Fintype I]
    (parent child : I → Q) (hne : ∀ x, parent x ≠ child x)
    (active : ∀ x, (AwayFromTwo (parent x) (child x) → C) → Prop)
    (escape good : ∀ x, (AwayFromTwo (parent x) (child x) → C) → C → Prop)
    (η ρ : ℚ) (hη : 0 ≤ η)
    (hescape : ∀ x off, active x off →
      ∑ a : C, (if escape x off a then (1 : ℚ) else 0) ≤ Fintype.card C * η)
    (hgood : ∀ x off, active x off →
      ∑ b : C, (if good x off b then (1 : ℚ) else 0) ≤ Fintype.card C * ρ) :
    (∑ H : Q → C, ∑ x : I,
      if active x (fun z => H z.val) ∧ escape x (fun z => H z.val) (H (parent x)) ∧
        good x (fun z => H z.val) (H (child x)) then (1 : ℚ) else 0) ≤
      η * ρ * ∑ H : Q → C, ∑ x : I,
        if active x (fun z => H z.val) then (1 : ℚ) else 0 := by
  let q : ℚ := Fintype.card C
  have hq : 0 ≤ q := Nat.cast_nonneg _
  conv_rhs => rw [Finset.sum_comm, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  let I (condition : Prop) : ℚ := if condition then 1 else 0
  change (∑ H : Q → C, I (active x _ ∧ escape x _ (H (parent x)) ∧ good x _ (H (child x)))) ≤
    η * ρ * ∑ H : Q → C, I (active x (fun z => H z.val))
  rw [sum_two_fresh_weight (parent x) (child x) (hne x)
    (fun off a b => I (active x off ∧ escape x off a ∧ good x off b)),
    sum_two_fresh_weight (parent x) (child x) (hne x) (fun off _ _ => I (active x off)), mul_sum]
  apply Finset.sum_le_sum
  intro off _
  by_cases ha : active x off
  · have hi (a b : C) : I (active x off ∧ escape x off a ∧ good x off b) =
        I (escape x off a) * I (good x off b) := by
      by_cases he : escape x off a <;> by_cases hg : good x off b <;> simp [I, ha, he, hg]
    simp only [hi, ← mul_sum, ← sum_mul]
    have hprod := mul_le_mul (hescape x off ha) (hgood x off ha)
      (sum_nonneg fun b _ => by
        change 0 ≤ I (good x off b)
        unfold I
        split_ifs <;> norm_num) (mul_nonneg hq hη)
    simpa only [I, ha, if_true, sum_const, card_univ, nsmul_eq_mul, mul_one,
      mul_assoc, mul_left_comm, mul_comm] using hprod
  · simp [I, ha]

/-- An opening address already fixes its initial prefix. At the same
commitment cut, holding out both replies makes the two costs multiply. -/
theorem openingFirst_cut_sum_le {I Key Cut : Type} [Fintype I] [Nonempty C]
    (tree : Tree Q C Out fuel) (parent child : I → Q) (hne : ∀ x, parent x ≠ child x)
    (key : Q → Key) (cut : (Q → C) → Key → Cut)
    (hkey : ∀ x, key (parent x) = key (child x))
    (hcut : ∀ q H H', AgreeOff q H H' → cut H (key q) = cut H' (key q))
    (escape good : I → Cut → C → Prop) (η ρ : ℚ) (hη : 0 ≤ η)
    (hescape : ∀ x ct, ∑ a : C, (if escape x ct a then (1 : ℚ) else 0) ≤ Fintype.card C * η)
    (hgood : ∀ x ct, ∑ b : C, (if good x ct b then (1 : ℚ) else 0) ≤ Fintype.card C * ρ) :
    (∑ H : Q → C, ∑ x : I,
      if firstOfTwo tree H (parent x) (child x) = .right ∧
        escape x (cut H (key (parent x))) (H (parent x)) ∧
        good x (cut H (key (parent x))) (H (child x)) then (1 : ℚ) else 0) ≤
      η * ρ * ∑ H : Q → C, ∑ x : I,
        if firstOfTwo tree H (parent x) (child x) = .right then (1 : ℚ) else 0 := by
  let out (x : I) (off : AwayFromTwo (parent x) (child x) → C) : Q → C :=
    (splitTwo (parent x) (child x) (hne x)).symm
      (off, Classical.arbitrary C, Classical.arbitrary C)
  have hoff (x : I) (H : Q → C) (q : Q) (hp : q ≠ parent x) (hc : q ≠ child x) :
      H q = out x (fun z => H z.val) q := by simp [out, splitTwo, hp, hc]
  have hfirst (x : I) (H : Q → C) :
      firstOfTwo tree (out x (fun z => H z.val)) (parent x) (child x) =
        firstOfTwo tree H (parent x) (child x) :=
    (firstOfTwo_congr_off tree H _ (parent x) (child x) (hoff x H)).symm
  have hsame (x : I) (H : Q → C) :
      cut (out x (fun z => H z.val)) (key (parent x)) = cut H (key (parent x)) :=
    (cut_eq_of_off_pair key cut hcut (parent x) (child x) (hkey x) H _ (hoff x H)).symm
  have h := openingFirst_sum_le parent child hne
    (fun x off => firstOfTwo tree (out x off) (parent x) (child x) = .right)
    (fun x off => escape x (cut (out x off) (key (parent x))))
    (fun x off => good x (cut (out x off) (key (parent x)))) η ρ hη
    (fun x off _ => hescape x (cut (out x off) (key (parent x))))
    (fun x off _ => hgood x (cut (out x off) (key (parent x))))
  simpa only [hfirst, hsame] using h

section Prefix

open LfzkV1.NizkDeployedHash

variable {Ctx Msg : Type} [Inhabited Msg] {nl : ℕ} {widths : ℕ → ℕ}

private noncomputable def point (ctx : Ctx) (msgs : ℕ → Msg) (i : ℕ) :
    MPoint Ctx Msg nl widths := msgPoint ctx (fun f j => f j) msgs i

/-- The hash input at a slot depends only on messages through that slot. -/
theorem msgPoint_eq_of_prefix (ctx : Ctx) {a b : ℕ → Msg} {i : ℕ}
    (h : ∀ j ≤ i, a j = b j) :
    msgPoint (nl := nl) (w := widths) ctx (fun f j => f j) a i =
      msgPoint ctx (fun f j => f j) b i := by
  unfold msgPoint
  congr 1
  funext j
  by_cases hj : j.val ≤ i
  · simpa only [padMsgs, if_pos hj] using h j.val hj
  · simp only [padMsgs, if_neg hj]

omit [Fintype C] in
/-- The state reconstructed at a legacy hash input is the verifier's
actual state before that role. This holds even if the adversary queried
the point before any of its ancestors. -/
theorem state_at_msgPoint {State Lift : Type}
    (chainOf : (ℕ → Msg) → Bcs.ClaimChain C (Rounds.Role.length nl widths) State Lift)
    (hloc : LfzkV1.NizkZk.MsgLocal chainOf)
    (ctx : Ctx) (H : MPoint Ctx Msg nl widths → C) (msgs : ℕ → Msg)
    (k : Fin (Rounds.Role.length nl widths)) :
    let p := point ctx msgs k.val
    (chainOf p.msgFn).state p.role.slot (mpoints.chal H p) =
      (chainOf msgs).state k.val (fun j => H (point ctx msgs j.val)) := by
  dsimp only
  let p := point (nl := nl) (widths := widths) ctx msgs k.val
  have hslot : p.role.slot = k.val := slot_msgPoint ctx (fun f i => f i) msgs k.isLt
  have hm : ∀ j < p.role.slot, p.msgFn j = msgs j := by
    intro j hj
    have hj' : j < k.val := hslot ▸ hj
    exact msgFn_msgPoint ctx (fun f i => f i) msgs (k := k.val) (i := j) k.isLt hj'.le
  let coins (s : ℕ) (j : Fin s) : C := H (point ctx msgs j.val)
  have hcoins : mpoints.chal H p = coins p.role.slot := by
    funext j
    have hj : j.val < k.val := hslot ▸ j.isLt
    exact congrArg H (anc_msgPoint ctx (fun f i => f i) msgs hj k.isLt)
  change (chainOf p.msgFn).state p.role.slot (mpoints.chal H p) = _
  rw [LfzkV1.NizkZk.state_congrG hloc _ hm, hcoins, hslot]

end Prefix

end LfzkV1.CanonicalOpening125
