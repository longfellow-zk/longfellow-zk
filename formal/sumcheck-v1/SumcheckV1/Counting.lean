import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting finite events

The plumbing every soundness bound in this repo speaks: an event is a `Finset` of the sample
space, and a bound on it is transported along a *splitting* — a pair of maps `Ω → D` and `Ω → B`
whose product is injective, saying "everything decided before this coin" and "this coin".

Nothing here is about sumcheck, or about any protocol.  It lives in this library because the
Fiat--Shamir count is stated in these terms and there is no smaller place to put it.

`event_card_le_split` is the workhorse: it bounds an event on an arbitrary `Ω` by a count over a
product it merely *factors through*, at no cost when the maps really do split.  `card_of_split_bij`
is the strengthening to a bijection, which is what turns a count into a probability, and
`split_injective_not_pinning` is the witness that the weaker form really is weaker.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true

open Classical

namespace SumcheckV1

variable {Ω : Type} [Fintype Ω]

/-- The size of an event.  A one-line alias, but it names the thing every bound is about. -/
noncomputable def event_card (E : Finset Ω) : ℕ := E.card

lemma card_filter_comp {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) (P : β → Prop) :
    (Finset.filter (fun x => P (f x)) Finset.univ).card =
    ∑ y ∈ Finset.filter P Finset.univ, (Finset.filter (fun x => f x = y) Finset.univ).card := by
  have h_union : Finset.filter (fun x => P (f x)) Finset.univ =
    Finset.biUnion (Finset.filter P Finset.univ) (fun y => Finset.filter (fun x => f x = y) Finset.univ) := by
    ext x
    simp
  rw [h_union]
  apply Finset.card_biUnion
  intro y1 hy1 y2 hy2 hne
  apply Finset.disjoint_left.mpr
  intro x hx1 hx2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
  exact hne (hx1.symm.trans hx2)

lemma card_prod_filter {α β : Type*} [Fintype α] [Fintype β] (P : α → β → Prop) :
    (Finset.filter (fun (pr : α × β) => P pr.1 pr.2) Finset.univ).card =
    ∑ a : α, (Finset.filter (fun b => P a b) Finset.univ).card := by
  have h_union : Finset.filter (fun (pr : α × β) => P pr.1 pr.2) Finset.univ =
    Finset.biUnion Finset.univ (fun a => (Finset.filter (fun b => P a b) Finset.univ).map ⟨fun b => (a, b), fun b1 b2 h => Prod.mk.inj h |>.2⟩) := by
    ext ⟨a, b⟩
    simp
  rw [h_union]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro a _
    rw [Finset.card_map]
  · intro a1 _ a2 _ hne
    apply Finset.disjoint_left.mpr
    intro ⟨x, y⟩ hx1 hx2
    rw [Finset.mem_map] at hx1 hx2
    rcases hx1 with ⟨b1, _, h1⟩
    rcases hx2 with ⟨b2, _, h2⟩
    dsimp at h1 h2
    exact hne ((congr_arg Prod.fst h1).trans (congr_arg Prod.fst h2).symm)

lemma pairs_card_le {D F : Type} [Fintype D] [Fintype F] (Q : D → F → Prop)
    (hQ : ∀ d : D, (Finset.filter (fun a : F => Q d a) Finset.univ).card ≤ 1) :
    (Finset.filter (fun p : D × F => Q p.1 p.2) Finset.univ).card ≤ Fintype.card D := by
  rw [card_prod_filter Q]
  calc ∑ d : D, (Finset.filter (fun a : F => Q d a) Finset.univ).card
      ≤ ∑ _d : D, 1 := Finset.sum_le_sum (fun d _ => hQ d)
    _ = Fintype.card D := by simp

lemma pairs_card_le_mul {D C : Type} [Fintype D] [Fintype C] (Q : D → C → Prop) (m : ℕ)
    (hQ : ∀ d : D, (Finset.filter (fun a : C => Q d a) Finset.univ).card ≤ m) :
    (Finset.filter (fun p : D × C => Q p.1 p.2) Finset.univ).card ≤ Fintype.card D * m := by
  rw [card_prod_filter Q]
  calc ∑ d : D, (Finset.filter (fun a : C => Q d a) Finset.univ).card
      ≤ ∑ _d : D, m := Finset.sum_le_sum (fun d _ => hQ d)
    _ = Fintype.card D * m := by simp [mul_comm]

lemma option_bad_pairs_card {D F A : Type} [Fintype D] [Fintype F]
    (E : D → Option A) (P : D → A → F → Prop)
    (hP : ∀ (d : D) (v : A), (Finset.filter (fun a : F => P d v a) Finset.univ).card ≤ 1) :
    (Finset.filter (fun p : D × F => ∃ v, E p.1 = some v ∧ P p.1 v p.2) Finset.univ).card
      ≤ Fintype.card D := by
  have h := pairs_card_le (D := D) (F := F) (fun d a => ∃ v, E d = some v ∧ P d v a)
    (fun d => by
      cases hd : E d with
      | none =>
        refine le_trans (Finset.card_le_card (t := (∅ : Finset F)) ?_) (by simp)
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        obtain ⟨v, hv, -⟩ := ha
        exact absurd hv (by simp)
      | some v =>
        refine le_trans (Finset.card_le_card
          (t := Finset.filter (fun a : F => P d v a) Finset.univ) ?_) (hP d v)
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        obtain ⟨u, hu, hPu⟩ := ha
        cases Option.some.inj hu
        exact hPu)
  convert h using 2
  congr!

lemma option_bad_pairs_card_mul {D A C : Type} [Fintype D] [Fintype C] (E : D → Option A)
    (P : D → A → C → Prop) (m : ℕ)
    (hP : ∀ (d : D) (v : A), (Finset.filter (fun a : C => P d v a) Finset.univ).card ≤ m) :
    (Finset.filter (fun p : D × C => ∃ v, E p.1 = some v ∧ P p.1 v p.2) Finset.univ).card
      ≤ Fintype.card D * m := by
  have h := pairs_card_le_mul (D := D) (C := C) (fun d a => ∃ v, E d = some v ∧ P d v a) m
    (fun d => by
      cases hd : E d with
      | none =>
        refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        obtain ⟨v, hv, -⟩ := ha
        exact absurd hv (by simp)
      | some v =>
        refine le_trans (Finset.card_le_card
          (t := Finset.filter (fun a : C => P d v a) Finset.univ) ?_) (hP d v)
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        obtain ⟨u, hu, hPu⟩ := ha
        cases Option.some.inj hu
        exact hPu)
  convert h using 2
  congr!

lemma card_filter_fst_le {X Y : Type} [Fintype X] [Fintype Y] (Q : X → Prop)
    [DecidablePred Q] [DecidablePred (fun ω : X × Y => Q ω.1)] (m : ℕ)
    (h : (Finset.filter Q Finset.univ).card ≤ m) :
    (Finset.filter (fun ω : X × Y => Q ω.1) Finset.univ).card ≤ m * Fintype.card Y := by
  have hprod : (Finset.filter (fun ω : X × Y => Q ω.1) Finset.univ)
      = (Finset.filter Q Finset.univ) ×ˢ (Finset.univ : Finset Y) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, and_true]
  rw [hprod, Finset.card_product, Finset.card_univ]
  exact Nat.mul_le_mul_right _ h

lemma card_le_of_split {Ω A B : Type} [Fintype Ω] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (data : Ω → A) (alpha : Ω → B) (K : ℕ)
    (huni : ∀ (d : A) (a : B),
      (Finset.filter (fun ω => data ω = d ∧ alpha ω = a) Finset.univ).card ≤ K)
    (Q : A × B → Prop) :
    (Finset.filter (fun ω => Q (data ω, alpha ω)) Finset.univ).card
      ≤ K * (Finset.filter Q Finset.univ).card := by
  rw [card_filter_comp (fun ω => (data ω, alpha ω)) Q]
  calc ∑ y ∈ Finset.filter Q Finset.univ,
        (Finset.filter (fun ω => (data ω, alpha ω) = y) Finset.univ).card
      ≤ ∑ _y ∈ Finset.filter Q Finset.univ, K := by
        refine Finset.sum_le_sum (fun y _ => ?_)
        have h : (Finset.filter (fun ω => (data ω, alpha ω) = y) Finset.univ)
            = Finset.filter (fun ω => data ω = y.1 ∧ alpha ω = y.2) Finset.univ := by
          ext ω; simp [Prod.ext_iff]
        rw [h]; exact huni y.1 y.2
    _ = (Finset.filter Q Finset.univ).card * K := by simp [Finset.sum_const, mul_comm]
    _ = K * (Finset.filter Q Finset.univ).card := by ring

lemma event_card_le_split {D B : Type} [Fintype D] [Fintype B]
    [DecidableEq D] [DecidableEq B]
    (dataOf : Ω → D) (coordOf : Ω → B)
    (hinj : Function.Injective (fun ω => (dataOf ω, coordOf ω)))
    (P : Ω → Prop) (Q : D × B → Prop) (hPQ : ∀ ω, P ω → Q (dataOf ω, coordOf ω)) (m : ℕ)
    (hQ : (Finset.filter Q Finset.univ).card ≤ m) :
    event_card (Finset.filter P Finset.univ) ≤ m := by
  classical
  have hsub : Finset.filter P Finset.univ
      ⊆ Finset.filter (fun ω => Q (dataOf ω, coordOf ω)) Finset.univ := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact hPQ ω hω
  have hK : ∀ (d : D) (a : B),
      (Finset.filter (fun ω => dataOf ω = d ∧ coordOf ω = a) Finset.univ).card ≤ 1 := by
    intro d a
    refine Finset.card_le_one.mpr (fun x hx y hy => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    refine hinj ?_
    show (dataOf x, coordOf x) = (dataOf y, coordOf y)
    rw [hx.1, hx.2, hy.1, hy.2]
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (card_le_of_split dataOf coordOf 1 hK Q) ?_
  rw [one_mul]
  exact hQ

theorem split_injective_not_pinning :
    Function.Injective (fun _ : Unit => ((), true))
      ∧ Fintype.card Unit ≠ Fintype.card Unit * Fintype.card Bool := by
  refine ⟨fun a b _ => Subsingleton.elim a b, ?_⟩
  decide

lemma card_of_split_bij {D B : Type} [Fintype D] [Fintype B]
    (dataOf : Ω → D) (coordOf : Ω → B)
    (hbij : Function.Bijective (fun ω => (dataOf ω, coordOf ω))) :
    Fintype.card Ω = Fintype.card D * Fintype.card B := by
  rw [← Fintype.card_prod]
  exact Fintype.card_of_bijective hbij

end SumcheckV1
