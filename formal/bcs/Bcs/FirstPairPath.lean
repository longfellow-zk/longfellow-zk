import Bcs.FirstPairCombined

/-! Pathwise query accounting for a grouped parent/response budget. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Finset Merkle.RandomOracle
open scoped Classical

/-- At a fixed oracle, a parent-first query charges the sum of its response
budgets; a child-first query charges one response budget.  Both use the same
`N` queried points.  This is separate from the two-fresh-coordinate
averaging step, so the budget may later be chosen from off-pair field data. -/
theorem tree_first_pair_grouped_path_le
    {Q C Out Parent Response : Type}
    [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    [Fintype Parent] [Fintype Response] {N : ℕ}
    (tree : Tree Q C Out N)
    (parent : Parent → Q) (child : Parent → Response → Q)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective
      (fun i : Parent × Response => child i.1 i.2))
    (hdisjoint : ∀ p p' r, parent p ≠ child p' r)
    (budget : Parent → Response → ℚ)
    (hnonneg : ∀ p r, 0 ≤ budget p r)
    (beta : ℚ) (hbeta : 0 ≤ beta)
    (hsumBudget : ∀ p, ∑ r : Response, budget p r ≤ beta)
    (H : Q → C) :
    (∑ p : Parent, ∑ r : Response,
      if firstOfTwoOffResult tree (parent p) (child p r)
          (hdisjoint p p r) (fun z => H z.1) ≠ .neither then
        budget p r else 0) ≤ (N : ℚ) * beta := by
  classical
  let selected (p : Parent) (r : Response) :=
    firstOfTwoOffResult tree (parent p) (child p r)
      (hdisjoint p p r) (fun z => H z.1)
  let qset := (queried tree H).toFinset
  let parents := (univ : Finset Parent).filter
    (fun p => parent p ∈ qset)
  let children := (univ : Finset (Parent × Response)).filter
    (fun i => child i.1 i.2 ∈ qset)
  have hleft (p : Parent) (r : Response)
      (h : selected p r = .left) : parent p ∈ qset := by
    have hh : firstOfTwo tree H (parent p) (child p r) = .left := by
      rw [← firstOfTwoOff_eq tree (parent p) (child p r)
        (hdisjoint p p r) H]
      exact h
    exact List.mem_toFinset.mpr
      (firstOfTwo_left_mem tree H (parent p) (child p r) hh)
  have hright (p : Parent) (r : Response)
      (h : selected p r = .right) : child p r ∈ qset := by
    have hh : firstOfTwo tree H (parent p) (child p r) = .right := by
      rw [← firstOfTwoOff_eq tree (parent p) (child p r)
        (hdisjoint p p r) H]
      exact h
    exact List.mem_toFinset.mpr
      (firstOfTwo_right_mem tree H (parent p) (child p r) hh)
  have hsingle (p : Parent) (r : Response) : budget p r ≤ beta :=
    (Finset.single_le_sum (fun s _ => hnonneg p s)
      (Finset.mem_univ r)).trans (hsumBudget p)
  have hsplit :
      (∑ p : Parent, ∑ r : Response,
        if selected p r ≠ .neither then budget p r else 0) =
      (∑ p : Parent, ∑ r : Response,
        if selected p r = .left then budget p r else 0) +
      (∑ p : Parent, ∑ r : Response,
        if selected p r = .right then budget p r else 0) := by
    calc
      _ = ∑ p : Parent, ∑ r : Response,
        ((if selected p r = .left then budget p r else 0) +
         (if selected p r = .right then budget p r else 0)) := by
          apply Finset.sum_congr rfl
          intro p _
          apply Finset.sum_congr rfl
          intro r _
          cases h : selected p r <;> simp
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hleftTotal :
      (∑ p : Parent, ∑ r : Response,
        if selected p r = .left then budget p r else 0) ≤
      ∑ p : Parent, if p ∈ parents then beta else 0 := by
    apply Finset.sum_le_sum
    intro p _
    by_cases hp : parent p ∈ qset
    · have hmem : p ∈ parents := by simp [parents, hp]
      simp only [hmem, ↓reduceIte]
      calc
        _ ≤ ∑ r : Response, budget p r := by
          apply Finset.sum_le_sum
          intro r _
          by_cases h : selected p r = .left
          · simp [h]
          · simpa [h] using hnonneg p r
        _ ≤ beta := hsumBudget p
    · have hnot : ∀ r, selected p r ≠ .left := by
        intro r h
        exact hp (hleft p r h)
      have hmem : p ∉ parents := by simp [parents, hp]
      simp [hmem, hnot]
  have hrightTotal :
      (∑ p : Parent, ∑ r : Response,
        if selected p r = .right then budget p r else 0) ≤
      ∑ i : Parent × Response,
        if i ∈ children then beta else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro r _
    by_cases h : selected p r = .right
    · have hmem : (p, r) ∈ children := by
        simp [children, hright p r h]
      simp [h, hmem, hsingle p r]
    · simp only [h, ↓reduceIte]
      split_ifs
      · exact hbeta
      · exact le_refl _
  have hparentCard :
      (parents.image parent).card = parents.card :=
    Finset.card_image_of_injOn
      (fun p _ p' _ heq => hparent heq)
  have hchildCard :
      (children.image (fun i => child i.1 i.2)).card =
        children.card :=
    Finset.card_image_of_injOn
      (fun i _ j _ heq => hchild heq)
  have himagesDisjoint :
      Disjoint (parents.image parent)
        (children.image (fun i => child i.1 i.2)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases Finset.mem_image.mp hx with ⟨p, _, hpx⟩
    rcases Finset.mem_image.mp hy with ⟨i, _, hix⟩
    exact hdisjoint p i.1 i.2 (hpx.trans hix.symm)
  have himageSubset :
      parents.image parent ∪
        children.image (fun i => child i.1 i.2) ⊆ qset := by
    intro x hx
    rcases Finset.mem_union.mp hx with hp | hc
    · rcases Finset.mem_image.mp hp with ⟨p, hpm, hpx⟩
      subst x
      exact (Finset.mem_filter.mp hpm).2
    · rcases Finset.mem_image.mp hc with ⟨i, him, hix⟩
      subst x
      exact (Finset.mem_filter.mp him).2
  have hcard : parents.card + children.card ≤ N := by
    calc
      _ = (parents.image parent).card +
            (children.image (fun i => child i.1 i.2)).card := by
              rw [hparentCard, hchildCard]
      _ = (parents.image parent ∪
            children.image (fun i => child i.1 i.2)).card :=
              (Finset.card_union_of_disjoint himagesDisjoint).symm
      _ ≤ qset.card := Finset.card_le_card himageSubset
      _ ≤ N := (List.toFinset_card_le _).trans (queried_length_le tree H)
  calc
    _ = (∑ p : Parent, ∑ r : Response,
          if selected p r = .left then budget p r else 0) +
        (∑ p : Parent, ∑ r : Response,
          if selected p r = .right then budget p r else 0) := hsplit
    _ ≤ (∑ p : Parent, if p ∈ parents then beta else 0) +
        (∑ i : Parent × Response,
          if i ∈ children then beta else 0) :=
            add_le_add hleftTotal hrightTotal
    _ = (parents.card + children.card : ℚ) * beta := by
      simp [← Finset.sum_filter, Finset.sum_const, parents, children,
        add_mul]
    _ ≤ N * beta :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hbeta

end Bcs.TotalOracle
