import LigeroFamily.Soundness.FiniteCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Cast.Order

/-!
# Disjoint event ledgers

This module supplies the protocol-neutral finite counting boundary used by
Ligero acceptance and extraction bounds.

`ThreeEventPartition` records three named, pairwise-disjoint events whose union
is exactly the winning event.  `FlatEventLedger` adds the fiber bounds needed
when the sample space is a uniform product `Challenge × Query`.
-/

namespace LigeroFamily

open Finset

/-- Three pairwise-disjoint semantic causes of a winning execution. -/
structure ThreeEventPartition (Ω : Type*) where
  win : Ω → Prop
  allErrors : Ω → Prop
  linearErrors : Ω → Prop
  badAlpha : Ω → Prop
  win_iff : ∀ ω, win ω ↔ allErrors ω ∨ linearErrors ω ∨ badAlpha ω
  all_linear_disjoint : ∀ ω, allErrors ω → ¬ linearErrors ω
  all_bad_disjoint : ∀ ω, allErrors ω → ¬ badAlpha ω
  linear_bad_disjoint : ∀ ω, linearErrors ω → ¬ badAlpha ω

namespace ThreeEventPartition

variable {Ω : Type*} [Fintype Ω]

noncomputable def winSet (P : ThreeEventPartition Ω) : Finset Ω := by
  classical
  exact univ.filter P.win

noncomputable def allErrorsSet (P : ThreeEventPartition Ω) : Finset Ω := by
  classical
  exact univ.filter P.allErrors

noncomputable def linearErrorsSet (P : ThreeEventPartition Ω) : Finset Ω := by
  classical
  exact univ.filter P.linearErrors

noncomputable def badAlphaSet (P : ThreeEventPartition Ω) : Finset Ω := by
  classical
  exact univ.filter P.badAlpha

theorem winSet_eq_union [DecidableEq Ω] (P : ThreeEventPartition Ω) :
    P.winSet = P.allErrorsSet ∪ P.linearErrorsSet ∪ P.badAlphaSet := by
  classical
  ext ω
  simp only [winSet, allErrorsSet, linearErrorsSet, badAlphaSet,
    mem_filter, mem_univ, true_and, mem_union]
  simpa [or_assoc] using P.win_iff ω

theorem disjoint_all_linear (P : ThreeEventPartition Ω) :
    Disjoint P.allErrorsSet P.linearErrorsSet := by
  classical
  rw [Finset.disjoint_left]
  intro ω hall hlinear
  exact P.all_linear_disjoint ω (mem_filter.mp hall).2 (mem_filter.mp hlinear).2

theorem disjoint_all_bad (P : ThreeEventPartition Ω) :
    Disjoint P.allErrorsSet P.badAlphaSet := by
  classical
  rw [Finset.disjoint_left]
  intro ω hall hbad
  exact P.all_bad_disjoint ω (mem_filter.mp hall).2 (mem_filter.mp hbad).2

theorem disjoint_linear_bad (P : ThreeEventPartition Ω) :
    Disjoint P.linearErrorsSet P.badAlphaSet := by
  classical
  rw [Finset.disjoint_left]
  intro ω hlinear hbad
  exact P.linear_bad_disjoint ω (mem_filter.mp hlinear).2 (mem_filter.mp hbad).2

/-- Exact cardinality identity for the semantic trichotomy. -/
theorem card_winSet (P : ThreeEventPartition Ω) :
    P.winSet.card = P.allErrorsSet.card + P.linearErrorsSet.card +
      P.badAlphaSet.card := by
  classical
  rw [P.winSet_eq_union]
  have hleft : Disjoint (P.allErrorsSet ∪ P.linearErrorsSet) P.badAlphaSet := by
    rw [Finset.disjoint_union_left]
    exact ⟨P.disjoint_all_bad, P.disjoint_linear_bad⟩
  rw [Finset.card_union_of_disjoint hleft,
    Finset.card_union_of_disjoint P.disjoint_all_linear]

end ThreeEventPartition

noncomputable def eventFiber {Challenge Query : Type*} [Fintype Query]
    (event : Challenge × Query → Prop) (challenge : Challenge) : Finset Query := by
  classical
  exact univ.filter fun query => event (challenge, query)

/-- Fiberwise data for flat counting on `Challenge × Query`.

The two query-covered events receive arbitrary per-challenge budgets.  The
third event is contained in `exceptional × Query`, so it is charged by an
exact exceptional-challenge count rather than by another query cover.
-/
structure FlatEventLedger (Challenge Query : Type*)
    [Fintype Challenge] [Fintype Query] where
  partition : ThreeEventPartition (Challenge × Query)
  allBudget : Challenge → ℕ
  linearBudget : Challenge → ℕ
  exceptional : Finset Challenge
  all_fiber_card : ∀ challenge,
    (eventFiber partition.allErrors challenge).card ≤ allBudget challenge
  linear_fiber_card : ∀ challenge,
    (eventFiber partition.linearErrors challenge).card ≤ linearBudget challenge
  badAlpha_exceptional : ∀ challenge query,
    partition.badAlpha (challenge, query) → challenge ∈ exceptional

namespace FlatEventLedger

variable {Challenge Query : Type*}
variable [Fintype Challenge] [Fintype Query]

theorem allErrors_card_le (L : FlatEventLedger Challenge Query) :
    L.partition.allErrorsSet.card ≤ ∑ challenge, L.allBudget challenge := by
  classical
  change (univ.filter fun pair : Challenge × Query =>
    L.partition.allErrors pair).card ≤ _
  rw [Internal.card_filter_product_eq_sum
    (fun challenge query => L.partition.allErrors (challenge, query))]
  exact Finset.sum_le_sum fun challenge _ => by
    simpa [eventFiber] using L.all_fiber_card challenge

theorem linearErrors_card_le (L : FlatEventLedger Challenge Query) :
    L.partition.linearErrorsSet.card ≤ ∑ challenge, L.linearBudget challenge := by
  classical
  change (univ.filter fun pair : Challenge × Query =>
    L.partition.linearErrors pair).card ≤ _
  rw [Internal.card_filter_product_eq_sum
    (fun challenge query => L.partition.linearErrors (challenge, query))]
  exact Finset.sum_le_sum fun challenge _ => by
    simpa [eventFiber] using L.linear_fiber_card challenge

theorem badAlpha_card_le (L : FlatEventLedger Challenge Query) :
    L.partition.badAlphaSet.card ≤ L.exceptional.card * Fintype.card Query := by
  classical
  let rectangle : Finset (Challenge × Query) := L.exceptional ×ˢ univ
  calc
    L.partition.badAlphaSet.card ≤ rectangle.card := by
      apply Finset.card_le_card
      intro pair hpair
      have hbad := (Finset.mem_filter.mp hpair).2
      exact Finset.mem_product.mpr
        ⟨L.badAlpha_exceptional pair.1 pair.2 hbad, Finset.mem_univ _⟩
    _ = L.exceptional.card * Fintype.card Query := by simp [rectangle]

/-- Flat finite-cardinality bound obtained from the exact semantic partition. -/
theorem win_card_le (L : FlatEventLedger Challenge Query) :
    L.partition.winSet.card ≤
      (∑ challenge, L.allBudget challenge) +
      (∑ challenge, L.linearBudget challenge) +
      L.exceptional.card * Fintype.card Query := by
  rw [L.partition.card_winSet]
  exact Nat.add_le_add (Nat.add_le_add L.allErrors_card_le
    L.linearErrors_card_le) L.badAlpha_card_le

/-- Probability form of the flat event-ledger bound. -/
theorem win_ratio_le [Nonempty Challenge] [Nonempty Query]
    (L : FlatEventLedger Challenge Query) :
    (L.partition.winSet.card : ℚ) /
        ((Fintype.card Challenge : ℚ) * Fintype.card Query) ≤
      (((∑ challenge, L.allBudget challenge) +
        (∑ challenge, L.linearBudget challenge) +
        L.exceptional.card * Fintype.card Query : ℕ) : ℚ) /
          ((Fintype.card Challenge : ℚ) * Fintype.card Query) := by
  have hChallenge : (0 : ℚ) < Fintype.card Challenge := by
    exact_mod_cast Fintype.card_pos
  have hQuery : (0 : ℚ) < Fintype.card Query := by
    exact_mod_cast Fintype.card_pos
  have hnum : (L.partition.winSet.card : ℚ) ≤
      ((∑ challenge, L.allBudget challenge) +
        (∑ challenge, L.linearBudget challenge) +
        L.exceptional.card * Fintype.card Query : ℕ) := by
    exact_mod_cast L.win_card_le
  exact div_le_div_of_nonneg_right hnum (mul_pos hChallenge hQuery).le

/-- A uniform-budget relaxation of `win_card_le`. -/
theorem win_card_le_uniform (L : FlatEventLedger Challenge Query)
    (allBound linearBound exceptionalBound : ℕ)
    (hall : ∀ challenge, L.allBudget challenge ≤ allBound)
    (hlinear : ∀ challenge, L.linearBudget challenge ≤ linearBound)
    (hexceptional : L.exceptional.card ≤ exceptionalBound) :
    L.partition.winSet.card ≤
      Fintype.card Challenge * (allBound + linearBound) +
        exceptionalBound * Fintype.card Query := by
  refine L.win_card_le.trans ?_
  have hallSum : (∑ challenge, L.allBudget challenge) ≤
      Fintype.card Challenge * allBound := by
    calc
      (∑ challenge, L.allBudget challenge) ≤ ∑ _challenge : Challenge, allBound :=
        Finset.sum_le_sum fun challenge _ => hall challenge
      _ = Fintype.card Challenge * allBound := by simp
  have hlinearSum : (∑ challenge, L.linearBudget challenge) ≤
      Fintype.card Challenge * linearBound := by
    calc
      (∑ challenge, L.linearBudget challenge) ≤
          ∑ _challenge : Challenge, linearBound :=
        Finset.sum_le_sum fun challenge _ => hlinear challenge
      _ = Fintype.card Challenge * linearBound := by simp
  calc
    (∑ challenge, L.allBudget challenge) +
        (∑ challenge, L.linearBudget challenge) +
        L.exceptional.card * Fintype.card Query
      ≤ Fintype.card Challenge * allBound +
          Fintype.card Challenge * linearBound +
          exceptionalBound * Fintype.card Query := by
        exact Nat.add_le_add (Nat.add_le_add hallSum hlinearSum)
          (Nat.mul_le_mul_right _ hexceptional)
    _ = Fintype.card Challenge * (allBound + linearBound) +
          exceptionalBound * Fintype.card Query := by
        rw [Nat.mul_add]

end FlatEventLedger

end LigeroFamily
