import LigeroFamily.Soundness.PotentialProfile
import LigeroFamily.Soundness.FiniteCounting

/-!
# Pairwise extraction from a graded challenge potential

The same potential pays for both fresh verifier answers.  Its expectation
after the combination challenge pays the challenge charge; only the remaining
`1 - ψ` fraction of an accepted query is charged at the query answer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace LigeroFamily.PotentialProfile

open Finset
open scoped Classical

/-- The common finite averaging step. Both interactive signed drift and
Fiat–Shamir positive-increase accounting supply a pointwise bound of this
form, but obtain it from different local certificates. -/
theorem pair_ratio_le_of_pointwise
    {Challenge Query : Type*} [Fintype Challenge] [DecidableEq Challenge]
    [Nonempty Challenge] [Fintype Query] [DecidableEq Query] [Nonempty Query]
    (potential : Challenge → ℚ)
    (accepts : Challenge → Query → Prop) [DecidableRel accepts]
    (challengeCost queryCost : ℚ)
    (hchallenge : (∑ c : Challenge, potential c) /
      Fintype.card Challenge ≤ challengeCost)
    (hpoint : ∀ c : Challenge,
      ((univ.filter fun q : Query => accepts c q).card : ℚ) /
        Fintype.card Query ≤ potential c + queryCost) :
    ((univ.filter fun p : Challenge × Query => accepts p.1 p.2).card : ℚ) /
        (Fintype.card Challenge * Fintype.card Query) ≤
      challengeCost + queryCost := by
  let A (c : Challenge) : ℚ :=
    ((univ.filter fun q : Query => accepts c q).card : ℚ) / Fintype.card Query
  have hcount :
    (univ.filter fun p : Challenge × Query => accepts p.1 p.2).card =
      ∑ c : Challenge, (univ.filter fun q : Query => accepts c q).card :=
    Internal.card_filter_product_eq_sum accepts
  have hC : (0 : ℚ) < Fintype.card Challenge := by exact_mod_cast Fintype.card_pos
  calc
    ((univ.filter fun p : Challenge × Query => accepts p.1 p.2).card : ℚ) /
        (Fintype.card Challenge * Fintype.card Query) =
      (∑ c : Challenge, A c) / Fintype.card Challenge := by
        rw [hcount]
        push_cast
        simp only [A, div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        ring
    _ ≤ (∑ c : Challenge, (potential c + queryCost)) /
          Fintype.card Challenge := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hC)
            exact Finset.sum_le_sum fun c _ => hpoint c
    _ = (∑ c : Challenge, potential c) /
          Fintype.card Challenge + queryCost := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rw [div_eq_mul_inv, div_eq_mul_inv]
            have hcard : (Fintype.card Challenge : ℚ) ≠ 0 := ne_of_gt hC
            field_simp
    _ ≤ challengeCost + queryCost := add_le_add hchallenge le_rfl

/-- The interactive version charges signed drift at the query. In
particular, choosing the potential to equal the conditional acceptance
probability makes the terminal charge zero and recovers the flat average. -/
theorem pair_ratio_le_signed
    {Challenge Query : Type*} [Fintype Challenge] [DecidableEq Challenge]
    [Nonempty Challenge] [Fintype Query] [DecidableEq Query] [Nonempty Query]
    (potential : Challenge → ℚ)
    (accepts : Challenge → Query → Prop) [DecidableRel accepts]
    (challengeCost queryCost : ℚ)
    (hchallenge : (∑ c : Challenge, potential c) /
      Fintype.card Challenge ≤ challengeCost)
    (hquery : ∀ c : Challenge,
      (((univ.filter fun q : Query => accepts c q).card : ℚ) /
          Fintype.card Query) - potential c ≤ queryCost) :
    ((univ.filter fun p : Challenge × Query => accepts p.1 p.2).card : ℚ) /
        (Fintype.card Challenge * Fintype.card Query) ≤
      challengeCost + queryCost := by
  apply pair_ratio_le_of_pointwise potential accepts challengeCost queryCost hchallenge
  intro c
  have h := hquery c
  linarith

/-- A response-independent envelope for the final query gives the exact
flat interactive bound after averaging over the first challenge.  This is
the zero-query terminal rule; no maximum over challenge values is taken. -/
theorem pair_ratio_le_flat
    {Challenge Query : Type*} [Fintype Challenge] [DecidableEq Challenge]
    [Nonempty Challenge] [Fintype Query] [DecidableEq Query] [Nonempty Query]
    (accepts : Challenge → Query → Prop) [DecidableRel accepts]
    (envelope : Challenge → ℚ)
    (hcover : ∀ c : Challenge,
      ((univ.filter fun q : Query => accepts c q).card : ℚ) /
        Fintype.card Query ≤ envelope c) :
    ((univ.filter fun p : Challenge × Query => accepts p.1 p.2).card : ℚ) /
        (Fintype.card Challenge * Fintype.card Query) ≤
      (∑ c : Challenge, envelope c) / Fintype.card Challenge := by
  have h := pair_ratio_le_signed envelope accepts
    ((∑ c : Challenge, envelope c) / Fintype.card Challenge) 0 le_rfl
    (by
      intro c
      have hc := hcover c
      linarith)
  simpa using h

/-- An extraction-failure event over a challenge and a subsequent query.
There is no agreement cutoff: `challengeCost` can be the sum of every
agreement tail, while `queryCost` can be optimized independently. -/
theorem pair_ratio_le
    {Challenge Query : Type*} [Fintype Challenge] [DecidableEq Challenge]
    [Nonempty Challenge] [Fintype Query] [DecidableEq Query] [Nonempty Query]
    {n : ℕ} (ψ : Curve n) (agreement : Challenge → ℕ)
    (hagreement : ∀ c, agreement c ≤ n)
    (accepts : Challenge → Query → Prop) [DecidableRel accepts]
    (challengeCost queryCost : ℚ)
    (hchallenge : (∑ c : Challenge, ψ.value (agreement c)) /
      Fintype.card Challenge ≤ challengeCost)
    (hquery : ∀ c : Challenge,
      (1 - ψ.value (agreement c)) *
        (((univ.filter fun q : Query => accepts c q).card : ℚ) /
          Fintype.card Query) ≤ queryCost) :
    ((univ.filter fun p : Challenge × Query => accepts p.1 p.2).card : ℚ) /
        (Fintype.card Challenge * Fintype.card Query) ≤
      challengeCost + queryCost := by
  classical
  let A (c : Challenge) : ℚ :=
    ((univ.filter fun q : Query => accepts c q).card : ℚ) / Fintype.card Query
  have hA (c : Challenge) : 0 ≤ A c ∧ A c ≤ 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · unfold A
      have hcard := Finset.card_le_card (Finset.filter_subset
        (s := (univ : Finset Query)) (fun q => accepts c q))
      have hcast : ((univ.filter fun q : Query => accepts c q).card : ℚ) ≤
          Fintype.card Query := by exact_mod_cast hcard
      exact (div_le_one (by exact_mod_cast Fintype.card_pos)).mpr hcast
  have hpoint (c : Challenge) : A c ≤ ψ.value (agreement c) + queryCost := by
    have hψ : 0 ≤ ψ.value (agreement c) := ψ.nonneg _ (hagreement c)
    have hmul : ψ.value (agreement c) * A c ≤ ψ.value (agreement c) :=
      mul_le_of_le_one_right hψ (hA c).2
    have hq := hquery c
    dsimp [A]
    nlinarith
  exact pair_ratio_le_of_pointwise (fun c => ψ.value (agreement c)) accepts
    challengeCost queryCost
    hchallenge hpoint

end LigeroFamily.PotentialProfile
