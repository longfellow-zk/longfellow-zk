import LigeroFamily.Soundness.AgreementProfile
import Bcs.TotalOracle

/-!
# Grading after a bounded search for the combination challenge

If a prover sees `tries` independent combination challenges and selects one
before the column-query challenge is drawn, the probability that the selected
challenge has agreement at least `a` is bounded by `tries` times the original
tail, capped at one.  The existing agreement-profile integral can therefore
be reused with an amplified tail at *every* agreement level.

This is a two-stage result.  It does not account for column-query points
queried before the combination challenge is selected; the full adaptive
Fiat–Shamir compiler needs an additional argument for those points.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LigeroFamily.AgreementProfile

open Finset
open scoped Classical

def amplified {n : ℕ} (profile : AgreementProfile n) (tries : ℕ) :
    AgreementProfile n where
  labelsAtLeast a := tries * profile.labelsAtLeast a

theorem selected_average_coverRatio_le_amplified
    {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (tries q n e g queryCount : ℕ) (htries : 0 < tries) (hq : 0 < q)
    (profile : AgreementProfile n) (agreement : X → ℕ)
    (hagreement : ∀ x, agreement x ≤ n)
    (hdensity : ∀ a ≤ n,
      q * (tailSet agreement a).card ≤
        profile.labelsAtLeast a * Fintype.card X)
    (selected : (Fin tries → X) → X)
    (hselected : ∀ draws, ∃ i : Fin tries, selected draws = draws i) :
    (∑ draws : Fin tries → X,
        coverRatio n e g queryCount (agreement (selected draws))) /
        Fintype.card (Fin tries → X) ≤
      (profile.amplified tries).contribution q n e g queryCount := by
  classical
  let cardX := Fintype.card X
  have hcardX : 0 < cardX := Fintype.card_pos
  have hpower : cardX ^ tries = cardX * cardX ^ (tries - 1) := by
    calc
      cardX ^ tries = cardX ^ ((tries - 1) + 1) := by congr 1; omega
      _ = cardX ^ (tries - 1) * cardX := pow_succ _ _
      _ = cardX * cardX ^ (tries - 1) := by ring
  have hdensityDraws (a : ℕ) (ha : a ≤ n) :
      q * (tailSet (fun draws : Fin tries → X => agreement (selected draws)) a).card ≤
        (profile.amplified tries).labelsAtLeast a *
          Fintype.card (Fin tries → X) := by
    let β := (tailSet agreement a).card
    let hit : Finset (Fin tries → X) :=
      univ.filter fun draws => ∃ i : Fin tries, a ≤ agreement (draws i)
    have hsub : tailSet (fun draws : Fin tries → X => agreement (selected draws)) a ⊆
        hit := by
      intro draws hd
      obtain ⟨i, hi⟩ := hselected draws
      exact mem_filter.mpr ⟨mem_univ _, ⟨i, by simpa [hi] using (mem_filter.mp hd).2⟩⟩
    have hhit : hit.card ≤ tries * β * cardX ^ (tries - 1) := by
      have hunion : hit = univ.biUnion fun i : Fin tries =>
          univ.filter fun draws : Fin tries → X => a ≤ agreement (draws i) := by
        ext draws
        simp [hit]
      rw [hunion]
      calc
        (univ.biUnion fun i : Fin tries =>
            univ.filter fun draws : Fin tries → X => a ≤ agreement (draws i)).card
            ≤ ∑ i : Fin tries,
                (univ.filter fun draws : Fin tries → X =>
                  a ≤ agreement (draws i)).card := card_biUnion_le
        _ ≤ ∑ _i : Fin tries, β * cardX ^ (tries - 1) := by
          apply Finset.sum_le_sum
          intro i _
          have hcoord := Bcs.TotalOracle.card_coord_le_const
            (ι := Fin tries) (C := X) i
            (fun (_ : Fin tries → X) (c : X) => a ≤ agreement c)
            (by intro H H' hoff c hc; exact hc)
            β (by
              intro H
              apply Finset.card_le_card
              intro c hc
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
              simp only [tailSet, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact hc)
          convert hcoord using 1
          · rfl
          · congr 1
            ext draws
            simp
          · change β * (Fintype.card X) ^ (tries - 1) =
              β * (Fintype.card X) ^ (Fintype.card (Fin tries) - 1)
            rw [Fintype.card_fin]
        _ = tries * β * cardX ^ (tries - 1) := by simp [β, cardX]; ring
    calc
      q * (tailSet (fun draws : Fin tries → X =>
          agreement (selected draws)) a).card ≤ q * hit.card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
      _ ≤ q * (tries * β * cardX ^ (tries - 1)) :=
        Nat.mul_le_mul_left _ hhit
      _ = tries * (q * β) * cardX ^ (tries - 1) := by ring
      _ ≤ tries * (profile.labelsAtLeast a * cardX) * cardX ^ (tries - 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hdensity a ha))
      _ = (profile.amplified tries).labelsAtLeast a *
          Fintype.card (Fin tries → X) := by
        simp only [amplified, Fintype.card_fun, Fintype.card_fin]
        rw [hpower]
        ring
  exact average_coverRatio_le_contribution q n e g queryCount
    (profile.amplified tries) (fun draws : Fin tries → X =>
      agreement (selected draws)) hq
    (fun draws => hagreement (selected draws)) hdensityDraws

/-- The two-stage acceptance statement: after seeing `tries` independent
combination challenges, the prover selects one and then receives one fresh,
independent column query.  Its bound integrates the amplified challenge tail
against the query-cover increments. -/
theorem selected_query_rate_le_amplified
    {X Query : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Query] [Nonempty Query]
    (tries q n e g queryCount : ℕ) (htries : 0 < tries) (hq : 0 < q)
    (profile : AgreementProfile n) (agreement : X → ℕ)
    (hagreement : ∀ x, agreement x ≤ n)
    (hdensity : ∀ a ≤ n,
      q * (tailSet agreement a).card ≤
        profile.labelsAtLeast a * Fintype.card X)
    (selected : (Fin tries → X) → X)
    (hselected : ∀ draws, ∃ i : Fin tries, selected draws = draws i)
    (good : X → Query → Prop)
    (hgood : ∀ x,
      ((univ.filter fun query : Query => good x query).card : ℚ) /
        Fintype.card Query ≤ coverRatio n e g queryCount (agreement x)) :
    ((univ.filter fun pair : (Fin tries → X) × Query =>
      good (selected pair.1) pair.2).card : ℚ) /
        (Fintype.card (Fin tries → X) * Fintype.card Query) ≤
      (profile.amplified tries).contribution q n e g queryCount := by
  classical
  have hcard := Bcs.card_filter_prod_fst
    (fun pair : (Fin tries → X) × Query => good (selected pair.1) pair.2)
  have hsum : (∑ draws : Fin tries → X,
      ((univ.filter fun query : Query => good (selected draws) query).card : ℚ) /
        Fintype.card Query) ≤
      ∑ draws : Fin tries → X,
        coverRatio n e g queryCount (agreement (selected draws)) :=
    Finset.sum_le_sum fun draws _ => hgood (selected draws)
  have hdraws : (0 : ℚ) < Fintype.card (Fin tries → X) := by
    exact_mod_cast Fintype.card_pos
  calc
    ((univ.filter fun pair : (Fin tries → X) × Query =>
        good (selected pair.1) pair.2).card : ℚ) /
        (Fintype.card (Fin tries → X) * Fintype.card Query) =
      (∑ draws : Fin tries → X,
        ((univ.filter fun query : Query => good (selected draws) query).card : ℚ) /
          Fintype.card Query) / Fintype.card (Fin tries → X) := by
      rw [hcard]
      push_cast
      have hsplit :
          (∑ draws : Fin tries → X,
              ((univ.filter fun query : Query => good (selected draws) query).card : ℚ) /
                Fintype.card Query) =
            (∑ draws : Fin tries → X,
              ((univ.filter fun query : Query => good (selected draws) query).card : ℚ)) /
                Fintype.card Query := by
        simp_rw [div_eq_mul_inv]
        rw [Finset.sum_mul]
      rw [hsplit]
      ring
    _ ≤ (∑ draws : Fin tries → X,
        coverRatio n e g queryCount (agreement (selected draws))) /
          Fintype.card (Fin tries → X) :=
      div_le_div_of_nonneg_right hsum (le_of_lt hdraws)
    _ ≤ (profile.amplified tries).contribution q n e g queryCount :=
      selected_average_coverRatio_le_amplified tries q n e g queryCount
        htries hq profile agreement hagreement hdensity selected hselected

end LigeroFamily.AgreementProfile
