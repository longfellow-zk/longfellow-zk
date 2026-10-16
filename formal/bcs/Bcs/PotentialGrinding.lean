import Bcs.PotentialOracle

/-!
# Graded positive-increase charging at prefix-only hash points

This is the rational analogue of `CtxGrinding.ratio_le`.  The prover may
inspect hash points out of transcript order.  The charge at a point uses
only the commitment context and earlier transcript answers, both fixed when
that point's answer is held out.  The event-specific telescope from a
maximum-over-prefixes potential is supplied as `haccept`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle.CtxGrinding

open Finset
open scoped Classical

variable {C Q Out Key K : Type} [Fintype C] [DecidableEq Q] {N L : ℕ}
variable (G : CtxGrinding C Q Out Key K N L)

/-- On an injective verifier schedule, every verifier charge is represented
once in the charged-point sum.  This is needed when a potential telescope
splits its unit across a combination challenge and its following query. -/
theorem verifier_charge_le_total [Fintype Q]
    (hinputs : ∀ out, Function.Injective
      (fun i : Fin L => G.hashInput out i.val))
    (f : Q → ℚ) (hnonneg : ∀ x, 0 ≤ f x) (H : Q → C) :
    ∑ i : Fin L, f (G.point H i.val) ≤
      ∑ x : Q, if G.Charged x H then f x else 0 := by
  classical
  let v : Fin L → Q := fun i => G.point H i.val
  have hv : Function.Injective v := hinputs (G.proof H)
  have hsub : (univ : Finset (Fin L)).image v ⊆
      (univ : Finset Q).filter (fun x => G.Charged x H) := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨i, rfl⟩⟩
  calc
    ∑ i : Fin L, f (G.point H i.val) =
        ∑ x ∈ (univ : Finset (Fin L)).image v, f x := by
          rw [Finset.sum_image (by intro i _ j _ hij; exact hv hij)]
    _ ≤ ∑ x ∈ (univ : Finset Q).filter (fun x => G.Charged x H), f x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hnonneg x)
    _ = ∑ x : Q, if G.Charged x H then f x else 0 := by
      rw [Finset.sum_filter]

/-- Exact role-dependent cost of the points seen by a prefix-only prover.
The `N` term counts queried hash points, and each verifier slot contributes
its own cost.  No integer ceiling is taken. -/
theorem charged_rational_budget_le [Fintype Q]
    (budget : Q → ℚ) (hbudget : ∀ x, 0 ≤ budget x)
    (betaMax : ℚ) (hbetaMax : 0 ≤ betaMax)
    (hmax : ∀ x : Q, budget x ≤ betaMax)
    (slotBeta : Fin L → ℚ)
    (hslot : ∀ out : Out, ∀ i : Fin L,
      budget (G.hashInput out i.val) ≤ slotBeta i)
    (H : Q → C) :
    ∑ x ∈ (univ.filter fun x => G.Charged x H), budget x ≤
      N * betaMax + ∑ i, slotBeta i := by
  classical
  let A := (queried G.adversary H).toFinset
  let V := (univ : Finset (Fin L)).image fun i => G.point H i.val
  have hsub : (univ.filter fun x => G.Charged x H) ⊆ A ∪ V := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rcases hx with hq | ⟨k, hk⟩
    · exact mem_union_left _ (List.mem_toFinset.mpr hq)
    · exact mem_union_right _ (mem_image.mpr ⟨k, mem_univ _, hk⟩)
  have hAle : ∑ x ∈ A, budget x ≤ N * betaMax := by
    refine le_trans (Finset.sum_le_card_nsmul A budget betaMax fun x _ => hmax x) ?_
    rw [nsmul_eq_mul]
    have hc : A.card ≤ N :=
      (List.toFinset_card_le _).trans (queried_length_le G.adversary H)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hbetaMax
  have hVle : ∑ x ∈ V, budget x ≤ ∑ i, slotBeta i :=
    le_trans (Finset.sum_image_le_of_nonneg fun x _ => hbudget x)
      (Finset.sum_le_sum fun i _ => hslot _ i)
  have hunion := Finset.sum_union_inter (s₁ := A) (s₂ := V) (f := budget)
  calc
    ∑ x ∈ (univ.filter fun x => G.Charged x H), budget x ≤
        ∑ x ∈ A ∪ V, budget x :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hbudget x)
    _ ≤ ∑ x ∈ A, budget x + ∑ x ∈ V, budget x := by
          have hi : 0 ≤ ∑ x ∈ A ∩ V, budget x :=
            Finset.sum_nonneg fun x _ => hbudget x
          linarith
    _ ≤ N * betaMax + ∑ i, slotBeta i := add_le_add hAle hVle

/-- Rational-grading compiler at the actual commitment context.  In contrast
to the Boolean `Bad` interface, `charge` can split an accepting execution's
cost among many challenge and query answers by positive increase. -/
theorem potential_ratio_le_rat [Fintype Q] [Nonempty C]
    (charge : K → (x : Q) → (Fin (G.pts.slot x) → C) → C → ℚ)
    (hnonneg : ∀ κ x pref c, 0 ≤ charge κ x pref c)
    (budget : Q → ℚ) (hbudget : ∀ x, 0 ≤ budget x)
    (hlocal : ∀ κ x pref,
      ∑ c : C, charge κ x pref c ≤ budget x)
    (betaMax : ℚ) (hbetaMax : 0 ≤ betaMax)
    (hmax : ∀ x : Q, budget x ≤ betaMax)
    (slotBeta : Fin L → ℚ)
    (hslot : ∀ out : Out, ∀ i : Fin L,
      budget (G.hashInput out i.val) ≤ slotBeta i)
    (E : (Q → C) → Prop) [DecidablePred E]
    (haccept : ∀ H, E H →
      1 ≤ ∑ x : Q, if G.Charged x H then
        charge (G.ctxAt H (G.key x)) x (G.pts.chal H x) (H x) else 0) :
    ((univ.filter E).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (N * betaMax + ∑ i, slotBeta i) / Fintype.card C := by
  classical
  let wt (x : Q) (H : Q → C) (c : C) : ℚ :=
    charge (G.ctxAt H (G.key x)) x (G.pts.chal H x) c
  have hoff : ∀ x (H H' : Q → C), AgreeOff x H H' →
      ∀ c, wt x H c = wt x H' c := by
    intro x H H' h c
    simp only [wt]
    rw [G.ctxAt_off H H' x h, ← G.pts.chal_congr h]
  have hcharged : ∀ x (H H' : Q → C), AgreeOff x H H' →
      (G.Charged x H ↔ G.Charged x H') := by
    intro x H H' h
    exact ⟨G.charged_off h, G.charged_off h.symm⟩
  exact potential_event_ratio_le_budget E G.Charged hcharged wt hoff
    budget _ (fun x H => hlocal (G.ctxAt H (G.key x)) x (G.pts.chal H x))
    (G.charged_rational_budget_le budget hbudget betaMax hbetaMax hmax slotBeta hslot)
    (fun x H c => hnonneg (G.ctxAt H (G.key x)) x (G.pts.chal H x) c)
    haccept

/-- Same `N` query factor and verifier-slot budgets as the Boolean compiler,
but with exact rational positive-increase weights.  The proof does not
identify a particular escape slot; it accepts an event-wise potential
telescope, allowing the entire graded challenge/query curve to be used. -/
theorem potential_ratio_le [Fintype Q] [Nonempty C]
    (charge : K → (x : Q) → (Fin (G.pts.slot x) → C) → C → ℚ)
    (hnonneg : ∀ κ x pref c, 0 ≤ charge κ x pref c)
    (hlocal : ∀ κ x pref,
      ∑ c : C, charge κ x pref c ≤ G.beta x)
    (betaMax : ℕ) (hmax : ∀ x : Q, G.beta x ≤ betaMax)
    (slotBeta : Fin L → ℕ)
    (hslot : ∀ out : Out, ∀ i : Fin L,
      G.beta (G.hashInput out i.val) ≤ slotBeta i)
    (E : (Q → C) → Prop) [DecidablePred E]
    (haccept : ∀ H, E H →
      1 ≤ ∑ x : Q, if G.Charged x H then
        charge (G.ctxAt H (G.key x)) x (G.pts.chal H x) (H x) else 0) :
    ((univ.filter E).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      ((N * betaMax + ∑ i, slotBeta i : ℕ) : ℚ) / Fintype.card C := by
  classical
  let wt (x : Q) (H : Q → C) (c : C) : ℚ :=
    charge (G.ctxAt H (G.key x)) x (G.pts.chal H x) c
  have hoff : ∀ x (H H' : Q → C), AgreeOff x H H' →
      ∀ c, wt x H c = wt x H' c := by
    intro x H H' h c
    simp only [wt]
    rw [G.ctxAt_off H H' x h, ← G.pts.chal_congr h]
  have hcharged : ∀ x (H H' : Q → C), AgreeOff x H H' →
      (G.Charged x H ↔ G.Charged x H') := by
    intro x H H' h
    exact ⟨G.charged_off h, G.charged_off h.symm⟩
  have htotal : ∀ H : Q → C,
      ∑ x ∈ (univ.filter fun x => G.Charged x H), (G.beta x : ℚ) ≤
        (N * betaMax + ∑ i, slotBeta i : ℕ) := by
    intro H
    have hs : ∑ x ∈ (univ.filter fun x => G.Charged x H), G.beta x =
        ∑ x : Q, G.weight x H := by
      rw [Finset.sum_filter]
      rfl
    have hn : ∑ x ∈ (univ.filter fun x => G.Charged x H), G.beta x ≤
        N * betaMax + ∑ i, slotBeta i := by
      rw [hs]
      exact G.total_weight_le betaMax hmax slotBeta hslot H
    exact_mod_cast hn
  exact potential_event_ratio_le_budget E G.Charged hcharged wt hoff
    (fun x => (G.beta x : ℚ)) _
    (fun x H => hlocal (G.ctxAt H (G.key x)) x (G.pts.chal H x))
    htotal (fun x H c => hnonneg (G.ctxAt H (G.key x)) x (G.pts.chal H x) c)
    haccept

end Bcs.TotalOracle.CtxGrinding
