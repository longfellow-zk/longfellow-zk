import Bcs.AffineCharges
import Bcs.PotentialGrinding

namespace Bcs.TotalOracle
open Finset AffineBlock Footprint
open scoped Classical
variable {Q C : Type} [Fintype Q] [DecidableEq Q] [Fintype C]

theorem charged_rational_sum_le_expected
    (charged : Q → (Q → C) → Prop)
    (hchargedOff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      (charged q H ↔ charged q H'))
    (wt : Q → (Q → C) → C → ℚ)
    (hwtOff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      ∀ c, wt q H c = wt q H' c)
    (budget : Q → ℚ) (B : (Q → C) → ℚ)
    (hlocal : ∀ q H, ∑ c : C, wt q H c ≤ budget q)
    (htotal : ∀ H : Q → C,
      ∑ q ∈ (univ.filter fun q => charged q H), budget q ≤ B H) :
    (∑ H : Q → C, ∑ q : Q,
      if charged q H then wt q H (H q) else 0) * Fintype.card C ≤
      (∑ H : Q → C, B H) := by
  classical
  let W : Q → (Q → C) → C → ℚ :=
    fun q H c => if charged q H then wt q H c else 0
  have hWoff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      ∀ c, W q H c = W q H' c := by
    intro q H H' hoff c
    simp only [W]
    rw [propext (hchargedOff q H H' hoff)]
    split
    · exact hwtOff q H H' hoff c
    · rfl
  have hsum : (∑ H : Q → C, ∑ q : Q, W q H (H q)) * Fintype.card C =
      ∑ H : Q → C, ∑ q : Q, ∑ c : C, W q H c := by
    calc
      (∑ H : Q → C, ∑ q : Q, W q H (H q)) * Fintype.card C =
          ∑ q : Q, (∑ H : Q → C, W q H (H q)) * Fintype.card C := by
            rw [Finset.sum_comm, Finset.sum_mul]
      _ = ∑ q : Q, ∑ H : Q → C, ∑ c : C, W q H c := by
            apply Finset.sum_congr rfl
            intro q _
            exact sum_coord_mul_rat q (W q) (hWoff q)
      _ = _ := Finset.sum_comm
  change (∑ H : Q → C, ∑ q : Q, W q H (H q)) * Fintype.card C ≤ _
  rw [hsum]
  calc
    (∑ H : Q → C, ∑ q : Q, ∑ c : C, W q H c) ≤
        ∑ H : Q → C, B H := by
          apply Finset.sum_le_sum
          intro H _
          calc
            (∑ q : Q, ∑ c : C, W q H c) ≤
                ∑ q : Q, if charged q H then budget q else 0 := by
                  apply Finset.sum_le_sum
                  intro q _
                  by_cases hc : charged q H
                  · simpa only [W, hc, ↓reduceIte] using hlocal q H
                  · simp [W, hc]
            _ = ∑ q ∈ (univ.filter fun q : Q => charged q H), budget q := by
                  rw [Finset.sum_filter]
            _ ≤ B H := htotal H

theorem potential_event_ratio_le_expected [Nonempty C]
    (accepts : (Q → C) → Prop) [DecidablePred accepts]
    (charged : Q → (Q → C) → Prop)
    (hchargedOff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      (charged q H ↔ charged q H'))
    (wt : Q → (Q → C) → C → ℚ)
    (hwtOff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      ∀ c, wt q H c = wt q H' c)
    (budget : Q → ℚ) (B : (Q → C) → ℚ)
    (hlocal : ∀ q H, ∑ c : C, wt q H c ≤ budget q)
    (htotal : ∀ H : Q → C,
      ∑ q ∈ (univ.filter fun q => charged q H), budget q ≤ B H)
    (hwt_nonneg : ∀ q H c, 0 ≤ wt q H c)
    (haccept : ∀ H, accepts H →
      1 ≤ ∑ q : Q, if charged q H then wt q H (H q) else 0) :
    ((univ.filter accepts).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      average B / Fintype.card C := by
  classical
  have hpoint (H : Q → C) :
      (if accepts H then (1 : ℚ) else 0) ≤
        ∑ q : Q, if charged q H then wt q H (H q) else 0 := by
    by_cases ha : accepts H
    · simpa only [ha, ↓reduceIte] using haccept H ha
    · simp only [ha, ↓reduceIte]
      exact Finset.sum_nonneg fun q _ => by
        split
        · exact hwt_nonneg q H (H q)
        · exact le_rfl
  have hsum : ((univ.filter accepts).card : ℚ) ≤
      ∑ H : Q → C, ∑ q : Q,
        if charged q H then wt q H (H q) else 0 := by
    calc
      ((univ.filter accepts).card : ℚ) =
          ∑ H : Q → C, if accepts H then (1 : ℚ) else 0 := by
            rw [Finset.natCast_card_filter]
      _ ≤ _ := Finset.sum_le_sum fun H _ => hpoint H
  have hcharge := charged_rational_sum_le_expected charged hchargedOff wt hwtOff
    budget B hlocal htotal
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℚ) < (Fintype.card C : ℚ) ^ Fintype.card Q := pow_pos hC _
  rw [div_le_div_iff₀ hpow hC]
  have hmain := mul_le_mul_of_nonneg_right hsum (le_of_lt hC)
  have he : average B * (Fintype.card C : ℚ) ^ Fintype.card Q = ∑ H : Q → C, B H := by
    simp only [average, Fintype.card_fun, Nat.cast_pow]
    exact div_mul_cancel₀ _ hpow.ne'
  rw [he]
  nlinarith [hmain]

end Bcs.TotalOracle

namespace Bcs.TotalOracle.CtxGrinding
open Finset AffineBlock Footprint
open scoped Classical
variable {C Q Out Key K : Type} [Fintype C] [DecidableEq Q] {N L : ℕ}
variable (G : CtxGrinding C Q Out Key K N L)

theorem charged_rational_domain_budget_le [Fintype Q]
    (domain : Finset Q) (budget : Q → ℚ) (hbudget : ∀ x, 0 ≤ budget x)
    (betaMax : ℚ) (hbetaMax : 0 ≤ betaMax)
    (hmax : ∀ x : Q, budget x ≤ if x ∈ domain then betaMax else 0)
    (slotBeta : Fin L → ℚ)
    (hslot : ∀ out : Out, ∀ i : Fin L,
      budget (G.hashInput out i.val) ≤ slotBeta i)
    (H : Q → C) :
    ∑ x ∈ (univ.filter fun x => G.Charged x H), budget x ≤
      queryCost domain G.adversary H * betaMax + ∑ i, slotBeta i := by
  classical
  let A := (queried G.adversary H).toFinset
  let V := (univ : Finset (Fin L)).image fun i => G.point H i.val
  have hsub : (univ.filter fun x => G.Charged x H) ⊆ A ∪ V := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rcases hx with hq | ⟨k, hk⟩
    · exact mem_union_left _ (List.mem_toFinset.mpr hq)
    · exact mem_union_right _ (mem_image.mpr ⟨k, mem_univ _, hk⟩)
  have hAle : ∑ x ∈ A, budget x ≤ queryCost domain G.adversary H * betaMax := by
    calc
      _ ≤ ∑ x ∈ A, if x ∈ domain then betaMax else 0 :=
        sum_le_sum (fun x _ => hmax x)
      _ = ((A.filter (fun x => x ∈ domain)).card : ℚ) * betaMax := by
        rw [← sum_filter]; simp
      _ ≤ queryCost domain G.adversary H * betaMax :=
        mul_le_mul_of_nonneg_right (queried_domain_card_le domain G.adversary H) hbetaMax
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
    _ ≤ queryCost domain G.adversary H * betaMax + ∑ i, slotBeta i := add_le_add hAle hVle

/-- Rational-grading compiler at the actual commitment context.  In contrast
to the Boolean `Bad` interface, `charge` can split an accepting execution's
cost among many challenge and query answers by positive increase. -/
theorem potential_domain_ratio_le [Fintype Q] [Nonempty C]
    (charge : K → (x : Q) → (Fin (G.pts.slot x) → C) → C → ℚ)
    (hnonneg : ∀ κ x pref c, 0 ≤ charge κ x pref c)
    (domain : Finset Q) (budget : Q → ℚ) (hbudget : ∀ x, 0 ≤ budget x)
    (hlocal : ∀ κ x pref,
      ∑ c : C, charge κ x pref c ≤ budget x)
    (betaMax : ℚ) (hbetaMax : 0 ≤ betaMax)
    (hmax : ∀ x : Q, budget x ≤ if x ∈ domain then betaMax else 0)
    (slotBeta : Fin L → ℚ)
    (hslot : ∀ out : Out, ∀ i : Fin L,
      budget (G.hashInput out i.val) ≤ slotBeta i)
    (E : (Q → C) → Prop) [DecidablePred E]
    (haccept : ∀ H, E H →
      1 ≤ ∑ x : Q, if G.Charged x H then
        charge (G.ctxAt H (G.key x)) x (G.pts.chal H x) (H x) else 0) :
    ((univ.filter E).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (average (queryCost domain G.adversary) * betaMax + ∑ i, slotBeta i) / Fintype.card C := by
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
  have h := potential_event_ratio_le_expected E G.Charged hcharged wt hoff
    budget _ (fun x H => hlocal (G.ctxAt H (G.key x)) x (G.pts.chal H x))
    (G.charged_rational_domain_budget_le domain budget hbudget betaMax hbetaMax hmax slotBeta hslot)
    (fun x H c => hnonneg (G.ctxAt H (G.key x)) x (G.pts.chal H x) c)
    haccept
  have he : average (fun H => queryCost domain G.adversary H * betaMax + ∑ i, slotBeta i) =
      average (queryCost domain G.adversary) * betaMax + ∑ i, slotBeta i := by
    rw [average_add, average_const]
    simp only [average, ← sum_mul, div_mul_eq_mul_div]
  change _ ≤ average (fun H => queryCost domain G.adversary H * betaMax + ∑ i, slotBeta i) /
    Fintype.card C at h
  rw [he] at h
  exact h

end Bcs.TotalOracle.CtxGrinding

namespace Bcs.AffineBlock
open Finset TotalOracle TotalOracle.Footprint Merkle.RandomOracle
open scoped Classical

/-- A local charge compiler with an arbitrary injective verifier schedule.
Off-coordinate dependence is required of the charge, not of the schedule.
The latter may be selected by the complete adaptive prover. -/
theorem oracle_sound_of_charges
    {Q C Out : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    {L : ℕ} (domain : Finset Q) (point : Out → ℕ → Q)
    (hpoint : ∀ out, Function.Injective (fun i : Fin L => point out i.val))
    (weight : Q → (Q → C) → C → ℚ)
    (hoff : ∀ q H H', AgreeOff q H H' → ∀ c, weight q H c = weight q H' c)
    (hn : ∀ q H c, 0 ≤ weight q H c)
    (budget : Q → ℚ) (hb : ∀ q, 0 ≤ budget q)
    (hl : ∀ q H, ∑ c, weight q H c ≤ budget q)
    (rate : Rate) (slots : Fin L → ℚ)
    (hquery : ∀ q, budget q ≤ if q ∈ domain then Fintype.card C * rate.slope else 0)
    (hslots : ∀ out i, budget (point out i.val) ≤ slots i)
    (hsum : (∑ i, slots i) ≤ Fintype.card C * rate.intercept)
    (failure : Out → (Q → C) → Prop)
    (hpay : ∀ out H, failure out H →
      1 ≤ ∑ i : Fin L, weight (point out i.val) H (H (point out i.val))) :
    OracleSound domain failure rate := by
  intro N tree
  let G : CtxGrinding C Q Out Unit Unit N L := {
    adversary := tree
    hashInput := point
    pts := { slot := fun _ => 0, anc := fun q _ => q, anc_ne := by intros; omega }
    key := fun _ => ()
    ctxAt := fun _ _ => ()
    ctxAt_off := by intros; rfl
    Bad := fun _ _ _ _ => False
    beta := fun _ => 0
    bad_bound := by intros; simp }
  refine ⟨queryCost_nonneg domain tree, ?_⟩
  have hc : ∀ q H H', AgreeOff q H H' → (G.Charged q H ↔ G.Charged q H') :=
    fun q H H' h => ⟨G.charged_off h, G.charged_off h.symm⟩
  have hp (H : Q → C) (hf : failure (tree.run H).1 H) :
      1 ≤ ∑ q, if G.Charged q H then weight q H (H q) else 0 :=
    (hpay _ H hf).trans (G.verifier_charge_le_total hpoint _ (fun q => hn q H _) H)
  have h := potential_event_ratio_le_expected (fun H => failure (tree.run H).1 H)
    G.Charged hc weight hoff budget _ hl
    (G.charged_rational_domain_budget_le domain budget hb
      (Fintype.card C * rate.slope) (mul_nonneg (Nat.cast_nonneg _) rate.slope_nonneg)
      hquery slots hslots) hn hp
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hav : average (fun H => queryCost domain tree H * (Fintype.card C * rate.slope) + ∑ i, slots i) =
      average (queryCost domain tree) * (Fintype.card C * rate.slope) + ∑ i, slots i := by
    rw [average_add, average_const]
    simp only [average, ← sum_mul, div_mul_eq_mul_div]
  change _ ≤ average (fun H => queryCost domain tree H * (Fintype.card C * rate.slope) + ∑ i, slots i) /
    Fintype.card C at h
  rw [hav] at h
  simp only [FiniteProbability.density, Fintype.card_fun, Nat.cast_pow]
  apply h.trans
  apply (div_le_iff₀ hC).mpr
  nlinarith

end Bcs.AffineBlock

namespace Bcs.AffineBlock
open Finset TotalOracle Merkle.RandomOracle
open scoped Classical

/-- Embed a block's actual typed inputs in a shared oracle. Queries outside
its image have zero charge, while all coordinates remain available to the prover. -/
theorem oracle_sound_of_embedded_charges
    {P Q C Out : Type} [Fintype P] [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    {L : ℕ} (embed : P ↪ Q) (domain : Finset Q) (point : Out → ℕ → P)
    (hpoint : ∀ out, Function.Injective (fun i : Fin L => point out i.val))
    (weight : P → (Q → C) → C → ℚ)
    (hoff : ∀ p H H', AgreeOff (embed p) H H' → ∀ c, weight p H c = weight p H' c)
    (hn : ∀ p H c, 0 ≤ weight p H c)
    (budget : P → ℚ) (hb : ∀ p, 0 ≤ budget p)
    (hl : ∀ p H, ∑ c, weight p H c ≤ budget p)
    (rate : Rate) (slots : Fin L → ℚ)
    (hquery : ∀ p, budget p ≤ if embed p ∈ domain then Fintype.card C * rate.slope else 0)
    (hslots : ∀ out i, budget (point out i.val) ≤ slots i)
    (hsum : (∑ i, slots i) ≤ Fintype.card C * rate.intercept)
    (failure : Out → (Q → C) → Prop)
    (hpay : ∀ out H, failure out H →
      1 ≤ ∑ i : Fin L, weight (point out i.val) H (H (embed (point out i.val)))) :
    OracleSound domain failure rate := by
  let lift (f : P → ℚ) (q : Q) : ℚ := if h : ∃ p, embed p = q then f h.choose else 0
  have he (f : P → ℚ) (p : P) : lift f (embed p) = f p := by
    unfold lift
    split_ifs with h
    · rw [embed.injective h.choose_spec]
    · exact (h ⟨p, rfl⟩).elim
  refine oracle_sound_of_charges domain (fun out i => embed (point out i))
    (fun out => embed.injective.comp (hpoint out))
    (fun q H c => lift (fun p => weight p H c) q) ?_ ?_ (lift budget) ?_ ?_ rate slots ?_ ?_ hsum failure ?_
  · intro q H H' ho c
    dsimp only [lift]
    split_ifs with h
    · exact hoff h.choose H H' (by simpa only [h.choose_spec] using ho) c
    · rfl
  · intro q H c; dsimp only [lift]; split_ifs; exact hn _ _ _; exact le_rfl
  · intro q; dsimp only [lift]; split_ifs; exact hb _; exact le_rfl
  · intro q H; dsimp only [lift]; split_ifs with h
    · exact hl _ _
    · simp
  · intro q
    dsimp only [lift]
    by_cases h : ∃ p, embed p = q
    · rw [dif_pos h]
      simpa only [h.choose_spec] using hquery h.choose
    · rw [dif_neg h]
      split_ifs
      · exact mul_nonneg (Nat.cast_nonneg _) rate.slope_nonneg
      · exact le_rfl
  · intro out i; rw [he]; exact hslots out i
  · intro out H hf; simp_rw [he]; exact hpay out H hf

end Bcs.AffineBlock
