import polygero.Recursion.FSRootQuery

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.FiatShamir.MerkleFS.Capacity
open Finset ProfileAnalysis Bcs.AffineBlock Bcs.TotalOracle Bcs.TotalOracle.Footprint
open Bcs.StoppedPotential
open TwoLevel
open scoped Classical
variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [DecidableEq D]
variable {I : Instance F} (child : Child I) (ctx : Context child (D := D))
variable (cp : HahnSystemCertificate child.instance)
variable (hazard : I.layer.Statement → I.layer.Oracle → I.layer.Coin → ℚ)
variable (hnonneg : ∀ σ W a, 0 ≤ hazard σ W a)
variable (hlocal : ∀ σ W V a, mean (fun q => indicator (queryCapacityRisk child cp σ W V a q)) ≤ hazard σ W a)

noncomputable def pointWeight (σ : I.layer.Statement) (rho : ℚ) :
    Point child (D := D) → (Point child (D := D) → Answer child) → Answer child → ℚ
  | .inl a,H,c => repeatPrice rho (hazard σ (ctx.parent a H) c.1.1)
  | .inr (.inl (a,b)),H,c =>
      (1-repeatPrice rho (hazard σ (ctx.parent a H) (H (gamma a)).1.1)) *
        indicator (queryCapacityRisk child cp σ (ctx.parent a H) (ctx.descendant (a,b) H)
          (H (gamma a)).1.1 c.1.2)
  | _,_,_ => 0

variable (σ : I.layer.Statement) (rho : ℚ) (hr : 0 ≤ rho)
variable (hroot : ∀ W, mean (fun a => repeatPrice rho (hazard σ W a)) ≤ rho)
variable (hfresh : ∀ W, mean (hazard σ W) ≤ rho)

theorem pointWeight_off (x : Point child (D := D)) (H H' : Point child (D := D) → Answer child)
    (ho : AgreeOff x H H') (c : Answer child) :
    pointWeight child ctx cp hazard σ rho x H c = pointWeight child ctx cp hazard σ rho x H' c := by
  rcases x with a | (⟨a,b⟩ | (z | z))
  · simp only [pointWeight,parent_off_point child ctx a (gamma a) rfl H H' ho]
  · have hw := parent_off_point child ctx a (query a b) rfl H H' ho
    have hv := descendant_off_point child ctx (a,b) (query a b) rfl H H' ho
    have ha := ho (gamma a) (by simp [gamma,query])
    simp only [pointWeight,hw,hv,ha]
  · rfl
  · rfl

include hr hnonneg in
theorem pointWeight_nonneg (x : Point child (D := D)) (H : Point child (D := D) → Answer child) (c : Answer child) :
    0 ≤ pointWeight child ctx cp hazard σ rho x H c := by
  rcases x with a | (⟨a,b⟩ | (z | z))
  · exact repeatPrice_nonneg _ _
  · exact mul_nonneg (sub_nonneg.mpr (Bcs.StoppedCharges.repeatPrice_le_one _ _ hr
      (hnonneg σ _ _))) (indicator_nonneg _)
  · rfl
  · rfl

include hr hnonneg hlocal hroot in
theorem pointWeight_mean (x : Point child (D := D)) (H : Point child (D := D) → Answer child) :
    average (pointWeight child ctx cp hazard σ rho x H) ≤ if x ∈ queryDomain child then rho else 0 := by
  rcases x with a | (⟨a,b⟩ | (z | z))
  · change mean (fun c : Answer child => repeatPrice rho
      (hazard σ (ctx.parent a H) c.1.1)) ≤ _
    simpa only [mean_prod,mean_const,queryDomain,mem_filter,mem_univ,true_and,role,
      show (0 : Fin 4) < 2 by decide,if_true] using hroot (ctx.parent a H)
  · have hq := hlocal σ (ctx.parent a H)
      (ctx.descendant (a,b) H) (H (gamma a)).1.1
    let c := hazard σ (ctx.parent a H) (H (gamma a)).1.1
    have hv : 0 ≤ 1-repeatPrice rho c := sub_nonneg.mpr
      (Bcs.StoppedCharges.repeatPrice_le_one _ _ hr (hnonneg σ _ _))
    have he : average (fun v : Answer child => indicator (queryCapacityRisk child cp σ
        (ctx.parent a H) (ctx.descendant (a,b) H) (H (gamma a)).1.1 v.1.2)) ≤ c := by
      change mean (fun v : Answer child => _) ≤ _
      simpa only [mean_prod,mean_const] using hq
    have hp := (repeat_child_step_iff c (repeatPrice rho c) rho).mp
      (repeatPrice_child_step c rho (hnonneg σ _ _) hr)
    change average (fun v : Answer child => (1-repeatPrice rho c)*_) ≤ _
    rw [average_mul]
    have hd : query (Q := I.layer.Query) (R := child.instance.layer.Payload) a b ∈ queryDomain child := by
      simp [queryDomain,query,role]
    have hd' : Sum.inr (Sum.inl (a,b)) ∈ queryDomain child := hd
    rw [if_pos hd']
    exact (mul_le_mul_of_nonneg_left he hv).trans (by nlinarith [hp])
  · change average (fun _ : Answer child => (0 : ℚ)) ≤ _
    simp [queryDomain,role]
  · change average (fun _ : Answer child => (0 : ℚ)) ≤ _
    simp [queryDomain,role]

/- The parent remains fixed across the pair. The child may vary with the
parent answer, but is fixed before its own query answer. -/
include hlocal hfresh in
theorem queryRisk_pair_mean (a b : D)
    (off : Outside ({gamma a,query a b} : Finset (Point child (D := D))) → Answer child) :
    average (fun on => indicator (queryRisk child ctx cp σ a b
      ((split {gamma a,query a b}).symm (on,off)))) ≤ rho := by
  let s : Finset (Point child (D := D)) := {gamma a,query a b}
  let ix : Inside s := ⟨gamma a,by simp [s]⟩
  let iy : Inside s := ⟨query a b,by simp [s]⟩
  have hxy : ix ≠ iy := by intro he; have := congrArg Subtype.val he; simp [ix,iy,gamma,query] at this
  let H (on : Inside s → Answer child) := (split s).symm (on,off)
  let base := H (fun _ => Classical.choice inferInstance)
  let W := ctx.parent a base
  have hW (on : Inside s → Answer child) : ctx.parent a (H on) = W := by
    apply parent_off_pair child ctx a b
    intro x hx
    exact (split_outside_eval s _ off x hx).trans (split_outside_eval s _ off x hx).symm
  rw [average_update iy]
  have hb (on : Inside s → Answer child) :
      average (fun c => indicator (queryRisk child ctx cp σ a b (H (Function.update on iy c)))) ≤
        hazard σ W (on ix).1.1 := by
    have hV (c : Answer child) : ctx.descendant (a,b) (H (Function.update on iy c)) =
        ctx.descendant (a,b) (H on) := by
      apply descendant_off_point child ctx (a,b) (query a b) rfl
      intro x hx
      by_cases hxs : x ∈ s
      · have hn : (⟨x,hxs⟩ : Inside s) ≠ iy := fun he => hx (congrArg Subtype.val he)
        simp [H,split_inside_eval,Function.update_of_ne hn,hxs]
      · exact (split_outside_eval s _ off x hxs).trans (split_outside_eval s _ off x hxs).symm
    have he (c : Answer child) : queryRisk child ctx cp σ a b (H (Function.update on iy c)) ↔
        queryCapacityRisk child cp σ W (ctx.descendant (a,b) (H on)) (on ix).1.1 c.1.2 := by
      simp only [queryRisk,hW,hV]
      rw [show H (Function.update on iy c) (gamma a) = on ix by
        exact (split_inside_eval s _ off _ ix.property).trans (Function.update_of_ne hxy _ _),
        show H (Function.update on iy c) (query a b) = c by
        exact (split_inside_eval s _ off _ iy.property).trans (Function.update_self _ _ _)]
    simp_rw [he]
    change mean (fun c : Answer child => _) ≤ _
    simpa only [mean_prod,mean_const] using hlocal σ W
      (ctx.descendant (a,b) (H on)) (on ix).1.1
  refine (average_mono hb).trans ?_
  refine (average_eval ix (fun c : Answer child => hazard σ W c.1.1)).trans_le ?_
  change mean (fun c : Answer child => _) ≤ _
  simpa only [mean_prod,mean_const] using hfresh W

/- Actual root-based parent/query ABS, retaining the joint intercept. -/
include hr hnonneg hlocal hroot hfresh in
theorem query_oracle_sound :
    OracleSound (queryDomain child) (fun d : Candidate child (D := D) => queryRisk child ctx cp σ d.1 d.2.1)
      (Rate.diagonal rho hr) := by
  apply oracle_sound_of_contextual_pair_completion (queryDomain child)
    (fun d : Candidate child (D := D) => gamma d.1) (fun d => query d.1 d.2.1)
    (fun d => by simp [gamma,query]) (pointWeight child ctx cp hazard σ rho)
    (pointWeight_off child ctx cp hazard σ rho) (pointWeight_nonneg child ctx cp hazard hnonneg σ rho hr)
    (Rate.diagonal rho hr) (le_refl _) ?_ _ ?_ ?_
  · intro x H
    have he := pointWeight_mean child ctx cp hazard hnonneg hlocal σ rho hr hroot x H
    have hc : (0 : ℚ) < Fintype.card (Answer child) := by exact_mod_cast Fintype.card_pos
    have h := (div_le_iff₀ hc).mp he
    simpa only [Rate.diagonal,average,mul_ite,mul_zero,mul_comm,zero_mul] using h
  · intro d off
    exact queryRisk_pair_mean child ctx cp hazard hlocal σ rho hfresh d.1 d.2.1 off
  · intro d H he
    change 1 ≤ repeatPrice rho _ + (1-repeatPrice rho _)*indicator _
    rw [show indicator (queryCapacityRisk child cp σ (ctx.parent d.1 H)
      (ctx.descendant (d.1,d.2.1) H) (H (gamma d.1)).1.1 (H (query d.1 d.2.1)).1.2) = 1 from if_pos he]
    ring_nf
    rfl

end RecursivePolygero.FiatShamir.MerkleFS.Capacity
