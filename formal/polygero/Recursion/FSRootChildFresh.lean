import polygero.Recursion.FSRootSplitChild
import polygero.Local.ExcludedTargets

set_option maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.FiatShamir.MerkleFS.SplitChild
open Finset Counting ProfileAnalysis Local Bcs.AffineBlock Bcs.TotalOracle Bcs.TotalOracle.Footprint
open TwoLevel
open scoped Classical
variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [DecidableEq D]
variable {I : Instance F} (child : Child I) (ctx : Context child (D := D))
variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

/-- A selected child challenge and terminal lookup, both still unread,
retain the ordinary IOP error. Other terminal responses may already have
been queried: only these two coordinates are held out. -/
theorem fresh_pair_mean (σ : I.layer.Statement) (d : Candidate child (D := D))
    (off : Outside ({childGamma d.1 d.2.1 d.2.2.1,terminal d} : Finset (Point child (D := D))) → Answer child) :
    average (fun on => if failure child ctx p cp σ d
      ((split {childGamma d.1 d.2.1 d.2.2.1,terminal d}).symm (on,off)) ∧
      ¬ queryRisk child ctx cp σ d.1 d.2.1
        ((split {childGamma d.1 d.2.1 d.2.2.1,terminal d}).symm (on,off)) then (1 : ℚ) else 0) ≤ cp.error := by
  let S : Finset (Point child (D := D)) := {childGamma d.1 d.2.1 d.2.2.1,terminal d}
  let H (on : Inside S → Answer child) := (split S).symm (on,off)
  let base := H (fun _ => Classical.choice inferInstance)
  let W := ctx.parent d.1 base
  let V := ctx.descendant (d.1,d.2.1) base
  let g : Outside S := ⟨gamma d.1,by simp [S,gamma,childGamma,terminal]⟩
  let q : Outside S := ⟨query d.1 d.2.1,by simp [S,query,childGamma,terminal]⟩
  let x : Inside S := ⟨childGamma d.1 d.2.1 d.2.2.1,by simp [S]⟩
  let y : Inside S := ⟨terminal d,by simp [S]⟩
  let a := (off g).1.1
  let stmt := child.link.statement σ W a d.2.2.1
  let target := Protocol.ProfileProof.inducedFamily (child := child) σ W a (fun _ => False) d.2.2.1
  have hw (on) : ctx.parent d.1 (H on) = W := by
    apply ctx.parent_off
    intro z hz
    have hzs : z ∉ S := by
      simp only [S,mem_insert,mem_singleton,not_or]
      exact ⟨fun he => hz (he ▸ rfl),fun he => hz (he ▸ rfl)⟩
    exact (split_outside_eval S _ off z hzs).trans (split_outside_eval S _ off z hzs).symm
  have hv (on) : ctx.descendant (d.1,d.2.1) (H on) = V := by
    apply ctx.descendant_off
    intro z hz
    have hzs : z ∉ S := by
      simp only [S,mem_insert,mem_singleton,not_or]
      exact ⟨fun he => hz (he ▸ rfl),fun he => hz (he ▸ rfl)⟩
    exact (split_outside_eval S _ off z hzs).trans (split_outside_eval S _ off z hzs).symm
  have hg (on) : H on (gamma d.1) = off g := split_outside_eval S _ off _ g.property
  have hq (on) : H on (query d.1 d.2.1) = off q := split_outside_eval S _ off _ q.property
  have hx (on) : H on (childGamma d.1 d.2.1 d.2.2.1) = on x := split_inside_eval S _ off _ x.property
  have hy (on) : H on (terminal d) = on y := split_inside_eval S _ off _ y.property
  have hg' (on) : H on (Sum.inl d.1) = off g := hg on
  have hq' (on) : H on (Sum.inr (Sum.inl (d.1,d.2.1))) = off q := hq on
  have hx' (on) : H on (Sum.inr (Sum.inr (Sum.inl (d.1,d.2.1,d.2.2.1)))) = on x := hx on
  have hy' (on) : H on (Sum.inr (Sum.inr (Sum.inr d))) = on y := hy on
  change average (fun on : Inside S → Answer child => if failure child ctx p cp σ d (H on) ∧
    ¬ queryRisk child ctx cp σ d.1 d.2.1 (H on) then (1 : ℚ) else 0) ≤ cp.error
  by_cases heq : (off q).1.2 = d.2.2.1
  · by_cases hrisk : queryCapacityRisk child cp σ W V a d.2.2.1
    · have hn (on) : ¬ (failure child ctx p cp σ d (H on) ∧ ¬ queryRisk child ctx cp σ d.1 d.2.1 (H on)) := by
        rintro ⟨_,hn⟩
        apply hn
        simpa only [queryRisk,hw,hv,hg,hq,heq] using hrisk
      simp only [hn,if_false,average_const]
      exact cp.error_nonneg
    · have hp (on) : (if failure child ctx p cp σ d (H on) ∧ ¬ queryRisk child ctx cp σ d.1 d.2.1 (H on)
          then (1 : ℚ) else 0) ≤ indicator (child.instance.layer.verify stmt V (on x).2.1 d.2.2.2 (on y).2.2 ∧
            outputHit target (scanRecoverAt child.instance stmt V (on x).2.1 d.2.2.2)) := by
        have himp : (failure child ctx p cp σ d (H on) ∧ ¬ queryRisk child ctx cp σ d.1 d.2.1 (H on)) →
            (child.instance.layer.verify stmt V (on x).2.1 d.2.2.2 (on y).2.2 ∧
              outputHit target (scanRecoverAt child.instance stmt V (on x).2.1 d.2.2.2)) := by
          rintro ⟨hf,_⟩
          obtain ⟨hacc,hr⟩ := (failure_empty_iff child p cp σ _ _).mp hf
          obtain ⟨hqq,hd,hvfy⟩ := (accepts_iff child σ _ _).mp hacc
          have ht := child_target_of_failed_proof child cp p σ (ctx.parent d.1 (H on))
            (ctx.descendant (d.1,d.2.1) (H on)) ((H on (gamma d.1)).1.1) d.2.2.1
            ((H on (childGamma d.1 d.2.1 d.2.2.1)).2.1) d.2.2.2 ((H on (terminal d)).2.2) hd
            (by simpa only [proofCoins,extractedCandidate,liftOracle,TwoLevel.gamma,TwoLevel.query,
            TwoLevel.childGamma,TwoLevel.terminal,hq',heq] using hr)
          constructor
          · simpa only [liftOracle,extractedCandidate,TwoLevel.gamma,TwoLevel.childGamma,TwoLevel.terminal,hw,hv,hg',hx',hy'] using hvfy
          · simpa only [hw,hv,hg,hx,hy] using ht
        by_cases h : failure child ctx p cp σ d (H on) ∧ ¬ queryRisk child ctx cp σ d.1 d.2.1 (H on)
        · rw [if_pos h,indicator,if_pos (himp h)]
        · rw [if_neg h]; exact indicator_nonneg _
      refine (average_mono hp).trans ?_
      have hxy : y ≠ x := by intro h; have := congrArg Subtype.val h; simp [x,y,childGamma,terminal] at this
      rw [average_two_eval x y hxy (fun b t : Answer child => indicator
        (child.instance.layer.verify stmt V b.2.1 d.2.2.2 t.2.2 ∧
          outputHit target (scanRecoverAt child.instance stmt V b.2.1 d.2.2.2)))]
      change mean (fun b : Answer child => mean (fun t : Answer child => _)) ≤ _
      simp only [mean_prod,mean_const]
      apply excluded_target_response_mean_le child.instance cp stmt V target
      intro e he ht
      exact hrisk ⟨e,he,ht⟩
  · have hn (on) : ¬ (failure child ctx p cp σ d (H on) ∧ ¬ queryRisk child ctx cp σ d.1 d.2.1 (H on)) := by
      rintro ⟨hf,_⟩
      have hacc := ((failure_empty_iff child p cp σ _ _).mp hf).1
      have hqq := ((accepts_iff child σ _ _).mp hacc).1
      apply heq
      have hh : (H on (query d.1 d.2.1)).1.2 = d.2.2.1 := by
        simpa only [liftOracle,extractedCandidate,TwoLevel.query] using hqq
      exact (congrArg (fun c : Answer child => c.1.2) (hq on)).symm.trans hh
    simp only [hn,if_false,average_const]
    exact cp.error_nonneg

end RecursivePolygero.FiatShamir.MerkleFS.SplitChild
