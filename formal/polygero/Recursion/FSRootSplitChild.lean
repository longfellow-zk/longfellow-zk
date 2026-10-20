import polygero.Recursion.FSRootTerminal
import polygero.Local.SplitChildPrice
import Bcs.ContextualFootprints

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.FiatShamir.MerkleFS.SplitChild
open Finset Counting ProfileAnalysis Local Bcs.AffineBlock Bcs.TotalOracle Bcs.TotalOracle.Footprint
open Bcs.TerminalCharges TwoLevel
open scoped Classical
variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [DecidableEq D]
variable {I : Instance F} (child : Child I) (ctx : Context child (D := D))
variable (cp : HahnSystemCertificate child.instance)

noncomputable def rigidWeight (σ : I.layer.Statement) (b : RootPrefix child (D := D))
    (H : Point child (D := D) → Answer child) : ℚ :=
  rigidChildBlockWeight child cp
    (child.link.statement σ (ctx.parent b.1 H) (H (gamma b.1)).1.1 b.2.2)
    (ctx.parent b.1 H,ctx.descendant (b.1,b.2.1) H,b.2.2) (liftOracle child b.1 b.2.1 H)

noncomputable def exceptionWeight (σ : I.layer.Statement) (b : RootPrefix child (D := D))
    (H : Point child (D := D) → Answer child) : ℚ :=
  indicator (nonrigidException child.instance cp
    (child.link.statement σ (ctx.parent b.1 H) (H (gamma b.1)).1.1 b.2.2)
    (ctx.descendant (b.1,b.2.1) H) (highSystems child.instance cp (ctx.descendant (b.1,b.2.1) H))
    (H (childGamma b.1 b.2.1 b.2.2)).2.1)

theorem blockWeight_eq (σ : I.layer.Statement) (b : RootPrefix child (D := D))
    (H : Point child (D := D) → Answer child) :
    blockWeight child ctx cp σ b H = rigidWeight child ctx cp σ b H+exceptionWeight child ctx cp σ b H := rfl

abbrev Index := (RootPrefix child (D := D) ⊕ RootPrefix child (D := D)) ⊕ Candidate child (D := D)

noncomputable def support : Index child (D := D) → Finset (Point child (D := D))
  | .inl (.inl b) => childBlock child b
  | .inl (.inr b) => {childGamma b.1 b.2.1 b.2.2}
  | .inr d => {terminal d}

noncomputable def weight (σ : I.layer.Statement) : Index child (D := D) → (Point child (D := D) → Answer child) → ℚ
  | .inl (.inl b) => rigidWeight child ctx cp σ b
  | .inl (.inr b) => exceptionWeight child ctx cp σ b
  | .inr d => baseWeight child ctx cp σ d

noncomputable def fullPrice : Index child (D := D) → (Point child (D := D) → Answer child) → ℚ
  | .inl (.inl b),H => rigidBudget child.instance cp (ctx.descendant (b.1,b.2.1) H)
  | .inl (.inr b),H => nonrigidBudget child.instance cp (ctx.descendant (b.1,b.2.1) H)
  | .inr _,_ => cp.threshold

theorem fullPrice_off (i : Index child (D := D)) (H H' : Point child (D := D) → Answer child)
    (ho : ∀ x, x ∉ support child i → H x = H' x) :
    fullPrice child ctx cp i H = fullPrice child ctx cp i H' := by
  rcases i with (b|b)|d
  · exact congrArg (rigidBudget child.instance cp) (descendant_off_block child ctx b H H' ho)
  · exact congrArg (nonrigidBudget child.instance cp)
      (descendant_off_point child ctx (b.1,b.2.1) (childGamma b.1 b.2.1 b.2.2) rfl H H'
        (by intro x hx; exact ho x (by simpa [support] using hx)))
  · rfl

noncomputable def budget (i : Index child (D := D))
    (off : Outside (support child i) → Answer child) : ℚ :=
  fullPrice child ctx cp i ((split (support child i)).symm (fun _ => Classical.choice inferInstance,off))

theorem budget_eq (i : Index child (D := D)) (H : Point child (D := D) → Answer child) :
    budget child ctx cp i (fun z => H z.1) = fullPrice child ctx cp i H := by
  apply fullPrice_off
  intro x hx
  exact split_outside_eval _ _ _ x hx

theorem weight_nonneg (σ : I.layer.Statement) (i : Index child (D := D)) (H : Point child (D := D) → Answer child) :
    0 ≤ weight child ctx cp σ i H := by
  rcases i with (b|b)|d
  · exact rigidChildBlockWeight_nonneg child cp _ _ _
  · exact indicator_nonneg _
  · exact baseWeight_nonneg child ctx cp σ d H

theorem budget_nonneg (i : Index child (D := D)) (off : Outside (support child i) → Answer child) :
    0 ≤ budget child ctx cp i off := by
  unfold budget
  rcases i with (b|b)|d
  · exact rigidBudget_nonneg _ _ _
  · exact nonrigidBudget_nonneg _ _ _
  · exact cp.threshold_nonneg

theorem rigid_local (σ : I.layer.Statement) (b : RootPrefix child (D := D))
    (off : Outside (childBlock child b) → Answer child) :
    average (fun on => rigidWeight child ctx cp σ b ((split (childBlock child b)).symm (on,off))) ≤
      budget child ctx cp (.inl (.inl b)) off := by
  let S := childBlock child b
  let H (on : Inside S → Answer child) := (split S).symm (on,off)
  let base := H (fun _ => Classical.choice inferInstance)
  let W := ctx.parent b.1 base
  let V := ctx.descendant (b.1,b.2.1) base
  let g : Outside S := ⟨gamma b.1,by simp [S,childBlock,blockKey,gamma]⟩
  let stmt := child.link.statement σ W (off g).1.1 b.2.2
  have hw (on) : ctx.parent b.1 (H on) = W := by
    apply parent_off_block child ctx b
    intro x hx
    exact (split_outside_eval S _ off x hx).trans (split_outside_eval S _ off x hx).symm
  have hv (on) : ctx.descendant (b.1,b.2.1) (H on) = V := by
    apply descendant_off_block child ctx b
    intro x hx
    exact (split_outside_eval S _ off x hx).trans (split_outside_eval S _ off x hx).symm
  have he (on) : rigidWeight child ctx cp σ b (H on) =
      rigidChildBlockWeight child cp stmt (W,V,b.2.2) (liftOracle child b.1 b.2.1 (H on)) := by
    simp only [rigidWeight,hw,hv]
    rw [show H on (gamma b.1) = off g from split_outside_eval S _ off _ g.property]
  change average (fun on => rigidWeight child ctx cp σ b (H on)) ≤ rigidBudget child.instance cp V
  simp_rw [he]
  rw [rigidPart_local]
  exact rigid_response_excess_mean_le child.instance cp stmt V

theorem exception_local (σ : I.layer.Statement) (b : RootPrefix child (D := D))
    (off : Outside ({childGamma b.1 b.2.1 b.2.2} : Finset (Point child (D := D))) → Answer child) :
    average (fun on => exceptionWeight child ctx cp σ b
      ((split {childGamma b.1 b.2.1 b.2.2}).symm (on,off))) ≤
      budget child ctx cp (.inl (.inr b)) off := by
  let S : Finset (Point child (D := D)) := {childGamma b.1 b.2.1 b.2.2}
  let H (on : Inside S → Answer child) := (split S).symm (on,off)
  let base := H (fun _ => Classical.choice inferInstance)
  let W := ctx.parent b.1 base
  let V := ctx.descendant (b.1,b.2.1) base
  let g : Outside S := ⟨gamma b.1,by simp [S,gamma,childGamma]⟩
  let c : Inside S := ⟨childGamma b.1 b.2.1 b.2.2,by simp [S]⟩
  let stmt := child.link.statement σ W (off g).1.1 b.2.2
  have ho (on) (x : Point child (D := D)) (hx : x ≠ c.1) : H on x = base x := by
    exact (split_outside_eval S _ off x (by simpa [S,c] using hx)).trans
      (split_outside_eval S _ off x (by simpa [S,c] using hx)).symm
  have hw (on) : ctx.parent b.1 (H on) = W :=
    parent_off_point child ctx b.1 c.1 rfl _ _ (ho on)
  have hv (on) : ctx.descendant (b.1,b.2.1) (H on) = V :=
    descendant_off_point child ctx (b.1,b.2.1) c.1 rfl _ _ (ho on)
  have he (on) : exceptionWeight child ctx cp σ b (H on) =
      indicator (nonrigidException child.instance cp stmt V (highSystems child.instance cp V) (on c).2.1) := by
    simp only [exceptionWeight,hw,hv]
    rw [show H on (gamma b.1) = off g from split_outside_eval S _ off _ g.property,
      show H on (childGamma b.1 b.2.1 b.2.2) = on c from split_inside_eval S _ off _ c.property]
    rw [hv on]
  change average (fun on => exceptionWeight child ctx cp σ b (H on)) ≤ nonrigidBudget child.instance cp V
  simp_rw [he]
  rw [average_eval c (fun a : Answer child => indicator
    (nonrigidException child.instance cp stmt V (highSystems child.instance cp V) a.2.1))]
  change mean (fun a : Answer child => _) ≤ _
  simp only [mean_prod,mean_const]
  exact nonrigidException_mean_le child.instance cp stmt V _

theorem local_mean (σ : I.layer.Statement) (i : Index child (D := D))
    (off : Outside (support child i) → Answer child) :
    average (fun on => weight child ctx cp σ i ((split (support child i)).symm (on,off))) ≤
      budget child ctx cp i off := by
  rcases i with (b|b)|d
  · exact rigid_local child ctx cp σ b off
  · exact exception_local child ctx cp σ b off
  · exact baseWeight_local child ctx cp σ d off

/-- Both verifier lookups are real and remain in the intercept. The
exception footprint is a singleton, so terminal grinding does not pay it
again at every terminal response key. -/
def replay (d : Candidate child (D := D)) : Merkle.RandomOracle.Tree (Point child (D := D)) (Answer child) Unit 2 :=
  .query (childGamma d.1 d.2.1 d.2.2.1) (fun _ => .query (terminal d) (fun _ => .done ()))

theorem query_load (H : Point child (D := D) → Answer child) (x : Point child (D := D)) :
    (∑ i : Index child (D := D), if x ∈ support child i then fullPrice child ctx cp i H else 0) =
    match x with
    | .inl _ => 0
    | .inr (.inl _) => 0
    | .inr (.inr (.inl b)) => rigidBudget child.instance cp (ctx.descendant (b.1,b.2.1) H)+
        nonrigidBudget child.instance cp (ctx.descendant (b.1,b.2.1) H)
    | .inr (.inr (.inr d)) => rigidBudget child.instance cp (ctx.descendant (d.1,d.2.1) H)+cp.threshold := by
  rcases x with a | (ab | (b | d)) <;>
    simp [Fintype.sum_sum_type,support,fullPrice,childBlock,blockKey,childGamma,terminal,childPrefix]

theorem replay_load (H : Point child (D := D) → Answer child) (d : Candidate child (D := D)) :
    (∑ i : Index child (D := D), if hits (replay child d) H (support child i) then fullPrice child ctx cp i H else 0) =
      rigidBudget child.instance cp (ctx.descendant (d.1,d.2.1) H)+
        nonrigidBudget child.instance cp (ctx.descendant (d.1,d.2.1) H)+cp.threshold := by
  simp [Fintype.sum_sum_type,replay,hits,support,fullPrice,childBlock,blockKey,childGamma,terminal,childPrefix]

theorem oracle_sound (p : HahnSystemCertificate I) (σ : I.layer.Statement)
    (C : ℚ) (hC : 0 ≤ C) (hsmall : cp.listBound < Nat.card F)
    (hcapacity : ∀ V, rigidExcessMass child.instance cp V+nonrigidMass child.instance cp V ≤ C)
    (hbase : cp.threshold+(1-cp.threshold)/(Nat.card F : ℚ) ≤ C/Nat.card F) :
    OracleSound (terminalDomain child)
      (fun d H => failure child ctx p cp σ d H ∧ ¬ queryRisk child ctx cp σ d.1 d.2.1 H)
      ⟨splitChildSlope child.instance cp C+cp.threshold,splitChildSlope child.instance cp C,
        add_nonneg (splitChildSlope_nonneg child.instance cp C hC) cp.threshold_nonneg,
        splitChildSlope_nonneg child.instance cp C hC⟩ := by
  apply oracle_sound_of_contextual_footprints (terminalDomain child) (replay child)
    (support child) (weight child ctx cp σ) (budget child ctx cp) _
    (weight_nonneg child ctx cp σ) (budget_nonneg child ctx cp) (local_mean child ctx cp σ)
  · intro H x
    simp_rw [budget_eq]
    rw [query_load]
    rcases x with a | (ab | (b | d))
    · simp [terminalDomain,role]
    · simp [terminalDomain,role]
    · simpa [terminalDomain,role] using split_budget_joint_le child.instance cp
        (ctx.descendant (b.1,b.2.1) H) C (hcapacity _)
    · simpa [terminalDomain,role] using split_budget_terminal_le child.instance cp
        (ctx.descendant (d.1,d.2.1) H) C hsmall hbase
  · intro H d H'
    simp_rw [budget_eq]
    have he : (fun i : Index child (D := D) => hits (replay child d) H' (support child i)) =
        (fun i => hits (replay child d) H (support child i)) := by funext i; rfl
    simp_rw [congrFun he]
    rw [replay_load]
    have h := split_budget_joint_le child.instance cp
      (ctx.descendant (d.1,d.2.1) H) C (hcapacity _)
    linarith
  · intro d H he
    have hp := wholeChildBlock_pay child cp p σ (extractedCandidate child (D := D) ctx d H)
      (liftOracle child d.1 d.2.1 H) he.1 he.2
    change 1 ≤ blockWeight child ctx cp σ (childPrefix child d) H+baseWeight child ctx cp σ d H at hp
    rw [blockWeight_eq] at hp
    refine hp.trans ?_
    have hr : rigidWeight child ctx cp σ (childPrefix child d) H ≤
        ∑ b : RootPrefix child (D := D), if hits (replay child d) H (childBlock child b) then rigidWeight child ctx cp σ b H else 0 := by
      simp [replay,hits,childPrefix,childBlock,blockKey,childGamma,terminal]
    have hexc : exceptionWeight child ctx cp σ (childPrefix child d) H ≤
        ∑ b : RootPrefix child (D := D), if hits (replay child d) H {childGamma b.1 b.2.1 b.2.2}
          then exceptionWeight child ctx cp σ b H else 0 := by
      simpa [replay,hits,childPrefix] using
        single_le_sum (f := fun b : RootPrefix child (D := D) => if hits (replay child d) H {childGamma b.1 b.2.1 b.2.2}
          then exceptionWeight child ctx cp σ b H else 0)
          (fun b _ => by split_ifs; exact indicator_nonneg _; rfl) (mem_univ (childPrefix child d))
    have hb : baseWeight child ctx cp σ d H ≤ ∑ e : Candidate child (D := D),
        if hits (replay child d) H {terminal e} then baseWeight child ctx cp σ e H else 0 := by
      simpa [replay,hits] using
        single_le_sum (f := fun e : Candidate child (D := D) => if hits (replay child d) H {terminal e}
          then baseWeight child ctx cp σ e H else 0)
          (fun e _ => by split_ifs; exact baseWeight_nonneg child ctx cp σ e H; rfl) (mem_univ d)
    simpa only [Fintype.sum_sum_type,support,weight] using add_le_add (add_le_add hr hexc) hb

end RecursivePolygero.FiatShamir.MerkleFS.SplitChild
