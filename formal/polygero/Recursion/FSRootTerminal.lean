import polygero.Recursion.FSRootQuery

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.FiatShamir.MerkleFS
open Finset Counting ProfileAnalysis Local Bcs.AffineBlock Bcs.TotalOracle Bcs.TotalOracle.Footprint
open Bcs.TerminalCharges TwoLevel
open scoped Classical
variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [DecidableEq D]
variable {I : Instance F} (child : Child I)
abbrev RootPrefix (_child : Child I) := D × D × I.layer.Query
noncomputable def roleDomain (i : Fin 4) : Finset (Point child (D := D)) :=
  univ.filter (fun x => role child x = i)
@[simp] theorem mem_childBlock (b : RootPrefix child (D := D)) (x : Point child (D := D)) :
    x ∈ childBlock child b ↔ blockKey child x = some b := by simp [childBlock]
theorem terminal_mem_childBlock (d : Candidate child (D := D)) :
    terminal d ∈ childBlock child (childPrefix child d) := by simp [blockKey,terminal]
theorem childGamma_mem_childBlock (b : RootPrefix child (D := D)) :
    childGamma b.1 b.2.1 b.2.2 ∈ childBlock child b := by simp [blockKey,childGamma]
private theorem block_load (price : ℚ) (x : Point child (D := D)) :
    (∑ b : RootPrefix child (D := D), if x ∈ childBlock child b then price else 0) =
      if x ∈ terminalDomain child then price else 0 := by
  cases x with
  | inl W => simp [childBlock, blockKey, terminalDomain, roleDomain, role]
  | inr x =>
    cases x with
    | inl WV => simp [childBlock, blockKey, terminalDomain, roleDomain, role]
    | inr x =>
      cases x with
      | inl b =>
        simp [childBlock, blockKey, terminalDomain, roleDomain, role]
      | inr d =>
        simp [childBlock, blockKey, terminalDomain, roleDomain, role]

private theorem singleton_load (price : ℚ) (x : Point child (D := D)) :
    (∑ d : Candidate child (D := D), if x ∈ ({terminal d} : Finset (Point child (D := D))) then price else 0) =
      if x ∈ roleDomain child 3 then price else 0 := by
  rcases x with W | (WV | (b | d)) <;>
    simp [terminal, roleDomain, role]

/-- Actual whole-child-block ABS compiler. A block charge is activated by
the first challenge *or terminal* query at its prefix. The terminal base
charge is paid separately; both prices are included on terminal calls. -/
theorem terminal_block_oracle_sound
    (blockWeight : RootPrefix child (D := D) → (Point child (D := D) → Answer child) → ℚ)
    (baseWeight : Candidate child (D := D) → (Point child (D := D) → Answer child) → ℚ)
    (blockPrice basePrice : ℚ) (hbp : 0 ≤ blockPrice) (htp : 0 ≤ basePrice)
    (hbn : ∀ b H, 0 ≤ blockWeight b H) (htn : ∀ d H, 0 ≤ baseWeight d H)
    (hbl : ∀ b off, average (fun on => blockWeight b
      ((split (childBlock child b)).symm (on, off))) ≤ blockPrice)
    (htl : ∀ d off, average (fun on => baseWeight d
      ((split ({terminal d} : Finset (Point child (D := D)))).symm (on, off))) ≤ basePrice)
    (event : Candidate child (D := D) → (Point child (D := D) → Answer child) → Prop)
    (hcover : ∀ d H, event d H →
      1 ≤ blockWeight (childPrefix child d) H + baseWeight d H) :
    OracleSound (terminalDomain child) event
      ⟨blockPrice+basePrice, blockPrice+basePrice, add_nonneg hbp htp, add_nonneg hbp htp⟩ := by
  let support : RootPrefix child (D := D) ⊕ Candidate child (D := D) → Finset (Point child (D := D))
    | .inl b => childBlock child b
    | .inr d => {terminal d}
  let weight : (RootPrefix child (D := D) ⊕ Candidate child (D := D)) → (Point child (D := D) → Answer child) → ℚ
    | .inl b => blockWeight b
    | .inr d => baseWeight d
  let budget : RootPrefix child (D := D) ⊕ Candidate child (D := D) → ℚ
    | .inl _ => blockPrice
    | .inr _ => basePrice
  apply oracle_sound_of_footprints (terminalDomain child) terminal support weight budget
    ⟨blockPrice+basePrice, blockPrice+basePrice, add_nonneg hbp htp, add_nonneg hbp htp⟩
  · intro i H; cases i with
    | inl b => exact hbn b H
    | inr d => exact htn d H
  · intro i; cases i <;> assumption
  · intro i off; cases i with
    | inl b => exact hbl b off
    | inr d => exact htl d off
  · intro x
    simp only [Fintype.sum_sum_type, support, budget]
    rw [block_load, singleton_load]
    by_cases h : x ∈ roleDomain child 3
    · have hd : x ∈ terminalDomain child := mem_filter.mpr ⟨mem_univ _,by
        have hh := (mem_filter.mp h).2
        rw [hh]; decide⟩
      simp [h, hd]
    · by_cases hd : x ∈ terminalDomain child
      · simpa only [h, hd, ↓reduceIte, add_zero] using le_add_of_nonneg_right htp
      · simp [h, hd]
  · intro d
    simp only [Fintype.sum_sum_type, support, budget]
    rw [block_load, singleton_load]
    simp [terminalDomain, roleDomain, role, terminal]
  · intro d H he
    simp only [Fintype.sum_sum_type, support, weight]
    have hb : blockWeight (childPrefix child d) H ≤
        ∑ b : RootPrefix child (D := D), if terminal d ∈ childBlock child b then blockWeight b H else 0 := by
      simpa only [terminal_mem_childBlock, ↓reduceIte] using
        (single_le_sum (f := fun b => if terminal d ∈ childBlock child b then blockWeight b H else 0)
          (fun b (_ : b ∈ (univ : Finset (RootPrefix child (D := D)))) =>
          by split_ifs; exact hbn b H; exact le_rfl) (mem_univ (childPrefix child d)))
    have ht : baseWeight d H ≤
        ∑ e : Candidate child (D := D), if terminal d ∈ ({terminal e} : Finset (Point child (D := D)))
          then baseWeight e H else 0 := by
      simpa only [mem_singleton, ↓reduceIte] using
        (single_le_sum (f := fun e => if terminal d ∈ ({terminal e} : Finset (Point child (D := D)))
          then baseWeight e H else 0) (fun e (_ : e ∈ (univ : Finset (Candidate child (D := D)))) =>
          by split_ifs; exact htn e H; exact le_rfl) (mem_univ d))
    exact (hcover d H he).trans (add_le_add hb ht)



variable (ctx : Context child (D := D))
variable (cp : HahnSystemCertificate child.instance)

theorem root_of_mem_block (b : RootPrefix child (D := D)) (x : Point child (D := D))
    (h : x ∈ childBlock child b) : TwoLevel.root x = b.1 := by
  have hh := (mem_childBlock child b x).mp h
  rcases x with a | (ab | (c | d))
  · cases hh
  · cases hh
  · have he := Option.some.inj hh; rw [← he]; rfl
  · have he := Option.some.inj hh; rw [← he]; rfl

theorem commitment_of_mem_block (b : RootPrefix child (D := D)) (x : Point child (D := D))
    (h : x ∈ childBlock child b) : childCommitment child x = some (b.1,b.2.1) := by
  have hh := (mem_childBlock child b x).mp h
  rcases x with a | (ab | (c | d))
  · cases hh
  · cases hh
  · have he := Option.some.inj hh; rw [← he]; rfl
  · have he := Option.some.inj hh; rw [← he]; rfl

theorem parent_off_block (b : RootPrefix child (D := D)) (H H' : Point child (D := D) → Answer child)
    (ho : ∀ x, x ∉ childBlock child b → H x = H' x) :
    ctx.parent b.1 H = ctx.parent b.1 H' := by
  apply ctx.parent_off
  intro x hx
  exact ho x (fun hm => hx (root_of_mem_block child b x hm))

theorem descendant_off_block (b : RootPrefix child (D := D)) (H H' : Point child (D := D) → Answer child)
    (ho : ∀ x, x ∉ childBlock child b → H x = H' x) :
    ctx.descendant (b.1,b.2.1) H = ctx.descendant (b.1,b.2.1) H' := by
  apply ctx.descendant_off
  intro x hx
  exact ho x (fun hm => hx (commitment_of_mem_block child b x hm))

noncomputable def blockWeight (σ : I.layer.Statement) (b : RootPrefix child (D := D))
    (H : Point child (D := D) → Answer child) : ℚ :=
  TwoLevel.wholeChildBlockWeight child cp σ
    (ctx.parent b.1 H,ctx.descendant (b.1,b.2.1) H,b.2.2) (liftOracle child b.1 b.2.1 H)

noncomputable def baseWeight (σ : I.layer.Statement) (d : Candidate child (D := D))
    (H : Point child (D := D) → Answer child) : ℚ :=
  TwoLevel.normalizedChildBaseWeight child cp σ (extractedCandidate child (D := D) ctx d H)
    (liftOracle child d.1 d.2.1 H)

theorem blockWeight_nonneg (σ : I.layer.Statement) (b : RootPrefix child (D := D))
    (H : Point child (D := D) → Answer child) : 0 ≤ blockWeight child ctx cp σ b H :=
  TwoLevel.wholeChildBlockWeight_nonneg child cp σ _ _

theorem baseWeight_nonneg (σ : I.layer.Statement) (d : Candidate child (D := D))
    (H : Point child (D := D) → Answer child) : 0 ≤ baseWeight child ctx cp σ d H :=
  TwoLevel.normalizedChildBaseWeight_nonneg child cp σ _ _

/-- Local averaging of a terminal base retains the actual extracted oracles. -/
theorem baseWeight_local (σ : I.layer.Statement) (d : Candidate child (D := D))
    (off : Outside ({terminal d} : Finset (Point child (D := D))) → Answer child) :
    average (fun on => baseWeight child ctx cp σ d ((split {terminal d}).symm (on,off))) ≤ cp.threshold := by
  let S : Finset (Point child (D := D)) := {terminal d}
  let H (on : Inside S → Answer child) := (split S).symm (on,off)
  let base := H (fun _ => Classical.choice inferInstance)
  let W := ctx.parent d.1 base
  let V := ctx.descendant (d.1,d.2.1) base
  let g : Outside S := ⟨gamma d.1,by simp [S,gamma,terminal]⟩
  let c : Outside S := ⟨childGamma d.1 d.2.1 d.2.2.1,by simp [S,childGamma,terminal]⟩
  let t : Inside S := ⟨terminal d,by simp [S]⟩
  let stmt := child.link.statement σ W (off g).1.1 d.2.2.1
  let coin := (off c).2.1
  let density := childResponseDensity child stmt V coin d.2.2.2
  have hw (on : Inside S → Answer child) : ctx.parent d.1 (H on) = W := by
    apply parent_off_point child ctx d.1 (terminal d) rfl
    intro x hx
    exact (split_outside_eval S _ off x (by simpa [S] using hx)).trans
      (split_outside_eval S _ off x (by simpa [S] using hx)).symm
  have hv (on : Inside S → Answer child) : ctx.descendant (d.1,d.2.1) (H on) = V := by
    apply descendant_off_point child ctx (d.1,d.2.1) (terminal d) rfl
    intro x hx
    exact (split_outside_eval S _ off x (by simpa [S] using hx)).trans
      (split_outside_eval S _ off x (by simpa [S] using hx)).symm
  have he (on : Inside S → Answer child) : baseWeight child ctx cp σ d (H on) =
      basePrice cp.threshold density * indicator
        (child.instance.layer.verify stmt V coin d.2.2.2 (on t).2.2) := by
    unfold baseWeight normalizedChildBaseWeight childBlockStatement TwoLevel.childPrefix extractedCandidate
    simp only [liftOracle,hw,hv,gamma,query,childGamma,terminal]
    rw [show H on (Sum.inl d.1) = off g from split_outside_eval S _ off _ g.property,
      show H on (Sum.inr (Sum.inr (Sum.inl (d.1,d.2.1,d.2.2.1)))) = off c from split_outside_eval S _ off _ c.property,
      show H on (Sum.inr (Sum.inr (Sum.inr d))) = on t from split_inside_eval S _ off _ t.property]
  change average (fun on : Inside S → Answer child => baseWeight child ctx cp σ d (H on)) ≤ _
  simp_rw [he]
  rw [average_eval t (fun a : Answer child => basePrice cp.threshold density * indicator
    (child.instance.layer.verify stmt V coin d.2.2.2 a.2.2))]
  change mean (fun a : Answer child => _) ≤ _
  rw [mean_mul_left]
  have hd : mean (fun a : Answer child => indicator
      (child.instance.layer.verify stmt V coin d.2.2.2 a.2.2)) = density := by
    simp only [mean_prod,mean_const]
    exact mean_indicator _
  rw [hd]
  exact basePrice_mul_le cp.threshold_nonneg


/-- The whole terminal footprint still has its exact normalized excess mean. -/
theorem rigidPart_local (stmt : child.instance.layer.Statement)
    (b : RootPrefix child (D := D)) (W : I.layer.Oracle) (V : child.instance.layer.Oracle)
    (off : Outside (childBlock child b) → Answer child) :
    average (fun on => rigidChildBlockWeight child cp stmt (W,V,b.2.2)
      (liftOracle child b.1 b.2.1 ((split (childBlock child b)).symm (on,off)))) =
    mean (fun a => responseIncidence child.instance cp stmt V a
      (coveredRigidResponses child.instance cp stmt V a (fun _ => False)
        (highSystems child.instance cp V)) - cp.threshold) := by
  let g : Inside (childBlock child b) := ⟨childGamma b.1 b.2.1 b.2.2,childGamma_mem_childBlock child b⟩
  let t (u : child.instance.layer.Payload) : Inside (childBlock child b) :=
    ⟨terminal (b.1,b.2.1,b.2.2,u),by simp [blockKey,terminal,childPrefix]⟩
  have htg (u : child.instance.layer.Payload) : t u ≠ g := by
    intro h
    have hh := congrArg Subtype.val h
    simp [t,g,terminal,childGamma] at hh
  have hden (a : Answer child) (u : child.instance.layer.Payload) :
      average (fun c : Answer child => if child.instance.layer.verify stmt V a.2.1 u c.2.2
        then (1:ℚ) else 0) = childResponseDensity child stmt V a.2.1 u := by
    change mean (fun c : Answer child => indicator (child.instance.layer.verify stmt V a.2.1 u c.2.2)) = _
    simp only [mean_prod,mean_const]
    exact mean_indicator _
  have hn := normalized_block_average g t htg cp.threshold cp.threshold_nonneg
    (fun a : Answer child => a.2.1.2 ∈ ReducedSystems.badChallenges
      (LigeroFamily.PolynomialDirect.primaryCode child.instance.domain child.instance.primary_le)
      (Local.Polygero.oracleWords V.ordinary) V.proximityMask)
    (fun a => coveredRigidResponses child.instance cp stmt V a.2.1 (fun _ => False)
      (highSystems child.instance cp V))
    (fun a u c => child.instance.layer.verify stmt V a.2.1 u c.2.2)
  simp_rw [hden] at hn
  have hw (on : Inside (childBlock child b) → Answer child) :
      rigidChildBlockWeight child cp stmt (W,V,b.2.2)
        (liftOracle child b.1 b.2.1 ((split (childBlock child b)).symm (on,off))) =
      (if (on g).2.1.2 ∈ ReducedSystems.badChallenges
        (LigeroFamily.PolynomialDirect.primaryCode child.instance.domain child.instance.primary_le)
        (Local.Polygero.oracleWords V.ordinary) V.proximityMask then 1-cp.threshold else
        ∑ u ∈ coveredRigidResponses child.instance cp stmt V (on g).2.1 (fun _ => False)
          (highSystems child.instance cp V),
          (1-basePrice cp.threshold (childResponseDensity child stmt V (on g).2.1 u)) *
            (if child.instance.layer.verify stmt V (on g).2.1 u (on (t u)).2.2 then 1 else 0)) := by
    simp only [rigidChildBlockWeight,liftOracle,childGamma,terminal,indicator]
    simp only [show (split (childBlock child b)).symm (on,off) (Sum.inr (Sum.inr (Sum.inl (b.1,b.2.1,b.2.2)))) = on g
      from split_inside_eval _ _ _ _ g.property]
    congr 1
    apply sum_congr rfl
    intro u _
    exact congrArg (fun a : Answer child => (1-basePrice cp.threshold
      (childResponseDensity child stmt V (on g).2.1 u)) *
        (if child.instance.layer.verify stmt V (on g).2.1 u a.2.2 then 1 else 0))
      (split_inside_eval _ _ _ _ (t u).property)
  simp_rw [hw]
  rw [hn]
  change mean (fun a : Answer child => _) = _
  simp only [mean_prod,mean_const]
  congr 1
  funext a
  unfold responseIncidence childResponseDensity
  split_ifs <;> ring

theorem blockWeight_local (σ : I.layer.Statement) (price : ℚ)
    (hmean : ∀ (stmt : child.instance.layer.Statement) (V : child.instance.layer.Oracle),
      mean (fun a => responseIncidence child.instance cp stmt V a
        (coveredRigidResponses child.instance cp stmt V a (fun _ => False)
          (highSystems child.instance cp V)) - cp.threshold +
        indicator (nonrigidException child.instance cp stmt V (highSystems child.instance cp V) a)) ≤ price)
    (b : RootPrefix child (D := D)) (off : Outside (childBlock child b) → Answer child) :
    average (fun on => blockWeight child ctx cp σ b
      ((split (childBlock child b)).symm (on,off))) ≤ price := by
  let S := childBlock child b
  let H (on : Inside S → Answer child) := (split S).symm (on,off)
  let base := H (fun _ => Classical.choice inferInstance)
  let W := ctx.parent b.1 base
  let V := ctx.descendant (b.1,b.2.1) base
  let g : Outside S := ⟨gamma b.1,by simp [S,blockKey,gamma]⟩
  let coin : Inside S := ⟨childGamma b.1 b.2.1 b.2.2,childGamma_mem_childBlock child b⟩
  let stmt := child.link.statement σ W (off g).1.1 b.2.2
  have hw (on : Inside S → Answer child) : ctx.parent b.1 (H on) = W := by
    apply parent_off_block child ctx b
    intro x hx
    exact (split_outside_eval S _ off x hx).trans (split_outside_eval S _ off x hx).symm
  have hv (on : Inside S → Answer child) : ctx.descendant (b.1,b.2.1) (H on) = V := by
    apply descendant_off_block child ctx b
    intro x hx
    exact (split_outside_eval S _ off x hx).trans (split_outside_eval S _ off x hx).symm
  have he (on : Inside S → Answer child) : blockWeight child ctx cp σ b (H on) =
      rigidChildBlockWeight child cp stmt (W,V,b.2.2) (liftOracle child b.1 b.2.1 (H on)) +
      indicator (nonrigidException child.instance cp stmt V (highSystems child.instance cp V) (on coin).2.1) := by
    unfold blockWeight wholeChildBlockWeight childBlockStatement
    simp only [hw,hv,liftOracle,gamma,query,childGamma,terminal]
    rw [show H on (Sum.inl b.1) = off g from split_outside_eval S _ off _ g.property,
      show H on (Sum.inr (Sum.inr (Sum.inl (b.1,b.2.1,b.2.2)))) = on coin from split_inside_eval S _ off _ coin.property]
    exact congrArg (fun U : child.instance.layer.Oracle =>
      rigidChildBlockWeight child cp stmt (W,V,b.2.2) (liftOracle child b.1 b.2.1 (H on)) +
        indicator (nonrigidException child.instance cp stmt U (highSystems child.instance cp U) (on coin).2.1)) (hv on)
  change average (fun on : Inside S → Answer child => blockWeight child ctx cp σ b (H on)) ≤ _
  simp_rw [he]
  rw [average_add,rigidPart_local]
  have hc : average (fun on : Inside S → Answer child => indicator
      (nonrigidException child.instance cp stmt V (highSystems child.instance cp V) (on coin).2.1)) =
      mean (fun a => indicator (nonrigidException child.instance cp stmt V (highSystems child.instance cp V) a)) := by
    rw [average_eval coin (fun a : Answer child => indicator
      (nonrigidException child.instance cp stmt V (highSystems child.instance cp V) a.2.1))]
    change mean (fun a : Answer child => _) = _
    simp only [mean_prod,mean_const]
  rw [hc,← mean_add]
  exact hmean stmt V

variable (p : HahnSystemCertificate I)

theorem child_oracle_sound (σ : I.layer.Statement) (price : ℚ) (hp : 0 ≤ price)
    (hmean : ∀ (stmt : child.instance.layer.Statement) (V : child.instance.layer.Oracle),
      mean (fun a => responseIncidence child.instance cp stmt V a
        (coveredRigidResponses child.instance cp stmt V a (fun _ => False)
          (highSystems child.instance cp V)) - cp.threshold +
        indicator (nonrigidException child.instance cp stmt V (highSystems child.instance cp V) a)) ≤ price) :
    OracleSound (terminalDomain child)
      (fun d H => failure child ctx p cp σ d H ∧ ¬ queryRisk child ctx cp σ d.1 d.2.1 H)
      (Rate.diagonal (price+cp.threshold) (add_nonneg hp cp.threshold_nonneg)) := by
  apply terminal_block_oracle_sound child (blockWeight child ctx cp σ) (baseWeight child ctx cp σ)
    price cp.threshold hp cp.threshold_nonneg (blockWeight_nonneg child ctx cp σ)
    (baseWeight_nonneg child ctx cp σ) (blockWeight_local child ctx cp σ price hmean)
    (baseWeight_local child ctx cp σ)
  intro d H he
  exact wholeChildBlock_pay child cp p σ (extractedCandidate child (D := D) ctx d H)
    (liftOracle child d.1 d.2.1 H) he.1 he.2

end RecursivePolygero.FiatShamir.MerkleFS
