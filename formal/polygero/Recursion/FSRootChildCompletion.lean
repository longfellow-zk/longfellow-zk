import polygero.Recursion.FSRootChildFresh

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.FiatShamir.MerkleFS.SplitChild
open Finset Counting ProfileAnalysis Bcs.AffineBlock Bcs.TotalOracle Bcs.TotalOracle.Footprint
open TwoLevel Merkle.RandomOracle
open scoped Classical
variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [DecidableEq D]
variable {I : Instance F} (child : Child I) (ctx : Context child (D := D))
variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance) (σ : I.layer.Statement)

noncomputable def completion (d : Candidate child (D := D)) (seen : Finset (Point child (D := D)))
    (H : Point child (D := D) → Answer child) : ℚ :=
  if childGamma d.1 d.2.1 d.2.2.1 ∈ seen then
    if terminal d ∈ seen then 0 else baseWeight child ctx cp σ d H
  else if terminal d ∈ seen then exceptionWeight child ctx cp σ (childPrefix child d) H
  else if failure child ctx p cp σ d H ∧ ¬ queryRisk child ctx cp σ d.1 d.2.1 H then 1 else 0

variable (C : ℚ) (hC : 0 ≤ C)
variable (hcapacity : ∀ V, rigidExcessMass child.instance cp V+nonrigidMass child.instance cp V ≤ C)
variable (hsmall : cp.listBound < Nat.card F)
variable (hbase : cp.threshold+(1-cp.threshold)/(Nat.card F : ℚ) ≤ C/Nat.card F)
variable (htheta : cp.threshold ≤ splitChildSlope child.instance cp C)
variable (herror : cp.error ≤ splitChildSlope child.instance cp C)

include hC hcapacity htheta herror in
theorem completion_average_le {N : ℕ}
    (tree : Tree (Point child (D := D)) (Answer child) (Candidate child (D := D)) N) :
    average (fun H => completion child ctx p cp σ (tree.run H).1 (queried tree H).toFinset H) ≤
      splitChildSlope child.instance cp C := by
  apply trace_completion_average_le tree
    (fun d seen => {childGamma d.1 d.2.1 d.2.2.1,terminal d} \ seen)
    (completion child ctx p cp σ) (splitChildSlope child.instance cp C)
  · intros; exact disjoint_left.mpr (fun _ h h' => (mem_sdiff.mp h).2 h')
  · intro d seen
    let x : Point child (D := D) := childGamma d.1 d.2.1 d.2.2.1
    let y : Point child (D := D) := terminal d
    by_cases hx : x ∈ seen <;> by_cases hy : y ∈ seen
    all_goals try dsimp only [x,y] at hx hy
    · intro off
      simp only [completion,hx,hy,↓reduceIte,average_const]
      exact splitChildSlope_nonneg child.instance cp C hC
    · have he : ({x,y} : Finset (Point child (D := D))) \ seen = {y} := by ext z; simp; aesop
      rw [he]
      intro off
      simpa only [completion,hx,hy,↓reduceIte] using
        (baseWeight_local child ctx cp σ d off).trans htheta
    · have he : ({x,y} : Finset (Point child (D := D))) \ seen = {x} := by ext z; simp; aesop
      rw [he]
      intro off
      have hl := exception_local child ctx cp σ (childPrefix child d) off
      let V := ctx.descendant (d.1,d.2.1)
        ((split ({x} : Finset (Point child (D := D)))).symm (fun _ => Classical.choice inferInstance,off))
      have hj := split_budget_joint_le child.instance cp V C (hcapacity V)
      have hp : nonrigidBudget child.instance cp V ≤ splitChildSlope child.instance cp C := by
        linarith [rigidBudget_nonneg child.instance cp V]
      simp only [completion,hx,hy,↓reduceIte]
      change average (fun on => exceptionWeight child ctx cp σ (childPrefix child d)
        ((split {x}).symm (on,off))) ≤ splitChildSlope child.instance cp C
      change average (fun on => exceptionWeight child ctx cp σ (childPrefix child d)
        ((split {x}).symm (on,off))) ≤ nonrigidBudget child.instance cp V at hl
      linarith
    · have he : ({x,y} : Finset (Point child (D := D))) \ seen = {x,y} := by ext z; simp; aesop
      rw [he]
      intro off
      simpa only [completion,hx,hy,↓reduceIte] using
        (fresh_pair_mean child ctx p cp σ d off).trans herror

private theorem selected_charge_le {A Q C : Type} [Fintype A] [DecidableEq Q]
    {N : ℕ} (tree : Tree Q C Unit N) (H : Q → C)
    (support : A → Finset Q) (weight : A → ℚ) (i : A)
    (hn : ∀ a, 0 ≤ weight a) (hh : hits tree H (support i) = true) :
    weight i ≤ ∑ a, if hits tree H (support a) then weight a else 0 := by
  simpa only [hh,↓reduceIte] using
    single_le_sum (f := fun a => if hits tree H (support a) then weight a else 0)
      (fun a _ => by split_ifs; exact hn a; rfl) (mem_univ i)

theorem completion_pay {N : ℕ}
    (tree : Tree (Point child (D := D)) (Answer child) (Candidate child (D := D)) N)
    (H : Point child (D := D) → Answer child)
    (hf : failure child ctx p cp σ (tree.run H).1 H ∧
      ¬ queryRisk child ctx cp σ (tree.run H).1.1 (tree.run H).1.2.1 H) :
    1 ≤ footprintCharge tree (support child) (weight child ctx cp σ) H+
      completion child ctx p cp σ (tree.run H).1 (queried tree H).toFinset H := by
  let d := (tree.run H).1
  let b := childPrefix child d
  let x : Point child (D := D) := childGamma d.1 d.2.1 d.2.2.1
  let y : Point child (D := D) := terminal d
  let seen := (queried tree H).toFinset
  let unitTree := tree.map (fun _ => ())
  have hhits (S : Finset (Point child (D := D))) : hits unitTree H S = hits tree H S := by
    dsimp only [unitTree]
    clear hf
    induction tree with
    | done => rfl
    | query q next ih => simp [Merkle.RandomOracle.Tree.map,hits,ih]
  have hl :
      (if x ∈ seen ∨ y ∈ seen then rigidWeight child ctx cp σ b H else 0)+
      (if x ∈ seen then exceptionWeight child ctx cp σ b H else 0)+
      (if y ∈ seen then baseWeight child ctx cp σ d H else 0) ≤
        footprintCharge tree (support child) (weight child ctx cp σ) H := by
    unfold footprintCharge
    simp only [Fintype.sum_sum_type,support,weight]
    simp_rw [← hhits]
    apply add_le_add
    · apply add_le_add
      · split_ifs with h
        · apply selected_charge_le unitTree H (childBlock child) (fun b => rigidWeight child ctx cp σ b H) b
            (fun b => rigidChildBlockWeight_nonneg child cp _ _ _)
          rw [hhits]
          rcases h with hx | hy
          · exact hits_of_mem tree H _ x (List.mem_toFinset.mp hx) (childGamma_mem_childBlock child b)
          · exact hits_of_mem tree H _ y (List.mem_toFinset.mp hy) (terminal_mem_childBlock child d)
        · exact sum_nonneg (fun b _ => by split_ifs; exact rigidChildBlockWeight_nonneg child cp _ _ _; rfl)
      · split_ifs with h
        · apply selected_charge_le unitTree H (fun b : RootPrefix child (D := D) => {childGamma b.1 b.2.1 b.2.2})
            (fun b => exceptionWeight child ctx cp σ b H) b (fun b => indicator_nonneg _)
          rw [hhits]
          exact hits_of_mem tree H _ x (List.mem_toFinset.mp h) (mem_singleton_self _)
        · exact sum_nonneg (fun b _ => by split_ifs; exact indicator_nonneg _; rfl)
    · split_ifs with h
      · apply selected_charge_le unitTree H (fun d : Candidate child (D := D) => {terminal d})
          (fun d => baseWeight child ctx cp σ d H) d (fun d => baseWeight_nonneg child ctx cp σ d H)
        rw [hhits]
        exact hits_of_mem tree H _ y (List.mem_toFinset.mp h) (mem_singleton_self _)
      · exact sum_nonneg (fun d _ => by split_ifs; exact baseWeight_nonneg child ctx cp σ d H; rfl)
  have hp := wholeChildBlock_pay child cp p σ (extractedCandidate child ctx d H)
    (liftOracle child d.1 d.2.1 H) hf.1 hf.2
  change 1 ≤ blockWeight child ctx cp σ b H+baseWeight child ctx cp σ d H at hp
  rw [blockWeight_eq] at hp
  change 1 ≤ _+completion child ctx p cp σ d seen H
  by_cases hx : x ∈ seen <;> by_cases hy : y ∈ seen
  all_goals try dsimp only [x,y] at hx hy
  · simp only [x,y,hx,hy,true_or,if_true] at hl
    simp only [completion,hx,hy,↓reduceIte,add_zero]
    exact hp.trans hl
  · simp only [x,y,hx,hy,true_or,if_true,if_false,add_zero] at hl
    simp only [completion,hx,hy,↓reduceIte]
    linarith
  · simp only [x,y,hx,hy,false_or,if_true,if_false,add_zero] at hl
    simp only [completion,hx,hy,↓reduceIte]
    linarith
  · simp only [x,y,hx,hy,false_or,if_false,zero_add] at hl
    have hfd : failure child ctx p cp σ d H ∧ ¬ queryRisk child ctx cp σ d.1 d.2.1 H := hf
    rw [completion,if_neg hx,if_neg hy,if_pos hfd]
    linarith

include hC hcapacity hsmall hbase in
theorem oracle_sound_joint_completion :
    OracleSound (terminalDomain child)
      (fun d H => failure child ctx p cp σ d H ∧ ¬ queryRisk child ctx cp σ d.1 d.2.1 H)
      (Rate.diagonal (splitChildSlope child.instance cp C)
        (splitChildSlope_nonneg child.instance cp C hC)) := by
  refine oracle_sound_of_contextual_footprint_completion (terminalDomain child) (support child)
    (weight child ctx cp σ) (budget child ctx cp) _ (weight_nonneg child ctx cp σ)
    (budget_nonneg child ctx cp) (local_mean child ctx cp σ) ?_
    (fun {_} tree H => completion child ctx p cp σ (tree.run H).1 (queried tree H).toFinset H) ?_ ?_ _ ?_
  · intro H x
    simp_rw [budget_eq]
    rw [query_load]
    rcases x with a | (ab | (b | d))
    · simp [terminalDomain,role]
    · simp [terminalDomain,role]
    · simpa [terminalDomain,role,Rate.diagonal] using split_budget_joint_le child.instance cp
        (ctx.descendant (b.1,b.2.1) H) C (hcapacity _)
    · simpa [terminalDomain,role,Rate.diagonal] using split_budget_terminal_le child.instance cp
        (ctx.descendant (d.1,d.2.1) H) C hsmall hbase
  · intro N tree H
    unfold completion
    split_ifs <;> first | exact baseWeight_nonneg child ctx cp σ _ H | exact indicator_nonneg _ | norm_num
  · intro N tree
    simpa only [Rate.diagonal] using completion_average_le child ctx p cp σ C hC hcapacity
      (threshold_le_splitChildSlope child.instance cp C hbase)
      (error_le_splitChildSlope child.instance cp C hbase) tree
  · intro N tree H hf; exact completion_pay child ctx p cp σ tree H hf

end RecursivePolygero.FiatShamir.MerkleFS.SplitChild
