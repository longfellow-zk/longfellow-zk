import polygero.Recursion.FSLocalDomains
import polygero.Recursion.FSQueryCapacity
import polygero.Local.RigidResponseIncidence
import Bcs.TerminalCharges

/-! Whole-child-block fractional charging on the actual typed FS inputs. -/

set_option maxHeartbeats 2000000

namespace RecursivePolygero.FiatShamir.TwoLevel

open Finset Counting ProfileAnalysis Local Bcs.AffineBlock Bcs.TotalOracle.Footprint
open Bcs.TerminalCharges
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)

abbrev ChildPrefix := I.layer.Oracle × child.instance.layer.Oracle × I.layer.Query

def childPrefix (d : Proof child) : ChildPrefix child := (d.1, d.2.1, d.2.2.1)

def childKey : HashInput child → Option (ChildPrefix child)
  | .inl _ => none
  | .inr (.inl _) => none
  | .inr (.inr (.inl b)) => some b
  | .inr (.inr (.inr d)) => some (childPrefix child d)

/-- The child challenge and all terminal keys with this fixed prefix.
The parent challenge and parent query remain outside this footprint. -/
noncomputable def childBlock (b : ChildPrefix child) : Finset (HashInput child) :=
  univ.filter (fun x => childKey child x = some b)

@[simp] theorem mem_childBlock (b : ChildPrefix child) (x : HashInput child) :
    x ∈ childBlock child b ↔ childKey child x = some b := by simp [childBlock]

theorem terminal_mem_childBlock (d : Proof child) :
    terminal d ∈ childBlock child (childPrefix child d) := by
  simp [childKey, terminal]

theorem childGamma_mem_childBlock (b : ChildPrefix child) :
    childGamma b.1 b.2.1 b.2.2 ∈ childBlock child b := by
  simp [childKey, childGamma]

theorem gamma_not_mem_childBlock (b : ChildPrefix child) (W : I.layer.Oracle) :
    gamma W ∉ childBlock child b := by simp [childKey, gamma]

theorem query_not_mem_childBlock (b : ChildPrefix child) (W : I.layer.Oracle)
    (V : child.instance.layer.Oracle) : query W V ∉ childBlock child b := by
  simp [childKey, query]

theorem childBlock_disjoint : Pairwise (fun a b =>
    Disjoint (childBlock child a) (childBlock child b)) := by
  intro a b hab
  apply disjoint_left.mpr
  intro x ha hb
  exact hab (Option.some.inj ((mem_childBlock child a x).mp ha |>.symm.trans
    ((mem_childBlock child b x).mp hb)))

noncomputable def terminalBlockDomain : Finset (HashInput child) :=
  roleDomain child 2 ∪ roleDomain child 3

private theorem block_load (price : ℚ) (x : HashInput child) :
    (∑ b : ChildPrefix child, if x ∈ childBlock child b then price else 0) =
      if x ∈ terminalBlockDomain child then price else 0 := by
  cases x with
  | inl W => simp [childBlock, childKey, terminalBlockDomain, roleDomain, hashRole]
  | inr x =>
    cases x with
    | inl WV => simp [childBlock, childKey, terminalBlockDomain, roleDomain, hashRole]
    | inr x =>
      cases x with
      | inl b =>
        simp [childBlock, childKey, terminalBlockDomain, roleDomain, hashRole]
      | inr d =>
        simp [childBlock, childKey, terminalBlockDomain, roleDomain, hashRole]

private theorem singleton_load (price : ℚ) (x : HashInput child) :
    (∑ d : Proof child, if x ∈ ({terminal d} : Finset (HashInput child)) then price else 0) =
      if x ∈ roleDomain child 3 then price else 0 := by
  rcases x with W | (WV | (b | d)) <;>
    simp [terminal, roleDomain, hashRole]

/-- Actual whole-child-block ABS compiler. A block charge is activated by
the first challenge *or terminal* query at its prefix. The terminal base
charge is paid separately; both prices are included on terminal calls. -/
theorem terminal_block_oracle_sound
    (blockWeight : ChildPrefix child → (HashInput child → Answer child) → ℚ)
    (baseWeight : Proof child → (HashInput child → Answer child) → ℚ)
    (blockPrice basePrice : ℚ) (hbp : 0 ≤ blockPrice) (htp : 0 ≤ basePrice)
    (hbn : ∀ b H, 0 ≤ blockWeight b H) (htn : ∀ d H, 0 ≤ baseWeight d H)
    (hbl : ∀ b off, average (fun on => blockWeight b
      ((split (childBlock child b)).symm (on, off))) ≤ blockPrice)
    (htl : ∀ d off, average (fun on => baseWeight d
      ((split ({terminal d} : Finset (HashInput child))).symm (on, off))) ≤ basePrice)
    (event : Proof child → (HashInput child → Answer child) → Prop)
    (hcover : ∀ d H, event d H →
      1 ≤ blockWeight (childPrefix child d) H + baseWeight d H) :
    OracleSound (terminalBlockDomain child) event
      ⟨blockPrice+basePrice, blockPrice+basePrice, add_nonneg hbp htp, add_nonneg hbp htp⟩ := by
  let support : ChildPrefix child ⊕ Proof child → Finset (HashInput child)
    | .inl b => childBlock child b
    | .inr d => {terminal d}
  let weight : (ChildPrefix child ⊕ Proof child) → (HashInput child → Answer child) → ℚ
    | .inl b => blockWeight b
    | .inr d => baseWeight d
  let budget : ChildPrefix child ⊕ Proof child → ℚ
    | .inl _ => blockPrice
    | .inr _ => basePrice
  apply oracle_sound_of_footprints (terminalBlockDomain child) terminal support weight budget
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
    · have hd : x ∈ terminalBlockDomain child := mem_union_right _ h
      simp [h, hd]
    · by_cases hd : x ∈ terminalBlockDomain child
      · simpa only [h, hd, ↓reduceIte, add_zero] using le_add_of_nonneg_right htp
      · simp [h, hd]
  · intro d
    simp only [Fintype.sum_sum_type, support, budget]
    rw [block_load, singleton_load]
    simp [terminalBlockDomain, roleDomain, hashRole, terminal]
  · intro d H he
    simp only [Fintype.sum_sum_type, support, weight]
    have hb : blockWeight (childPrefix child d) H ≤
        ∑ b : ChildPrefix child, if terminal d ∈ childBlock child b then blockWeight b H else 0 := by
      simpa only [terminal_mem_childBlock, ↓reduceIte] using
        (single_le_sum (f := fun b => if terminal d ∈ childBlock child b then blockWeight b H else 0)
          (fun b (_ : b ∈ (univ : Finset (ChildPrefix child))) =>
          by split_ifs; exact hbn b H; exact le_rfl) (mem_univ (childPrefix child d)))
    have ht : baseWeight d H ≤
        ∑ e : Proof child, if terminal d ∈ ({terminal e} : Finset (HashInput child))
          then baseWeight e H else 0 := by
      simpa only [mem_singleton, ↓reduceIte] using
        (single_le_sum (f := fun e => if terminal d ∈ ({terminal e} : Finset (HashInput child))
          then baseWeight e H else 0) (fun e (_ : e ∈ (univ : Finset (Proof child))) =>
          by split_ifs; exact htn e H; exact le_rfl) (mem_univ d))
    exact (hcover d H he).trans (add_le_add hb ht)

variable (cp : HahnSystemCertificate child.instance)

noncomputable def childResponseDensity (σ : child.instance.layer.Statement)
    (V : child.instance.layer.Oracle) (a : child.instance.layer.Coin)
    (u : child.instance.layer.Payload) : ℚ :=
  (responseCount child.instance.layer σ V a u : ℚ) / Fintype.card child.instance.layer.Query

theorem childResponseDensity_nonneg (σ : child.instance.layer.Statement)
    (V : child.instance.layer.Oracle) (a : child.instance.layer.Coin)
    (u : child.instance.layer.Payload) : 0 ≤ childResponseDensity child σ V a u := by
  unfold childResponseDensity
  positivity

theorem childResponseDensity_le_one (σ : child.instance.layer.Statement)
    (V : child.instance.layer.Oracle) (a : child.instance.layer.Coin)
    (u : child.instance.layer.Payload) : childResponseDensity child σ V a u ≤ 1 := by
  unfold childResponseDensity
  apply (div_le_one (by exact_mod_cast Fintype.card_pos)).mpr
  exact_mod_cast (card_filter_le (s := (univ : Finset child.instance.layer.Query))
    (p := fun q => child.instance.layer.verify σ V a u q)).trans_eq (card_univ)

/-- The whole-block normalized excess for the actual rigid response set.
The rank event is paid once with weight `1-theta`, rather than once for
each payload. -/
noncomputable def rigidChildBlockWeight (σ : child.instance.layer.Statement)
    (b : ChildPrefix child) (H : HashInput child → Answer child) : ℚ :=
  let a := (H (childGamma b.1 b.2.1 b.2.2)).2.1
  if a.2 ∈ ReducedSystems.badChallenges
      (LigeroFamily.PolynomialDirect.primaryCode child.instance.domain child.instance.primary_le)
      (Local.Polygero.oracleWords b.2.1.ordinary) b.2.1.proximityMask then 1-cp.threshold else
    ∑ u ∈ coveredRigidResponses child.instance cp σ b.2.1 a (fun _ => False)
        (highSystems child.instance cp b.2.1),
      (1-basePrice cp.threshold (childResponseDensity child σ b.2.1 a u)) *
        indicator (child.instance.layer.verify σ b.2.1 a u
          (H (terminal (b.1,b.2.1,b.2.2,u))).2.2)

theorem rigidChildBlockWeight_nonneg (σ : child.instance.layer.Statement)
    (b : ChildPrefix child) (H : HashInput child → Answer child) :
    0 ≤ rigidChildBlockWeight child cp σ b H := by
  dsimp only [rigidChildBlockWeight]
  split_ifs
  · exact sub_nonneg.mpr cp.threshold_lt_one.le
  · exact sum_nonneg fun u _ => mul_nonneg
      (sub_nonneg.mpr (basePrice_le_one cp.threshold_nonneg)) (indicator_nonneg _)

/-- Exact whole-footprint mean of actual response charges. Every terminal
hash is resampled, so a cached response does not invalidate this identity. -/
theorem rigidChildBlockWeight_local_eq (σ : child.instance.layer.Statement)
    (b : ChildPrefix child)
    (off : Outside (childBlock child b) → Answer child) :
    average (fun on => rigidChildBlockWeight child cp σ b
      ((split (childBlock child b)).symm (on, off))) =
    mean (fun a => responseIncidence child.instance cp σ b.2.1 a
      (coveredRigidResponses child.instance cp σ b.2.1 a (fun _ => False)
        (highSystems child.instance cp b.2.1)) - cp.threshold) := by
  let g : Inside (childBlock child b) :=
    ⟨childGamma b.1 b.2.1 b.2.2, childGamma_mem_childBlock child b⟩
  let t (u : child.instance.layer.Payload) : Inside (childBlock child b) :=
    ⟨terminal (b.1,b.2.1,b.2.2,u), by simp [childKey, terminal, childPrefix]⟩
  have htg (u : child.instance.layer.Payload) : t u ≠ g := by
    intro h
    have hh := congrArg Subtype.val h
    simp [t, g, terminal, childGamma] at hh
  have hden (a : Answer child) (u : child.instance.layer.Payload) :
      average (fun c : Answer child => if child.instance.layer.verify σ b.2.1 a.2.1 u c.2.2
        then (1:ℚ) else 0) = childResponseDensity child σ b.2.1 a.2.1 u := by
    change mean (fun c : Answer child => indicator
      (child.instance.layer.verify σ b.2.1 a.2.1 u c.2.2)) = _
    simp only [mean_prod, mean_const]
    exact mean_indicator _
  have hn := normalized_block_average g t htg cp.threshold cp.threshold_nonneg
    (fun a : Answer child => a.2.1.2 ∈ ReducedSystems.badChallenges
      (LigeroFamily.PolynomialDirect.primaryCode child.instance.domain child.instance.primary_le)
      (Local.Polygero.oracleWords b.2.1.ordinary) b.2.1.proximityMask)
    (fun a => coveredRigidResponses child.instance cp σ b.2.1 a.2.1 (fun _ => False)
      (highSystems child.instance cp b.2.1))
    (fun a u c => child.instance.layer.verify σ b.2.1 a.2.1 u c.2.2)
  simp_rw [hden] at hn
  have hw (on : Inside (childBlock child b) → Answer child) :
      rigidChildBlockWeight child cp σ b ((split (childBlock child b)).symm (on, off)) =
      (if (on g).2.1.2 ∈ ReducedSystems.badChallenges
        (LigeroFamily.PolynomialDirect.primaryCode child.instance.domain child.instance.primary_le)
        (Local.Polygero.oracleWords b.2.1.ordinary) b.2.1.proximityMask then 1-cp.threshold else
        ∑ u ∈ coveredRigidResponses child.instance cp σ b.2.1 (on g).2.1 (fun _ => False)
          (highSystems child.instance cp b.2.1),
          (1-basePrice cp.threshold (childResponseDensity child σ b.2.1 (on g).2.1 u)) *
            (if child.instance.layer.verify σ b.2.1 (on g).2.1 u (on (t u)).2.2 then 1 else 0)) := by
    simp only [rigidChildBlockWeight, split_inside_eval _ _ _ _
      (childGamma_mem_childBlock child b), indicator, g, t]
    congr 1
    apply sum_congr rfl
    intro u _
    rw [split_inside_eval _ _ _ _ (t u).property]
  simp_rw [hw]
  rw [hn]
  change mean (fun a : Answer child => _) = _
  simp only [mean_prod, mean_const]
  congr 1
  funext a
  unfold responseIncidence childResponseDensity
  split_ifs <;> ring

noncomputable def childBlockStatement (σ : I.layer.Statement) (b : ChildPrefix child)
    (H : HashInput child → Answer child) : child.instance.layer.Statement :=
  child.link.statement σ b.1 (H (gamma b.1)).1.1 b.2.2

noncomputable def normalizedChildBaseWeight (σ : I.layer.Statement)
    (d : Proof child) (H : HashInput child → Answer child) : ℚ :=
  let a := (H (childGamma d.1 d.2.1 d.2.2.1)).2.1
  let s := childBlockStatement child σ (childPrefix child d) H
  basePrice cp.threshold (childResponseDensity child s d.2.1 a d.2.2.2) *
    indicator (child.instance.layer.verify s d.2.1 a d.2.2.2 (H (terminal d)).2.2)

theorem normalizedChildBaseWeight_nonneg (σ : I.layer.Statement)
    (d : Proof child) (H : HashInput child → Answer child) :
    0 ≤ normalizedChildBaseWeight child cp σ d H := by
  exact mul_nonneg (basePrice_nonneg cp.threshold_nonneg) (indicator_nonneg _)

theorem normalizedChildBaseWeight_local (σ : I.layer.Statement) (d : Proof child)
    (off : Outside ({terminal d} : Finset (HashInput child)) → Answer child) :
    average (fun on => normalizedChildBaseWeight child cp σ d
      ((split ({terminal d} : Finset (HashInput child))).symm (on, off))) ≤ cp.threshold := by
  let s : Finset (HashInput child) := {terminal d}
  let g : Outside s := ⟨gamma d.1, by simp [s, gamma, terminal]⟩
  let c : Outside s := ⟨childGamma d.1 d.2.1 d.2.2.1,
    by simp [s, childGamma, terminal]⟩
  let t : Inside s := ⟨terminal d, by simp [s]⟩
  let statement := child.link.statement σ d.1 (off g).1.1 d.2.2.1
  let coin := (off c).2.1
  let density := childResponseDensity child statement d.2.1 coin d.2.2.2
  have hw (on : Inside s → Answer child) :
      normalizedChildBaseWeight child cp σ d ((split s).symm (on, off)) =
      basePrice cp.threshold density * indicator
        (child.instance.layer.verify statement d.2.1 coin d.2.2.2 (on t).2.2) := by
    unfold normalizedChildBaseWeight childBlockStatement childPrefix
    rw [split_outside_eval _ _ _ _ g.property,
      split_outside_eval _ _ _ _ c.property, split_inside_eval _ _ _ _ t.property]
  have heq := congrArg average (funext hw)
  rw [heq]
  rw [average_eval t (fun a : Answer child => basePrice cp.threshold density * indicator
    (child.instance.layer.verify statement d.2.1 coin d.2.2.2 a.2.2))]
  change mean (fun a : Answer child => basePrice cp.threshold density * indicator
    (child.instance.layer.verify statement d.2.1 coin d.2.2.2 a.2.2)) ≤ _
  rw [mean_mul_left]
  have hd : mean (fun a : Answer child => indicator
      (child.instance.layer.verify statement d.2.1 coin d.2.2.2 a.2.2)) = density := by
    simp only [mean_prod, mean_const]
    exact mean_indicator _
  rw [hd]
  exact basePrice_mul_le cp.threshold_nonneg

noncomputable def wholeChildBlockWeight (σ : I.layer.Statement)
    (b : ChildPrefix child) (H : HashInput child → Answer child) : ℚ :=
  let s := childBlockStatement child σ b H
  let a := (H (childGamma b.1 b.2.1 b.2.2)).2.1
  rigidChildBlockWeight child cp s b H +
    indicator (nonrigidException child.instance cp s b.2.1
      (highSystems child.instance cp b.2.1) a)

theorem wholeChildBlockWeight_nonneg (σ : I.layer.Statement)
    (b : ChildPrefix child) (H : HashInput child → Answer child) :
    0 ≤ wholeChildBlockWeight child cp σ b H := by
  exact add_nonneg (rigidChildBlockWeight_nonneg child cp _ b H) (indicator_nonneg _)

/-- Parent context is held outside the complete child footprint. The
remaining local inequality is an actual response-incidence mean, not an
assumption about a prover's adaptive behavior. -/
theorem wholeChildBlockWeight_local_le (σ : I.layer.Statement) (price : ℚ)
    (hmean : ∀ (s : child.instance.layer.Statement) (V : child.instance.layer.Oracle),
      mean (fun a => responseIncidence child.instance cp s V a
          (coveredRigidResponses child.instance cp s V a (fun _ => False)
            (highSystems child.instance cp V)) - cp.threshold +
        indicator (nonrigidException child.instance cp s V (highSystems child.instance cp V) a)) ≤ price)
    (b : ChildPrefix child) (off : Outside (childBlock child b) → Answer child) :
    average (fun on => wholeChildBlockWeight child cp σ b
      ((split (childBlock child b)).symm (on, off))) ≤ price := by
  let g : Outside (childBlock child b) :=
    ⟨gamma b.1, gamma_not_mem_childBlock child b b.1⟩
  let s := child.link.statement σ b.1 (off g).1.1 b.2.2
  let c : Inside (childBlock child b) :=
    ⟨childGamma b.1 b.2.1 b.2.2, childGamma_mem_childBlock child b⟩
  have hs (on : Inside (childBlock child b) → Answer child) :
      childBlockStatement child σ b ((split (childBlock child b)).symm (on, off)) = s := by
    unfold childBlockStatement
    rw [split_outside_eval _ _ _ _ g.property]
  simp only [wholeChildBlockWeight, hs]
  rw [average_add, rigidChildBlockWeight_local_eq]
  have hc : average (fun on => indicator
      (nonrigidException child.instance cp s b.2.1 (highSystems child.instance cp b.2.1)
        (((split (childBlock child b)).symm (on, off)) (childGamma b.1 b.2.1 b.2.2)).2.1)) =
      mean (fun a => indicator (nonrigidException child.instance cp s b.2.1
        (highSystems child.instance cp b.2.1) a)) := by
    have heval (on : Inside (childBlock child b) → Answer child) :
        ((split (childBlock child b)).symm (on, off))
          (childGamma b.1 b.2.1 b.2.2) = on c :=
      split_inside_eval (childBlock child b) on off (childGamma b.1 b.2.1 b.2.2)
        (childGamma_mem_childBlock child b)
    simp_rw [heval]
    rw [average_eval c (fun a : Answer child => indicator
      (nonrigidException child.instance cp s b.2.1 (highSystems child.instance cp b.2.1) a.2.1))]
    change mean (fun a : Answer child => _) = _
    simp only [mean_prod, mean_const]
  rw [hc, ← mean_add]
  exact hmean s b.2.1

variable (p : HahnSystemCertificate I)

private theorem child_target_of_failed_proof (σ : I.layer.Statement)
    (W : I.layer.Oracle) (V : child.instance.layer.Oracle)
    (a : I.layer.Coin) (q : I.layer.Query) (b : child.instance.layer.Coin)
    (R : child.instance.layer.Payload) (t : child.instance.layer.Query)
    (hd : child.link.direct W q)
    (hr : (twoProof child p cp).run σ W (constantMessages child (W,V,q,R)) ((a,q),(b,t)) = none) :
    outputHit (Protocol.ProfileProof.inducedFamily (child := child) σ W a (fun _ => False) q)
      (scanRecoverAt child.instance (child.link.statement σ W a q) V b R) := by
  simp only [twoProof, Protocol.HahnProfileProof.run, Protocol.HahnProfileProof.runTranscript,
    Protocol.chain, Chain.record, constantMessages, Protocol.HahnProfileProof.family] at hr
  cases he : scanRecoverAt child.instance (child.link.statement σ W a q) V b R with
  | none => trivial
  | some g =>
    have hs := scanRecoverAt_valid child.instance (child.link.statement σ W a q) V b R g he
    have hv := (child.verify_iff σ W a q _).mp ⟨hd, hs⟩
    simp only [he] at hr
    exact ⟨hv, by simp only [hr, outputHit]⟩

/-- Outside the parent-query target event, every high child response is
an arithmetic exception. The rigid responses share their excess budget;
the remaining proper systems use the response-free residual event. -/
theorem high_child_rigid_or_nonrigid (σ : I.layer.Statement)
    (W : I.layer.Oracle) (V : child.instance.layer.Oracle) (a : I.layer.Coin)
    (q : I.layer.Query) (b : child.instance.layer.Coin) (u : child.instance.layer.Payload)
    (hh : cp.threshold < childResponseDensity child (child.link.statement σ W a q) V b u)
    (htarget : outputHit
      (Protocol.ProfileProof.inducedFamily (child := child) σ W a (fun _ => False) q)
      (scanRecoverAt child.instance (child.link.statement σ W a q) V b u))
    (hout : b.2 ∉ ReducedSystems.badChallenges
      (LigeroFamily.PolynomialDirect.primaryCode child.instance.domain child.instance.primary_le)
      (Local.Polygero.oracleWords V.ordinary) V.proximityMask)
    (hnq : ¬ queryCapacityRisk child cp σ W V a q) :
    u ∈ coveredRigidResponses child.instance cp (child.link.statement σ W a q) V b
        (fun _ => False) (highSystems child.instance cp V) ∨
      nonrigidException child.instance cp (child.link.statement σ W a q) V
        (highSystems child.instance cp V) b := by
  obtain ⟨d, ha, he⟩ := high_target_response_cases child.instance cp
    (child.link.statement σ W a q) V b u
    (Protocol.ProfileProof.inducedFamily (child := child) σ W a (fun _ => False) q)
    hh htarget hout
  have hd : d ∈ highSystems child.instance cp V := mem_filter.mpr ⟨mem_univ _,
    hh.trans_le (assigned_response_fraction_le child.instance _ V b u d ha)⟩
  have hex : b ∈ systemExceptions cp.positive_degree child.instance.layout
      (child.link.statement σ W a q) d := by
    rcases he with ⟨_, he⟩ | ⟨hf, ht | he⟩
    · exact he
    · exact (hnq ⟨d, hd, ht⟩).elim
    · exact he
  by_cases hr : RigidSystem child.instance cp V d
  · left
    exact mem_filter.mpr ⟨mem_univ _, hh, d, hd, hr, ha, Or.inr hex⟩
  · exact Or.inr ⟨d, hd, hr, hex⟩

/-- Unit coverage on the actual transcript, including proper systems and
cached terminal hashes. No response-uniqueness assumption is supplied by
the caller. -/
theorem wholeChildBlock_pay (σ : I.layer.Statement) (d : Proof child)
    (H : HashInput child → Answer child)
    (hf : failure child p cp σ (fun _ => False) H d)
    (hnq : ¬ queryCapacityEvent child cp σ (query d.1 d.2.1) H) :
    1 ≤ wholeChildBlockWeight child cp σ (childPrefix child d) H +
      normalizedChildBaseWeight child cp σ d H := by
  obtain ⟨ha, hr⟩ := (failure_empty_iff child p cp σ H d).mp hf
  obtain ⟨hq, hd, hv⟩ := (accepts_iff child σ H d).mp ha
  let a := (H (gamma d.1)).1.1
  let b := (H (childGamma d.1 d.2.1 d.2.2.1)).2.1
  let s := child.link.statement σ d.1 a d.2.2.1
  let r := childResponseDensity child s d.2.1 b d.2.2.2
  have hbase : normalizedChildBaseWeight child cp σ d H = basePrice cp.threshold r := by
    simp only [normalizedChildBaseWeight, childBlockStatement, childPrefix]
    change basePrice cp.threshold r * indicator
      (child.instance.layer.verify s d.2.1 b d.2.2.2 (H (terminal d)).2.2) = _
    rw [show indicator (child.instance.layer.verify s d.2.1 b d.2.2.2
      (H (terminal d)).2.2) = 1 by exact if_pos hv, mul_one]
  rw [hbase]
  by_cases hl : r ≤ cp.threshold
  · have hb : basePrice cp.threshold r = 1 := if_pos hl
    rw [hb]
    exact le_add_of_nonneg_left (wholeChildBlockWeight_nonneg child cp σ _ H)
  have hhigh : cp.threshold < r := lt_of_not_ge hl
  have htarget := child_target_of_failed_proof child cp p σ d.1 d.2.1 a d.2.2.1 b
    d.2.2.2 (H (terminal d)).2.2 hd (by simpa only [proofCoins, hq] using hr)
  have hqout : ¬ queryCapacityRisk child cp σ d.1 d.2.1 a d.2.2.1 := by
    change ¬ queryCapacityRisk child cp σ d.1 d.2.1 a
      (H (query d.1 d.2.1)).1.2 at hnq
    rwa [hq] at hnq
  by_cases hb : b.2 ∈ ReducedSystems.badChallenges
      (LigeroFamily.PolynomialDirect.primaryCode child.instance.domain child.instance.primary_le)
      (Local.Polygero.oracleWords d.2.1.ordinary) d.2.1.proximityMask
  · have hw : 1-cp.threshold ≤ wholeChildBlockWeight child cp σ (childPrefix child d) H := by
      dsimp only [wholeChildBlockWeight, childPrefix, childBlockStatement, rigidChildBlockWeight]
      rw [if_pos hb]
      exact le_add_of_nonneg_right (indicator_nonneg _)
    have hp := basePrice_ge_threshold cp.threshold_nonneg cp.threshold_lt_one.le
      (childResponseDensity_le_one child s d.2.1 b d.2.2.2)
    linarith
  obtain hu | he := high_child_rigid_or_nonrigid child cp σ d.1 d.2.1 a d.2.2.1 b
    d.2.2.2 hhigh htarget hb hqout
  · have hw : 1-basePrice cp.threshold r ≤ wholeChildBlockWeight child cp σ (childPrefix child d) H := by
      dsimp only [wholeChildBlockWeight, childPrefix, childBlockStatement, rigidChildBlockWeight]
      rw [if_neg hb]
      apply le_trans _ (le_add_of_nonneg_right (indicator_nonneg _))
      have hs := single_le_sum
        (f := fun u => (1-basePrice cp.threshold (childResponseDensity child s d.2.1 b u)) *
          indicator (child.instance.layer.verify s d.2.1 b u
            (H (terminal (d.1,d.2.1,d.2.2.1,u))).2.2))
        (fun u _ => mul_nonneg (sub_nonneg.mpr (basePrice_le_one cp.threshold_nonneg))
          (indicator_nonneg _)) hu
      simpa only [show indicator (child.instance.layer.verify s d.2.1 b d.2.2.2
        (H (terminal d)).2.2) = 1 from if_pos hv, mul_one] using hs
    linarith
  · have hw : 1 ≤ wholeChildBlockWeight child cp σ (childPrefix child d) H := by
      dsimp only [wholeChildBlockWeight]
      have he' : indicator (nonrigidException child.instance cp s d.2.1
        (highSystems child.instance cp d.2.1) b) = 1 := if_pos he
      change 1 ≤ rigidChildBlockWeight child cp s (childPrefix child d) H +
        indicator (nonrigidException child.instance cp s d.2.1
          (highSystems child.instance cp d.2.1) b)
      rw [he']
      exact le_add_of_nonneg_left (rigidChildBlockWeight_nonneg child cp s _ H)
    exact hw.trans (le_add_of_nonneg_right (basePrice_nonneg cp.threshold_nonneg))

def childBlockFailure (σ : I.layer.Statement) (d : Proof child)
    (H : HashInput child → Answer child) : Prop :=
  failure child p cp σ (fun _ => False) H d ∧
    ¬ queryCapacityEvent child cp σ (query d.1 d.2.1) H

/-- A complete actual terminal-child certificate from a proved local
incidence budget. The mean premise contains no transcript/adversary data. -/
theorem child_block_oracle_sound_of_mean (σ : I.layer.Statement) (price : ℚ)
    (hp : 0 ≤ price)
    (hmean : ∀ (s : child.instance.layer.Statement) (V : child.instance.layer.Oracle),
      mean (fun a => responseIncidence child.instance cp s V a
          (coveredRigidResponses child.instance cp s V a (fun _ => False)
            (highSystems child.instance cp V)) - cp.threshold +
        indicator (nonrigidException child.instance cp s V (highSystems child.instance cp V) a)) ≤ price) :
    OracleSound (terminalBlockDomain child) (childBlockFailure child cp p σ)
      ⟨price+cp.threshold, price+cp.threshold,
        add_nonneg hp cp.threshold_nonneg, add_nonneg hp cp.threshold_nonneg⟩ := by
  apply terminal_block_oracle_sound child (wholeChildBlockWeight child cp σ)
    (normalizedChildBaseWeight child cp σ) price cp.threshold hp cp.threshold_nonneg
    (wholeChildBlockWeight_nonneg child cp σ) (normalizedChildBaseWeight_nonneg child cp σ)
    (wholeChildBlockWeight_local_le child cp σ price hmean)
    (normalizedChildBaseWeight_local child cp σ)
  intro d H h
  exact wholeChildBlock_pay child cp p σ d H h.1 h.2

theorem failure_query_or_child_block (σ : I.layer.Statement) (d : Proof child)
    (H : HashInput child → Answer child)
    (hf : failure child p cp σ (fun _ => False) H d) :
    queryCapacityEvent child cp σ (query d.1 d.2.1) H ∨ childBlockFailure child cp p σ d H := by
  by_cases hq : queryCapacityEvent child cp σ (query d.1 d.2.1) H
  · exact Or.inl hq
  · exact Or.inr ⟨hf, hq⟩

/-- The whole child block pays only two field units for arithmetic
exceptions at the fixed 81/80 geometry. The single baseline is retained
with its exact rank cross term. -/
theorem child_block_oracle_sound_fixed (hcp : cp.listBound < Nat.card F)
    (hn : child.instance.n = 8192) (hk : child.instance.r + child.instance.w = 512)
    (hs : child.instance.s = 64) (ha : cp.columnCutoff = 2714)
    (σ : I.layer.Statement) :
    OracleSound (terminalBlockDomain child) (childBlockFailure child cp p σ)
      (Rate.diagonal ((1-cp.threshold)*cp.toProfileParameters.rankError +
        2/(Nat.card F : ℚ) + cp.threshold) (by
          exact add_nonneg (add_nonneg (mul_nonneg
            (sub_nonneg.mpr cp.threshold_lt_one.le) (by unfold ProfileParameters.rankError; positivity))
            (by positivity)) cp.threshold_nonneg)) := by
  apply child_block_oracle_sound_of_mean child cp p σ
    ((1-cp.threshold)*cp.toProfileParameters.rankError + 2/(Nat.card F : ℚ))
    (add_nonneg (mul_nonneg (sub_nonneg.mpr cp.threshold_lt_one.le)
      (by unfold ProfileParameters.rankError; positivity)) (by positivity))
  intro s V
  let T := highSystems child.instance cp V
  have hT : T.card ≤ Nat.card F := (highSystems_card_le child.instance cp hcp V).trans hcp.le
  have hpmean := mean_mono (fun a =>
    responseIncidence_sub_threshold_add_nonrigid_le_rigidBlockCharge child.instance cp
      s V a (fun _ => False) (coveredRigidResponses child.instance cp s V a (fun _ => False) T)
      T (fun _ => coveredRigidResponses_cover child.instance cp s V a (fun _ => False) T))
  have hc := fixed_rigidBlockCharge_mean_le (Z := Unit) child.instance cp
    (fun _ => s) V (fun _ _ => False) T hT 0 (by norm_num)
    (by intro g; simp [indicator]) hn hk hs ha
  simp only [mean_const, add_zero] at hc
  exact hpmean.trans hc

end RecursivePolygero.FiatShamir.TwoLevel
