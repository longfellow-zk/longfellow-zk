import polygero.Recursion.FSInputs
import polygero.Local.ListSafety
import Bcs.SingletonCharging

/-! A complete four-event route to two-level FS soundness. Global
high-capacity list bounds replace incoming-envelope reuse by a uniform
parent threshold, with an explicit list-size cost. -/

namespace RecursivePolygero.FiatShamir.TwoLevel

open Finset Counting ProfileAnalysis Bcs.TotalOracle.Footprint Merkle.RandomOracle
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)
variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

private theorem mean_exists_mem_le {A D : Type} [Fintype A] [Fintype D]
    (T : Finset D) (P : A → D → Prop) (epsilon : ℚ)
    (h : ∀ d ∈ T, mean (fun a => indicator (P a d)) ≤ epsilon) :
    mean (fun a => indicator (∃ d ∈ T, P a d)) ≤ T.card * epsilon := by
  have hp (a : A) : indicator (∃ d ∈ T, P a d) ≤ ∑ d ∈ T, indicator (P a d) := by
    by_cases he : ∃ d ∈ T, P a d
    · obtain ⟨d, hd, he'⟩ := he
      have hs := single_le_sum (fun d (_ : d ∈ T) => indicator_nonneg (P a d)) hd
      simpa only [indicator, if_pos he', if_pos (show ∃ d ∈ T, P a d from ⟨d, hd, he'⟩)] using hs
    · simpa only [indicator, if_neg he] using sum_nonneg (s := T) (fun d _ => indicator_nonneg (P a d))
  calc
    _ ≤ _ := mean_mono hp
    _ = _ := SystemException.mean_finset_sum T _
    _ ≤ ∑ _d ∈ T, epsilon := sum_le_sum h
    _ = _ := by simp

noncomputable def queryRisk (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (V : child.instance.layer.Oracle) (a : I.layer.Coin) (q : I.layer.Query) : Prop :=
  ¬ listBad I p sigma W a ∧ ∃ d ∈ highSystems child.instance cp V,
    systemTarget child.instance cp.positive_degree V
      (Protocol.ProfileProof.inducedFamily (child := child) sigma W a (fun _ => False) q) d

theorem queryRisk_mean_le (hsmall : cp.listBound < Nat.card F)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (V : child.instance.layer.Oracle)
    (a : I.layer.Coin) :
    mean (fun q => indicator (queryRisk child p cp sigma W V a q)) ≤ cp.listBound * p.threshold := by
  by_cases hb : listBad I p sigma W a
  · simp only [queryRisk, hb, not_true_eq_false, false_and, indicator, if_false, mean_const]
    exact mul_nonneg (Nat.cast_nonneg _) p.threshold_nonneg
  · have he := envelope_le_threshold_of_not_listBad I p sigma W a hb
    have hg (g : (tupleCounts child.instance).Index) :=
      (induced_target_frequency_le child p sigma W (fun _ => False) a g).trans he
    simp only [queryRisk, hb, not_false_eq_true, true_and]
    have h := mean_exists_mem_le (highSystems child.instance cp V)
      (fun q d => systemTarget child.instance cp.positive_degree V
        (Protocol.ProfileProof.inducedFamily (child := child) sigma W a (fun _ => False) q) d)
      p.threshold (by
        intro d _
        by_cases hf : Local.Affine.consistent
            (LigeroFamily.PolynomialDirect.primaryCode child.instance.domain child.instance.primary_le)
            (Local.Polygero.oracleWords V.ordinary) V.proximityMask d.1 = univ
        · simpa only [systemTarget, exists_prop_of_true hf] using
            hg (systemLabel child.instance cp.positive_degree V d hf)
        · have hn (q : I.layer.Query) : ¬ systemTarget child.instance cp.positive_degree V
              (Protocol.ProfileProof.inducedFamily (child := child) sigma W a (fun _ => False) q) d :=
              fun ⟨h, _⟩ => hf h
          simpa only [indicator, if_neg (hn _), mean_const] using p.threshold_nonneg)
    exact h.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast highSystems_card_le child.instance cp hsmall V) p.threshold_nonneg)

noncomputable def terminalRisk (sigma : child.instance.layer.Statement)
    (V : child.instance.layer.Oracle) (b : child.instance.layer.Coin)
    (R : child.instance.layer.Payload) (t : child.instance.layer.Query) : Prop :=
  (responseCount child.instance.layer sigma V b R : ℚ) /
    Fintype.card child.instance.layer.Query ≤ cp.threshold ∧
  child.instance.layer.verify sigma V b R t

theorem terminalRisk_mean_le (sigma : child.instance.layer.Statement)
    (V : child.instance.layer.Oracle) (b : child.instance.layer.Coin)
    (R : child.instance.layer.Payload) :
    mean (fun t => indicator (terminalRisk child cp sigma V b R t)) ≤ cp.threshold := by
  by_cases h : (responseCount child.instance.layer sigma V b R : ℚ) /
      Fintype.card child.instance.layer.Query ≤ cp.threshold
  · simp only [terminalRisk, h, true_and, mean_indicator]
    exact h
  · simpa only [terminalRisk, h, false_and, indicator, if_false, mean_const] using cp.threshold_nonneg

def rootEvent (sigma : I.layer.Statement) : HashInput child → (HashInput child → Answer child) → Prop
  | .inl W, H => listBad I p sigma W (H (gamma W)).1.1
  | _, _ => False

noncomputable def queryEvent (sigma : I.layer.Statement) :
    HashInput child → (HashInput child → Answer child) → Prop
  | .inr (.inl (W, V)), H => queryRisk child p cp sigma W V
      (H (gamma W)).1.1 (H (query W V)).1.2
  | _, _ => False

def childEvent (sigma : I.layer.Statement) : HashInput child → (HashInput child → Answer child) → Prop
  | .inr (.inr (.inl (W, V, q))), H => listBad child.instance cp
      (child.link.statement sigma W (H (gamma W)).1.1 q) V (H (childGamma W V q)).2.1
  | _, _ => False

noncomputable def terminalEvent (sigma : I.layer.Statement) :
    HashInput child → (HashInput child → Answer child) → Prop
  | .inr (.inr (.inr (W, V, q, R))), H => terminalRisk child cp
      (child.link.statement sigma W (H (gamma W)).1.1 q) V
      (H (childGamma W V q)).2.1 R (H (terminal (W, V, q, R))).2.2
  | _, _ => False

theorem rootEvent_local (hsmall : p.listBound < Nat.card F) (sigma : I.layer.Statement)
    (x : HashInput child) (H : HashInput child → Answer child) :
    average (fun c => indicator (rootEvent child p sigma x (Function.update H x c))) ≤ listError I p := by
  rcases x with W | (wv | (wvq | d))
  · simp only [rootEvent, gamma, Function.update_self]
    change mean (fun c : Answer child => indicator (listBad I p sigma W c.1.1)) ≤ _
    simp only [mean_prod, mean_const]
    exact listBad_mean_le I p hsmall sigma W
  all_goals simpa only [rootEvent, indicator, if_false, average_const] using listError_nonneg I p

theorem queryEvent_local (hsmall : cp.listBound < Nat.card F) (sigma : I.layer.Statement)
    (x : HashInput child) (H : HashInput child → Answer child) :
    average (fun c => indicator (queryEvent child p cp sigma x (Function.update H x c))) ≤
      cp.listBound * p.threshold := by
  rcases x with W | (⟨W,V⟩ | (wvq | d))
  · simpa [queryEvent, indicator] using mul_nonneg (Nat.cast_nonneg cp.listBound) p.threshold_nonneg
  · simp only [queryEvent, gamma, query, Function.update_self, Function.update_of_ne (by simp :
      (Sum.inl W : HashInput child) ≠ Sum.inr (Sum.inl (W,V)))]
    change mean (fun c : Answer child => indicator
      (queryRisk child p cp sigma W V (H (.inl W)).1.1 c.1.2)) ≤ _
    simp only [mean_prod, mean_const]
    exact queryRisk_mean_le child p cp hsmall sigma W V _
  all_goals simpa [queryEvent, indicator] using mul_nonneg (Nat.cast_nonneg cp.listBound) p.threshold_nonneg

theorem childEvent_local (hsmall : cp.listBound < Nat.card F) (sigma : I.layer.Statement)
    (x : HashInput child) (H : HashInput child → Answer child) :
    average (fun c => indicator (childEvent child cp sigma x (Function.update H x c))) ≤
      listError child.instance cp := by
  rcases x with W | (wv | (⟨W,V,q⟩ | d))
  · simpa [childEvent, indicator] using listError_nonneg child.instance cp
  · simpa [childEvent, indicator] using listError_nonneg child.instance cp
  · simp only [childEvent, gamma, childGamma, Function.update_self,
      Function.update_of_ne (by simp : (Sum.inl W : HashInput child) ≠ Sum.inr (Sum.inr (Sum.inl (W,V,q))))]
    change mean (fun c : Answer child => indicator (listBad child.instance cp
      (child.link.statement sigma W (H (.inl W)).1.1 q) V c.2.1)) ≤ _
    simp only [mean_prod, mean_const]
    exact listBad_mean_le child.instance cp hsmall _ V
  · simpa [childEvent, indicator] using listError_nonneg child.instance cp

theorem terminalEvent_local (sigma : I.layer.Statement)
    (x : HashInput child) (H : HashInput child → Answer child) :
    average (fun c => indicator (terminalEvent child cp sigma x (Function.update H x c))) ≤ cp.threshold := by
  rcases x with W | (wv | (wvq | ⟨W,V,q,R⟩))
  · simpa [terminalEvent, indicator] using cp.threshold_nonneg
  · simpa [terminalEvent, indicator] using cp.threshold_nonneg
  · simpa [terminalEvent, indicator] using cp.threshold_nonneg
  · simp only [terminalEvent, gamma, childGamma, terminal, Function.update_self,
      Function.update_of_ne (by simp : (Sum.inl W : HashInput child) ≠ Sum.inr (Sum.inr (Sum.inr (W,V,q,R)))),
      Function.update_of_ne (by simp : (Sum.inr (Sum.inr (Sum.inl (W,V,q))) : HashInput child) ≠
        Sum.inr (Sum.inr (Sum.inr (W,V,q,R))))]
    change mean (fun c : Answer child => indicator (terminalRisk child cp
      (child.link.statement sigma W (H (.inl W)).1.1 q) V
      (H (.inr (.inr (.inl (W,V,q))))).2.1 R c.2.2)) ≤ _
    simp only [mean_prod, mean_const]
    exact terminalRisk_mean_le child cp _ V _ R

private theorem child_target_of_failure (sigma : I.layer.Statement)
    (W : I.layer.Oracle) (V : child.instance.layer.Oracle)
    (a : I.layer.Coin) (q : I.layer.Query) (b : child.instance.layer.Coin)
    (R : child.instance.layer.Payload) (t : child.instance.layer.Query)
    (hd : child.link.direct W q)
    (hr : (twoProof child p cp).run sigma W (constantMessages child (W,V,q,R)) ((a,q),(b,t)) = none) :
    outputHit (Protocol.ProfileProof.inducedFamily (child := child) sigma W a (fun _ => False) q)
      (scanRecoverAt child.instance (child.link.statement sigma W a q) V b R) := by
  simp only [twoProof, Protocol.HahnProfileProof.run, Protocol.HahnProfileProof.runTranscript,
    Protocol.chain, Chain.record, constantMessages, Protocol.HahnProfileProof.family] at hr
  cases he : scanRecoverAt child.instance (child.link.statement sigma W a q) V b R with
  | none => trivial
  | some g =>
    have hs := scanRecoverAt_valid child.instance (child.link.statement sigma W a q) V b R g he
    have hv := (child.verify_iff sigma W a q _).mp ⟨hd, hs⟩
    simp only [he] at hr
    exact ⟨hv, by simp only [hr, outputHit]⟩

/-- Exhaustive coverage for the actual typed transcript and extractor.
Proper systems are already included in the two list-exception events. -/
theorem failure_list_cover (sigma : I.layer.Statement)
    (H : HashInput child → Answer child) (d : Proof child)
    (hf : failure child p cp sigma (fun _ => False) H d) :
    rootEvent child p sigma (gamma d.1) H ∨
    queryEvent child p cp sigma (query d.1 d.2.1) H ∨
    childEvent child cp sigma (childGamma d.1 d.2.1 d.2.2.1) H ∨
    terminalEvent child cp sigma (terminal d) H := by
  obtain ⟨ha, hr⟩ := (failure_empty_iff child p cp sigma H d).mp hf
  obtain ⟨hq, hd, hv⟩ := (accepts_iff child sigma H d).mp ha
  by_cases hb : listBad I p sigma d.1 (H (gamma d.1)).1.1
  · exact Or.inl hb
  right
  have ht := child_target_of_failure child p cp sigma d.1 d.2.1 (H (gamma d.1)).1.1
    d.2.2.1 (H (childGamma d.1 d.2.1 d.2.2.1)).2.1 d.2.2.2 (H (terminal d)).2.2 hd
    (by simpa only [proofCoins, hq] using hr)
  by_cases hl : (responseCount child.instance.layer
      (child.link.statement sigma d.1 (H (gamma d.1)).1.1 d.2.2.1) d.2.1
      (H (childGamma d.1 d.2.1 d.2.2.1)).2.1 d.2.2.2 : ℚ) /
        Fintype.card child.instance.layer.Query ≤ cp.threshold
  · exact Or.inr (Or.inr ⟨hl, hv⟩)
  have hc := high_target_list_cover child.instance cp _ d.2.1 _ d.2.2.2 _ (lt_of_not_ge hl) ht
  rcases hc with hc | hc
  · exact Or.inr (Or.inl hc)
  · left
    change queryRisk child p cp sigma d.1 d.2.1 (H (gamma d.1)).1.1 (H (query d.1 d.2.1)).1.2
    rw [hq]
    exact ⟨hb, hc⟩

noncomputable def listBudget : ℚ :=
  listError I p + cp.listBound * p.threshold + listError child.instance cp + cp.threshold

/-- Complete ideal-ROM bound, with no assumptions about a prover's query
order, response rigidity, child commitment count, or residual coverage.
The two list sizes are genuine global bounds because they are below `|F|`.
Each event uses its own appended lookup, so no verifier freshness is assumed. -/
theorem fs_list_bound (hp : p.listBound < Nat.card F) (hcp : cp.listBound < Nat.card F)
    (sigma : I.layer.Statement) {N : ℕ}
    (tree : Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H =>
      failure child p cp sigma (fun _ => False) H (tree.run H).1) ≤
      (N + 1) * listBudget child p cp := by
  let events : Fin 4 → (HashInput child → Answer child) → Prop := ![
    fun H => rootEvent child p sigma (gamma (tree.run H).1.1) H,
    fun H => queryEvent child p cp sigma (query (tree.run H).1.1 (tree.run H).1.2.1) H,
    fun H => childEvent child cp sigma
      (childGamma (tree.run H).1.1 (tree.run H).1.2.1 (tree.run H).1.2.2.1) H,
    fun H => terminalEvent child cp sigma (terminal (tree.run H).1) H]
  have hu := Bcs.FiniteProbability.density_union_le
    (fun H => failure child p cp sigma (fun _ => False) H (tree.run H).1) events (by
      intro H hf
      rcases failure_list_cover child p cp sigma H (tree.run H).1 hf with h | h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩)
  have h0 := selected_singleton_event_le tree (fun d => gamma d.1) (rootEvent child p sigma)
    (listError I p) (listError_nonneg I p)
    (by intro x H; exact rootEvent_local child p hp sigma x H)
  have h1 := selected_singleton_event_le tree (fun d => query d.1 d.2.1) (queryEvent child p cp sigma)
    (cp.listBound * p.threshold) (mul_nonneg (Nat.cast_nonneg _) p.threshold_nonneg)
    (by intro x H; exact queryEvent_local child p cp hcp sigma x H)
  have h2 := selected_singleton_event_le tree (fun d => childGamma d.1 d.2.1 d.2.2.1)
    (childEvent child cp sigma) (listError child.instance cp) (listError_nonneg child.instance cp)
    (by intro x H; exact childEvent_local child cp hcp sigma x H)
  have h3 := selected_singleton_event_le tree terminal (terminalEvent child cp sigma)
    cp.threshold cp.threshold_nonneg (by intro x H; exact terminalEvent_local child cp sigma x H)
  simp only [events, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ] at hu
  unfold listBudget
  linarith

private theorem threshold_field_cost_le (theta c epsilon : ℚ)
    (ht : 0 ≤ theta) (hc : 0 ≤ c) (ht1 : theta ≤ 1)
    (he : epsilon = theta + (1-theta)*c) (he1 : epsilon ≤ 1/4) :
    theta + c ≤ (4/3) * epsilon := by
  have htc := mul_nonneg (sub_nonneg.mpr ht1) hc
  have ht4 : theta ≤ 1/4 := by linarith
  have hm := mul_nonneg (show 0 ≤ 1-4*theta by linarith) hc
  nlinarith

omit [Fintype F] [DecidableEq F] in
/-- A uniform list bound `L` loses at most a factor `2L` when each local
error is at most 1/4. Thus `L ≤ 4` gives three bits and `L ≤ 8` four bits.
This comparison uses the original affine interactive error, including its
cross term, rather than replacing it by an unnamed error parameter. -/
theorem listBudget_le_two_mul (L : ℕ) (hL : 1 ≤ L)
    (hpL : p.listBound ≤ L) (hcpL : cp.listBound ≤ L)
    (hp : p.error ≤ 1/4) (hcp : cp.error ≤ 1/4) :
    listBudget child p cp ≤ 2 * L * twoError p.error cp.error := by
  let u : ℚ := 1 / Nat.card F
  let m0 := p.toProfileParameters.rankError
  let m1 := cp.toProfileParameters.rankError
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hm0 : 0 ≤ m0 := by dsimp [m0, ProfileParameters.rankError]; positivity
  have hm1 : 0 ≤ m1 := by dsimp [m1, ProfileParameters.rankError]; positivity
  have hLn : (1 : ℚ) ≤ L := by exact_mod_cast hL
  have hL0 : (p.listBound : ℚ) ≤ L := by exact_mod_cast hpL
  have hL1 : (cp.listBound : ℚ) ≤ L := by exact_mod_cast hcpL
  have hc0 := threshold_field_cost_le p.threshold (m0+u) p.error p.threshold_nonneg
    (add_nonneg hm0 hu) p.threshold_lt_one.le rfl hp
  have hc1 := threshold_field_cost_le cp.threshold (m1+u) cp.error cp.threshold_nonneg
    (add_nonneg hm1 hu) cp.threshold_lt_one.le rfl hcp
  have hB : listBudget child p cp ≤ L * (p.threshold + (m0+u) + cp.threshold + (m1+u)) := by
    have h0 := mul_nonneg (sub_nonneg.mpr hLn) hm0
    have h1 := mul_nonneg (sub_nonneg.mpr hLn) hm1
    have h2 := mul_nonneg (sub_nonneg.mpr hL0) hu
    have h3 := mul_nonneg (sub_nonneg.mpr hL1) hu
    have h4 := mul_nonneg (sub_nonneg.mpr hL1) p.threshold_nonneg
    have h5 := mul_nonneg (sub_nonneg.mpr hLn) cp.threshold_nonneg
    change m0 + p.listBound / (Nat.card F : ℚ) + cp.listBound * p.threshold +
      (m1 + cp.listBound / (Nat.card F : ℚ)) + cp.threshold ≤ _
    simp only [div_eq_mul_inv] at ⊢
    dsimp only [u] at h2 h3
    simp only [one_div] at h2 h3
    dsimp only [u]
    simp only [one_div]
    nlinarith
  have hs : p.error + cp.error ≤ (4/3) * twoError p.error cp.error := by
    have hh := mul_nonneg p.error_nonneg (sub_nonneg.mpr hcp)
    unfold twoError
    nlinarith [p.error_nonneg, cp.error_nonneg]
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hc0 hc1) (Nat.cast_nonneg L : (0 : ℚ) ≤ L)
  have hscaled := mul_le_mul_of_nonneg_left hs (show (0 : ℚ) ≤ (4/3) * L by positivity)
  have hrho : 0 ≤ twoError p.error cp.error := by
    unfold twoError
    exact add_nonneg p.error_nonneg (mul_nonneg (sub_nonneg.mpr p.error_lt_one.le) cp.error_nonneg)
  have hnonneg := mul_nonneg (Nat.cast_nonneg L : (0 : ℚ) ≤ L) hrho
  nlinarith

theorem fs_list_loss_factor (hp : p.listBound < Nat.card F) (hcp : cp.listBound < Nat.card F)
    (L : ℕ) (hL : 1 ≤ L) (hpL : p.listBound ≤ L) (hcpL : cp.listBound ≤ L)
    (he0 : p.error ≤ 1/4) (he1 : cp.error ≤ 1/4)
    (sigma : I.layer.Statement) {N : ℕ}
    (tree : Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H =>
      failure child p cp sigma (fun _ => False) H (tree.run H).1) ≤
      (N + 1) * (2 * L * twoError p.error cp.error) :=
  (fs_list_bound child p cp hp hcp sigma tree).trans
    (mul_le_mul_of_nonneg_left (listBudget_le_two_mul child p cp L hL hpL hcpL he0 he1) (by positivity))

end RecursivePolygero.FiatShamir.TwoLevel
