import polygero.Recursion.FSWholeBlock
import Bcs.StoppedCompletion

/-! The parent/query verifier completes its unread coordinates jointly.
This improves the intercept without restricting adaptive child commitments
or changing the stopped-price spectrum premise. -/
set_option maxHeartbeats 1500000

namespace RecursivePolygero.FiatShamir.TwoLevel
open Finset Counting ProfileAnalysis Local Local.Polygero Bcs.AffineBlock Bcs.TotalOracle.Footprint
open Bcs.StoppedPotential
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)
variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

/-- With a fixed submitted proof, the four typed hash roles are fresh
independent coordinates. The ordinary IOP bound applies without grinding. -/
theorem fixed_failure_le_iop (σ : I.layer.Statement) (d : Proof child) :
    Bcs.FiniteProbability.density (fun H => failure child p cp σ (fun _ => False) H d) ≤
      twoError p.error cp.error := by
  have he (H : HashInput child → Answer child) :
      (if failure child p cp σ (fun _ => False) H d then (1 : ℚ) else 0) =
        weight child p cp σ (fun _ => False) d H := by
    by_cases hq : (H (query d.1 d.2.1)).1.2 = d.2.2.1
    · simp [weight, failure, accepts, hq, bad, indicator]
    · simp [weight, failure, accepts, hq]
  rw [density_eq_average]
  simp_rw [he]
  rw [average_split (support d)]
  simp_rw [local_average child p cp σ (fun _ => False) d]
  rw [average_const]
  exact (single_le_sum (fun q (_ : q ∈ univ) => budget_nonneg child p cp σ (fun _ => False)
    (d.1,d.2.1,q,d.2.2.2)) (mem_univ d.2.2.1)).trans
      (sum_budget_query_le child p cp σ d.1 d.2.1 d.2.2.2)

/-- A fresh pair's capacity mean retains the child list baseline, but
uses the capacity-weighted parent exception mean instead of a list union. -/
theorem queryCapacity_mean_le (hsmall : p.listBound < Nat.card F)
    (σ : I.layer.Statement) (W : I.layer.Oracle) :
    mean (queryCapacity child p cp σ W) ≤
      p.toProfileParameters.rankError + cp.listBound*p.threshold +
        (1-p.threshold+p.listBound*p.threshold)/Nat.card F := by
  let bad := fun a : I.layer.Coin => a.2 ∈ ReducedSystems.badChallenges
    (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask
  have hp (a : I.layer.Coin) : queryCapacity child p cp σ W a ≤
      indicator (bad a) + cp.listBound*p.threshold + weightedExceptions I p σ W a := by
    have hw : 0 ≤ weightedExceptions I p σ W a :=
      sum_nonneg fun d _ => mul_nonneg (by unfold systemCap; positivity) (indicator_nonneg _)
    have hb : 0 ≤ (cp.listBound : ℚ)*p.threshold := mul_nonneg (Nat.cast_nonneg _) p.threshold_nonneg
    change (if bad a then 1 else _) ≤ _
    by_cases h : bad a
    · simp only [indicator, if_pos h]
      linarith
    · simp only [indicator, if_neg h, zero_add]
      rfl
  calc
    _ ≤ _ := mean_mono hp
    _ = mean (fun a => indicator (bad a)) + cp.listBound*p.threshold +
        mean (weightedExceptions I p σ W) := by rw [mean_add, mean_add, mean_const]
    _ ≤ _ := add_le_add (add_le_add (rank_bad_mean I p.toProfileParameters W) (le_refl _))
      (weightedExceptions_mean_le I p hsmall σ W)

/-- Actual local-domain diagonal ABS for the first two hash roles. -/
theorem query_joint_oracle_sound (hcp : cp.listBound < Nat.card F)
    (σ : I.layer.Statement) (rate : ℚ) (hr : 0 ≤ rate)
    (hroot : ∀ W : I.layer.Oracle,
      mean (fun a => repeatPrice rate (queryCapacity child p cp σ W a)) ≤ rate)
    (hmean : ∀ W : I.layer.Oracle, mean (queryCapacity child p cp σ W) ≤ rate) :
    OracleSound (queryBlockDomain child)
      (fun d : Proof child => queryCapacityEvent child cp σ (query d.1 d.2.1))
      (Rate.diagonal rate hr) := by
  have hraw := Bcs.StoppedCharges.oracle_sound_joint (queryEmbedding child) (queryBlockDomain child)
    (queryEmbedding_mem_domain child)
    (fun W (c : Answer child) => queryCapacity child p cp σ W c.1.1)
    (fun W V a b => queryCapacityRisk child cp σ W V a.1.1 b.1.2)
    rate hr (fun W a => queryCapacity_nonneg child p cp σ W a.1.1) ?_ ?_ ?_
  · intro N tree
    have h := hraw N (tree.map (fun d : Proof child => (d.1, d.2.1)))
    refine ⟨queryCost_nonneg _ tree, ?_⟩
    have hb := h.bound
    have hcost : queryCost (queryBlockDomain child) (tree.map (fun d : Proof child => (d.1,d.2.1))) =
        queryCost (queryBlockDomain child) tree := by
      clear h hb
      funext H
      induction tree with
      | done => rfl
      | query q next ih => simp only [Merkle.RandomOracle.Tree.map, queryCost, ih]
    rw [hcost] at hb
    simp only [Merkle.RandomOracle.Tree.run_map] at hb
    change (Bcs.FiniteProbability.density fun H => queryCapacityRisk child cp σ
      (tree.run H).1.1 (tree.run H).1.2.1 (H (gamma (tree.run H).1.1)).1.1
      (H (query (tree.run H).1.1 (tree.run H).1.2.1)).1.2) ≤
        rate + rate * average (queryCost (queryBlockDomain child) tree) at hb
    exact hb
  · intro W
    change mean (fun c : Answer child => repeatPrice rate (queryCapacity child p cp σ W c.1.1)) ≤ rate
    simpa only [mean_prod, mean_const] using hroot W
  · intro W V a
    change mean (fun b : Answer child => Bcs.StoppedCharges.indicator
      (queryCapacityRisk child cp σ W V a.1.1 b.1.2)) ≤ _
    simp only [mean_prod, mean_const]
    exact queryCapacityRisk_mean_le child p cp hcp σ W V a.1.1
  · intro W V
    change mean (fun a : Answer child => mean (fun b : Answer child =>
      indicator (queryCapacityRisk child cp σ W V a.1.1 b.1.2))) ≤ rate
    simp only [mean_prod, mean_const]
    exact (mean_mono (queryCapacityRisk_mean_le child p cp hcp σ W V)).trans (hmean W)

def jointBlockRates (rho tau : ℚ) (hrho : 0 ≤ rho) (htau : 0 ≤ tau) : Fin 2 → Rate :=
  ![Rate.diagonal rho hrho, Rate.diagonal tau htau]

/-- The two local diagonal blocks compose with intercept rho+tau and
the larger query rate. Their failures need not be independent. -/
theorem joint_whole_block_oracle_sound (σ : I.layer.Statement)
    (rho tau : ℚ) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hparent : OracleSound (queryBlockDomain child)
      (fun d : Proof child => queryCapacityEvent child cp σ (query d.1 d.2.1))
      (Rate.diagonal rho hrho))
    (hchild : OracleSound (roleDomain child 2 ∪ roleDomain child 3)
      (residualFailure child p cp σ) (Rate.diagonal tau htau)) :
    OracleSound univ (fun d H => failure child p cp σ (fun _ => False) H d)
      ⟨rho+tau,max rho tau,add_nonneg hrho htau,hrho.trans (le_max_left _ _)⟩ := by
  have hcert (i : Fin 2) : OracleSound (wholeBlockDomains child i)
      (wholeBlockEvents child p cp σ i) (jointBlockRates rho tau hrho htau i) := by
    fin_cases i
    · exact hparent
    · exact hchild
  have hcover (d : Proof child) (H : HashInput child → Answer child)
      (hf : failure child p cp σ (fun _ => False) H d) : ∃ i, wholeBlockEvents child p cp σ i d H := by
    by_cases hp : queryCapacityEvent child cp σ (query d.1 d.2.1) H
    · exact ⟨0,hp⟩
    · exact ⟨1,hf,hp⟩
  have hslope (i : Fin 2) : (jointBlockRates rho tau hrho htau i).slope ≤ max rho tau := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have h := oracle_parallel_certificate (wholeBlockDomains child) (wholeBlockEvents child p cp σ)
    (jointBlockRates rho tau hrho htau) hcert
    (fun d H => failure child p cp σ (fun _ => False) H d) hcover
    (wholeBlockDomains_disjoint child) (max rho tau) (hrho.trans (le_max_left _ _)) hslope
  rw [wholeBlockDomains_union child] at h
  simpa only [aggregate, jointBlockRates, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Rate.diagonal, add_zero] using h

theorem joint_whole_block_affine_bound (σ : I.layer.Statement)
    (rho tau : ℚ) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hparent : OracleSound (queryBlockDomain child)
      (fun d : Proof child => queryCapacityEvent child cp σ (query d.1 d.2.1))
      (Rate.diagonal rho hrho))
    (hchild : OracleSound (roleDomain child 2 ∪ roleDomain child 3)
      (residualFailure child p cp σ) (Rate.diagonal tau htau))
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => failure child p cp σ (fun _ => False) H (tree.run H).1) ≤
      rho+tau+N*max rho tau := by
  have h := joint_whole_block_oracle_sound child p cp σ rho tau hrho htau hparent hchild N tree
  have hcost : ∀ H, queryCost (univ : Finset (HashInput child)) tree H ≤ (N : ℚ) := by
    clear h
    intro H
    induction tree with
    | done => simp [queryCost]
    | query q next ih =>
      simpa only [queryCost, Finset.mem_univ, if_true, Nat.cast_add, Nat.cast_one, add_comm]
        using add_le_add_left (ih (H q)) 1
  simpa only [mul_comm] using h.cap N hcost

end RecursivePolygero.FiatShamir.TwoLevel
