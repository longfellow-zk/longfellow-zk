import polygero.Recursion.FSQueryCapacity
import polygero.Recursion.FSLocalDomains
import Bcs.StoppedCharges

/-! Actual static stopped-price charges for the first two Polygero roles.
The capacity-spectrum premise is explicit. Its use is independent of the
order of parent and query lookups, including cached child commitments.
-/

set_option maxHeartbeats 1000000

namespace RecursivePolygero.FiatShamir.TwoLevel

open Finset Counting ProfileAnalysis Bcs.AffineBlock Bcs.TotalOracle.Footprint
open Bcs.StoppedPotential
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)
variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

def queryEmbedding : (I.layer.Oracle ⊕ (I.layer.Oracle × child.instance.layer.Oracle)) ↪ HashInput child where
  toFun
    | .inl W => gamma W
    | .inr (W,V) => query W V
  inj' := by
    intro x y h
    rcases x with W | ⟨W,V⟩ <;> rcases y with W' | ⟨W',V'⟩ <;>
      simp_all only [gamma, query, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq]

noncomputable def queryBlockDomain : Finset (HashInput child) :=
  roleDomain child 0 ∪ roleDomain child 1

theorem queryEmbedding_mem_domain (x) : queryEmbedding child x ∈ queryBlockDomain child := by
  cases x <;> simp [queryEmbedding, queryBlockDomain, roleDomain, hashRole, gamma, query]

private theorem queryCost_map {Q C Out Out' : Type} [DecidableEq Q]
    (domain : Finset Q) {N : ℕ} (tree : Merkle.RandomOracle.Tree Q C Out N)
    (f : Out → Out') (H : Q → C) :
    queryCost domain (tree.map f) H = queryCost domain tree H := by
  induction tree with
  | done => rfl
  | query q next ih => simp only [Merkle.RandomOracle.Tree.map, queryCost, ih]

/-- A local-domain certificate for the actual parent-query target event.
The only new hypothesis is the displayed mean stopped price. -/
theorem query_stopped_oracle_sound (hcp : cp.listBound < Nat.card F)
    (σ : I.layer.Statement) (rate : ℚ) (hr : 0 ≤ rate)
    (hroot : ∀ W : I.layer.Oracle,
      mean (fun a : I.layer.Coin => repeatPrice rate (queryCapacity child p cp σ W a)) ≤ rate) :
    OracleSound (queryBlockDomain child)
      (fun d : Proof child => queryCapacityEvent child cp σ (query d.1 d.2.1))
      ⟨2*rate, rate, by positivity, hr⟩ := by
  have hraw := Bcs.StoppedCharges.oracle_sound (queryEmbedding child) (queryBlockDomain child)
    (queryEmbedding_mem_domain child)
    (fun W (c : Answer child) => queryCapacity child p cp σ W c.1.1)
    (fun W V a b => queryCapacityRisk child cp σ W V a.1.1 b.1.2)
    rate hr (fun W a => queryCapacity_nonneg child p cp σ W a.1.1) ?_ ?_
  · intro N tree
    have h := hraw N (tree.map (fun d : Proof child => (d.1, d.2.1)))
    refine ⟨queryCost_nonneg _ tree, ?_⟩
    have hb := h.bound
    have hcost : queryCost (queryBlockDomain child) (tree.map (fun d : Proof child => (d.1, d.2.1))) =
        queryCost (queryBlockDomain child) tree := by
      funext H
      exact queryCost_map _ _ _ _
    rw [hcost] at hb
    simp only [Merkle.RandomOracle.Tree.run_map] at hb
    change (Bcs.FiniteProbability.density fun H => queryCapacityRisk child cp σ
      (tree.run H).1.1 (tree.run H).1.2.1 (H (gamma (tree.run H).1.1)).1.1
      (H (query (tree.run H).1.1 (tree.run H).1.2.1)).1.2) ≤
        2*rate + rate * average (queryCost (queryBlockDomain child) tree) at hb
    exact hb
  · intro W
    change mean (fun c : Answer child => repeatPrice rate (queryCapacity child p cp σ W c.1.1)) ≤ rate
    simpa only [mean_prod, mean_const] using hroot W
  · intro W V a
    change mean (fun b : Answer child => indicator
      (queryCapacityRisk child cp σ W V a.1.1 b.1.2)) ≤ _
    simp only [mean_prod, mean_const]
    exact queryCapacityRisk_mean_le child p cp hcp σ W V a.1.1

/-- A proved spectrum bound discharges the mean-price premise. The low
baseline is exactly `L_child * theta_parent`; it is not silently reduced
to a single parent threshold. -/
theorem query_stopped_oracle_sound_of_spectrum (hcp : cp.listBound < Nat.card F)
    (σ : I.layer.Statement) (rate : ℚ)
    (hbase : cp.listBound * p.threshold < rate)
    (hspectrum : ∀ W : I.layer.Oracle,
      p.toProfileParameters.rankError +
        StoppedSpectrum.spectrum I p W (rate - cp.listBound * p.threshold) / Nat.card F ≤ rate) :
    OracleSound (queryBlockDomain child)
      (fun d : Proof child => queryCapacityEvent child cp σ (query d.1 d.2.1))
      ⟨2*rate, rate,
        mul_nonneg (by norm_num) ((mul_nonneg (Nat.cast_nonneg _) p.threshold_nonneg).trans hbase.le),
        (mul_nonneg (Nat.cast_nonneg _) p.threshold_nonneg).trans hbase.le⟩ := by
  apply query_stopped_oracle_sound child p cp hcp σ rate
    ((mul_nonneg (Nat.cast_nonneg _) p.threshold_nonneg).trans hbase.le)
  intro W
  exact (StoppedSpectrum.conditionalCapacity_repeatPrice_mean_le I p σ W rate
    (cp.listBound * p.threshold) (mul_nonneg (Nat.cast_nonneg _) p.threshold_nonneg) hbase).trans
      (hspectrum W)

end RecursivePolygero.FiatShamir.TwoLevel
