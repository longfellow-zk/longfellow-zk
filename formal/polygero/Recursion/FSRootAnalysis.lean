import polygero.Recursion.FSRootComposition
import polygero.Recursion.FSRootTerminal
import polygero.Recursion.FSRootCapacity
import polygero.Recursion.FSCoreQuery

/-! Algebraic price obligations and their ROM transport, parameterized by
both parent and child prices. No numerical instance is imported. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.FiatShamir.MerkleFS.CoreAnalysis
open Finset FiatShamir FiatShamir.TwoLevel ProfileAnalysis Bcs.AffineBlock Bcs.TotalOracle.Footprint
open scoped Classical
variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [DecidableEq D]
variable {I : Instance F} (child : Child I)

/-- Numerical certificate fields, independent of all Merkle tapes and contexts. -/
structure AnalysisAt (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance) (rate childRate : ℚ) : Prop where
  root : ∀ σ W, mean (fun a => Bcs.StoppedPotential.repeatPrice rate
    (coreQueryCapacity child p cp σ W a)) ≤ rate
  fresh : ∀ σ W, mean (coreQueryCapacity child p cp σ W) ≤ rate
  small : cp.listBound < Nat.card F
  childMean : ∀ (stmt : child.instance.layer.Statement) (V : child.instance.layer.Oracle),
    mean (fun a => responseIncidence child.instance cp stmt V a
      (coveredRigidResponses child.instance cp stmt V a (fun _ => False)
        (highSystems child.instance cp V)) - cp.threshold +
      indicator (nonrigidException child.instance cp stmt V (highSystems child.instance cp V) a)) ≤
      childRate-cp.threshold
  child_nonneg : 0 ≤ childRate-cp.threshold

/-- Uniform root-context ABS transports the numerical capacity spectrum
without assuming that a child commitment is fixed before the parent coin. -/
theorem root_oracle_sound_at (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (rate childRate : ℚ) (hr : 0 ≤ rate) (hcr : 0 ≤ childRate) (hchild : childRate ≤ rate)
    (ha : AnalysisAt child p cp rate childRate) (ctx : MerkleFS.Context child (D := D)) (σ : I.layer.Statement) :
    OracleSound univ (MerkleFS.failure child ctx p cp σ)
      ⟨rate+childRate,rate,
        add_nonneg hr hcr,
        hr⟩ := by
  have hp := MerkleFS.Capacity.query_oracle_sound child ctx cp (coreQueryCapacity child p cp)
    (coreQueryCapacity_nonneg child p cp) (queryCapacityRisk_mean_le_core child p cp ha.small)
    σ rate hr (ha.root σ) (ha.fresh σ)
  have hc : OracleSound (MerkleFS.terminalDomain child)
      (fun d H => MerkleFS.failure child ctx p cp σ d H ∧ ¬ MerkleFS.queryRisk child ctx cp σ d.1 d.2.1 H)
      (Rate.diagonal childRate hcr) := by
    have h := MerkleFS.child_oracle_sound child ctx cp p σ (childRate-cp.threshold)
      ha.child_nonneg ha.childMean
    simpa only [sub_add_cancel] using h
  simpa only [Rate.diagonal,max_eq_left hchild] using
    MerkleFS.root_oracle_sound_of_blocks child p cp ctx σ (Rate.diagonal rate hr) hp
      (Rate.diagonal childRate hcr) hc

theorem root_failure_bound_at (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (rate childRate : ℚ) (hr : 0 ≤ rate) (hcr : 0 ≤ childRate) (hchild : childRate ≤ rate)
    (ha : AnalysisAt child p cp rate childRate) (ctx : MerkleFS.Context child (D := D)) (σ : I.layer.Statement)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (MerkleFS.Point child (D := D)) (MerkleFS.Answer child) (MerkleFS.Candidate child (D := D)) N) :
    Bcs.FiniteProbability.density (fun H => MerkleFS.failure child ctx p cp σ (tree.run H).1 H) ≤
      rate+childRate+N*rate := by
  have h := root_oracle_sound_at child p cp rate childRate hr hcr hchild ha ctx σ N tree
  have hc : ∀ H, queryCost (univ : Finset (MerkleFS.Point child (D := D))) tree H ≤ (N : ℚ) := by
    clear h
    intro H
    induction tree with
    | done => simp [queryCost]
    | query q next ih => simpa only [queryCost,mem_univ,if_true,Nat.cast_add,Nat.cast_one,add_comm]
        using add_le_add_left (ih (H q)) 1
  simpa only [mul_comm] using h.cap N hc


end RecursivePolygero.FiatShamir.MerkleFS.CoreAnalysis
