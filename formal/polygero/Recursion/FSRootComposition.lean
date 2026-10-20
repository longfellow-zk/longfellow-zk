import polygero.Recursion.FSRootTerminal

/-! Parallel composition of the parent/query and residual-child ABS bounds. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.FiatShamir.MerkleFS
open Finset FiatShamir FiatShamir.TwoLevel ProfileAnalysis Bcs.AffineBlock Bcs.TotalOracle.Footprint
open scoped Classical

variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [DecidableEq D]
variable {I : Instance F} (child : Child I)

/-- The disjoint query domains add their completion intercepts and
charge the maximum of their per-query slopes. -/
theorem root_oracle_sound_of_blocks (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (ctx : MerkleFS.Context child (D := D)) (σ : I.layer.Statement)
    (parentRate : Rate)
    (hparent : OracleSound (MerkleFS.queryDomain child)
      (fun d : MerkleFS.Candidate child (D := D) => MerkleFS.queryRisk child ctx cp σ d.1 d.2.1) parentRate)
    (childRate : Rate)
    (hchild : OracleSound (MerkleFS.terminalDomain child)
      (fun d H => MerkleFS.failure child ctx p cp σ d H ∧ ¬ MerkleFS.queryRisk child ctx cp σ d.1 d.2.1 H) childRate) :
    OracleSound univ (MerkleFS.failure child ctx p cp σ)
      ⟨parentRate.intercept+childRate.intercept,max parentRate.slope childRate.slope,
        add_nonneg parentRate.intercept_nonneg childRate.intercept_nonneg,
        parentRate.slope_nonneg.trans (le_max_left _ _)⟩ := by
  let domains : Fin 2 → Finset (MerkleFS.Point child (D := D)) :=
    ![MerkleFS.queryDomain child,MerkleFS.terminalDomain child]
  let events : Fin 2 → MerkleFS.Candidate child (D := D) → (MerkleFS.Point child → MerkleFS.Answer child) → Prop :=
    ![fun d H => MerkleFS.queryRisk child ctx cp σ d.1 d.2.1 H,
      fun d H => MerkleFS.failure child ctx p cp σ d H ∧ ¬ MerkleFS.queryRisk child ctx cp σ d.1 d.2.1 H]
  let rates : Fin 2 → Rate := ![parentRate,
    childRate]
  have hh (i : Fin 2) : OracleSound (domains i) (events i) (rates i) := by
    fin_cases i
    · exact hparent
    · exact hchild
  have hd : Pairwise (fun i j => Disjoint (domains i) (domains j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · apply disjoint_left.mpr; intro x hx hy
      have hlt := (mem_filter.mp hx).2
      have hge := (mem_filter.mp hy).2
      omega
    · apply disjoint_left.mpr; intro x hx hy
      have hge := (mem_filter.mp hx).2
      have hlt := (mem_filter.mp hy).2
      omega
    · exact (hij rfl).elim
  have hu : (univ.biUnion domains) = (univ : Finset (MerkleFS.Point child (D := D))) := by
    ext x
    rcases x with a | (ab | (b | d)) <;>
      simp [domains,Fin.exists_fin_two,MerkleFS.queryDomain,MerkleFS.terminalDomain,MerkleFS.role]
  have hprice (i : Fin 2) : (rates i).slope ≤ max parentRate.slope childRate.slope := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have h := oracle_parallel_certificate domains events rates hh (MerkleFS.failure child ctx p cp σ)
    (by intro d H hf; by_cases he : MerkleFS.queryRisk child ctx cp σ d.1 d.2.1 H
        ; exact ⟨0,he⟩; exact ⟨1,hf,he⟩)
    hd (max parentRate.slope childRate.slope)
    (parentRate.slope_nonneg.trans (le_max_left _ _)) hprice
  rw [hu] at h
  simpa only [aggregate,rates,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.head_cons,add_zero] using h


end RecursivePolygero.FiatShamir.MerkleFS
