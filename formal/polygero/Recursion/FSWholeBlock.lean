import polygero.Recursion.FSStoppedCharges

/-! Sequentially related recursive failures, composed over disjoint hash
footprints. The parent/query certificate may use any proved stopped price;
the terminal child certificate covers the residual failure. Arbitrary
interleavings pay the larger coefficient, since their domains are disjoint. -/

namespace RecursivePolygero.FiatShamir.TwoLevel

open Finset Bcs.AffineBlock Bcs.TotalOracle.Footprint
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)
variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

noncomputable def residualFailure (σ : I.layer.Statement)
    (d : Proof child) (H : HashInput child → Answer child) : Prop :=
  failure child p cp σ (fun _ => False) H d ∧
    ¬ queryCapacityEvent child cp σ (query d.1 d.2.1) H

noncomputable def wholeBlockDomains : Fin 2 → Finset (HashInput child) :=
  ![queryBlockDomain child, (roleDomain child 2 ∪ roleDomain child 3)]

noncomputable def wholeBlockEvents (σ : I.layer.Statement) :
    Fin 2 → Proof child → (HashInput child → Answer child) → Prop :=
  ![fun d H => queryCapacityEvent child cp σ (query d.1 d.2.1) H,
    residualFailure child p cp σ]

def wholeBlockRates (rho tau : ℚ) (hrho : 0 ≤ rho) (htau : 0 ≤ tau) : Fin 2 → Rate :=
  ![⟨2*rho,rho,mul_nonneg (by norm_num) hrho,hrho⟩,
    Rate.diagonal tau htau]

def wholeBlockRate (rho tau : ℚ) (hrho : 0 ≤ rho) (htau : 0 ≤ tau) : Rate :=
  ⟨2*rho+tau, max rho tau, add_nonneg (mul_nonneg (by norm_num) hrho) htau,
    hrho.trans (le_max_left _ _)⟩

theorem wholeBlockDomains_disjoint : Pairwise (fun i j =>
    Disjoint (wholeBlockDomains child i) (wholeBlockDomains child j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · apply disjoint_left.mpr
    intro x hx hy
    rcases x with W | (WV | (b | d)) <;>
      simp_all [wholeBlockDomains, queryBlockDomain, roleDomain, hashRole]
  · apply disjoint_left.mpr
    intro x hx hy
    rcases x with W | (WV | (b | d)) <;>
      simp_all [wholeBlockDomains, queryBlockDomain, roleDomain, hashRole]
  · exact (hij rfl).elim

theorem wholeBlockDomains_union : univ.biUnion (wholeBlockDomains child) = univ := by
  ext x
  rcases x with W | (WV | (b | d)) <;>
    simp [wholeBlockDomains, queryBlockDomain, roleDomain,
      hashRole, Fin.exists_fin_two]

/-- The whole two-level recursive interface. No relation between parent
and terminal query order is assumed. A proved better parent price can be
substituted without revisiting the terminal algebra or the composition. -/
theorem whole_block_oracle_sound (σ : I.layer.Statement)
    (rho tau : ℚ) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hparent : OracleSound (queryBlockDomain child)
      (fun d : Proof child => queryCapacityEvent child cp σ (query d.1 d.2.1))
      ⟨2*rho,rho,mul_nonneg (by norm_num) hrho,hrho⟩)
    (hchild : OracleSound ((roleDomain child 2 ∪ roleDomain child 3))
      (residualFailure child p cp σ) (Rate.diagonal tau htau)) :
    OracleSound univ (fun d H => failure child p cp σ (fun _ => False) H d)
      (wholeBlockRate rho tau hrho htau) := by
  have hcert (i : Fin 2) : OracleSound (wholeBlockDomains child i)
      (wholeBlockEvents child p cp σ i) (wholeBlockRates rho tau hrho htau i) := by
    fin_cases i
    · exact hparent
    · exact hchild
  have hcover (d : Proof child) (H : HashInput child → Answer child)
      (hf : failure child p cp σ (fun _ => False) H d) :
      ∃ i, wholeBlockEvents child p cp σ i d H := by
    by_cases hp : queryCapacityEvent child cp σ (query d.1 d.2.1) H
    · exact ⟨0,hp⟩
    · exact ⟨1,hf,hp⟩
  have hslope (i : Fin 2) : (wholeBlockRates rho tau hrho htau i).slope ≤ max rho tau := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have h := oracle_parallel_certificate (wholeBlockDomains child) (wholeBlockEvents child p cp σ)
    (wholeBlockRates rho tau hrho htau) hcert
    (fun d H => failure child p cp σ (fun _ => False) H d) hcover
    (wholeBlockDomains_disjoint child) (max rho tau) (hrho.trans (le_max_left _ _)) hslope
  rw [wholeBlockDomains_union child] at h
  simpa only [wholeBlockRate, aggregate, wholeBlockRates, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
    Rate.diagonal, add_zero] using h

/-- Full arbitrary-order ROM failure bound. The local prices are retained
as an affine intercept and the maximum per-query slope. -/
theorem whole_block_affine_bound (σ : I.layer.Statement)
    (rho tau : ℚ) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hparent : OracleSound (queryBlockDomain child)
      (fun d : Proof child => queryCapacityEvent child cp σ (query d.1 d.2.1))
      ⟨2*rho,rho,mul_nonneg (by norm_num) hrho,hrho⟩)
    (hchild : OracleSound ((roleDomain child 2 ∪ roleDomain child 3))
      (residualFailure child p cp σ) (Rate.diagonal tau htau))
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => failure child p cp σ (fun _ => False) H (tree.run H).1) ≤
      2*rho+tau + N*max rho tau := by
  have h := whole_block_oracle_sound child p cp σ rho tau hrho htau hparent hchild N tree
  have hcost : ∀ H, queryCost (univ : Finset (HashInput child)) tree H ≤ (N : ℚ) := by
    clear h
    intro H
    induction tree with
    | done => simp [queryCost]
    | query q next ih =>
      simpa only [queryCost, Finset.mem_univ, if_true, Nat.cast_add, Nat.cast_one, add_comm]
        using add_le_add_left (ih (H q)) 1
  simpa only [wholeBlockRate, mul_comm] using h.cap N hcost

/-- On a false parent statement, actual acceptance equals extraction
failure, so the composed coefficient is also a soundness coefficient. -/
theorem whole_block_soundness_bound (σ : I.layer.Statement)
    (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    (rho tau : ℚ) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hparent : OracleSound (queryBlockDomain child)
      (fun d : Proof child => queryCapacityEvent child cp σ (query d.1 d.2.1))
      ⟨2*rho,rho,mul_nonneg (by norm_num) hrho,hrho⟩)
    (hchild : OracleSound (roleDomain child 2 ∪ roleDomain child 3)
      (residualFailure child p cp σ) (Rate.diagonal tau htau))
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => accepts child σ H (tree.run H).1) ≤
      2*rho+tau + N*max rho tau := by
  have he (H : HashInput child → Answer child) :
      failure child p cp σ (fun _ => False) H (tree.run H).1 ↔
        accepts child σ H (tree.run H).1 := by
    rw [failure_empty_iff]
    have hn : (twoProof child p cp).run σ (tree.run H).1.1
        (constantMessages child (tree.run H).1) (proofCoins child H (tree.run H).1) = none := by
      cases hh : (twoProof child p cp).run σ (tree.run H).1.1
          (constantMessages child (tree.run H).1) (proofCoins child H (tree.run H).1) with
      | none => rfl
      | some g => exact (hfalse _ ((twoProof child p cp).run_valid _ _ _ _ g hh)).elim
    simp only [hn, and_true]
  simpa only [he] using whole_block_affine_bound child p cp σ rho tau hrho htau hparent hchild tree

end RecursivePolygero.FiatShamir.TwoLevel
