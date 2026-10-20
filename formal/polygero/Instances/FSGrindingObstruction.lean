import polygero.Instances.FSGrinding
import polygero.Instances.FSGrindingInstance
import polygero.Recursion.FSGrindingConcrete

/-! A concrete counterexample to the universal no-loss two-level FS bound.
The field, parent statement, code domains, child encoding, local IOP
certificates, bounded adversary and strict probability comparison are all
instantiated. The model is the existing typed challenge ROM of FSInputs. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace RecursivePolygero.Instances.FSGrindingObstruction
open Finset ProfileAnalysis Local Local.Polygero LigeroFamily
open FiatShamir FiatShamir.TwoLevel Merkle.RandomOracle
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private def reindexTree {Q A Out : Type} {N M : ℕ} (h : N=M)
    (tree : Tree Q A Out N) : Tree Q A Out M := h ▸ tree

private theorem run_reindexTree {Q A Out : Type} {N M : ℕ} (h : N=M)
    (tree : Tree Q A Out N) (H : Q → A) :
    (reindexTree h tree).run H = tree.run H := by
  subst M
  rfl

/-- The counterexample uses the same verified 81/80-opening geometry as
the complete three-bit upper bound, with concrete Johnson/Hahn local
certificates. There is no consumption or event-coverage assumption. -/
theorem exists_no_loss_violation (hF : Fintype.card F = 2^128)
    (D : ReedSolomon.Domain F 0 512 8192) :
    let I := FSGrindingInstance.retunedParent D
    let C := FSGrindingInstance.retunedChild D
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate C.instance,
    ∃ sigma : I.layer.Statement,
    ∃ tree : Tree (HashInput C) (Answer C) (Proof C) FSGrinding.totalQueries,
      (∀ witness, ¬ I.layer.satisfies sigma witness) ∧
      (FSGrinding.totalQueries + 1 : ℕ) * twoError p.error cp.error <
        Bcs.FiniteProbability.density (fun H =>
          failure C p cp sigma (fun _ => False) H (tree.run H).1) := by
  let I := FSGrindingInstance.retunedParent D
  let C := FSGrindingInstance.retunedChild D
  have hq : Nat.card F = FSTwoLevel.fieldSize := by
    rw [Nat.card_eq_fintype_card, hF]
    rfl
  have hgeo : FSTwoLevel.Geometry I (FSTwoLevel.data .threeBit) := ⟨rfl,rfl,rfl,rfl⟩
  have hcgeo : FSTwoLevel.Geometry C.instance (FSTwoLevel.childData .threeBit) := ⟨rfl,rfl,rfl,rfl⟩
  obtain ⟨p, hpTheta, _, hpMu⟩ := FSTwoLevel.certificate I (FSTwoLevel.data .threeBit)
    (FSTwoLevel.checked .threeBit).1 hgeo hq
  obtain ⟨cp, hcTheta, _, hcMu⟩ := FSTwoLevel.certificate C.instance (FSTwoLevel.childData .threeBit)
    (FSTwoLevel.checked .threeBit).2.1 hcgeo hq
  have herr : twoError p.error cp.error = FSGrinding.referenceError := by
    simp only [twoError, HahnSystemCertificate.error, ProfileAnalysis.profile,
      FSGrinding.referenceError, hpTheta, hcTheta, hpMu, hcMu, hq, FSGrinding.fieldSize,
      FSTwoLevel.fieldSize]
  let vals : Fin 3 ↪ F := Classical.choice (Function.Embedding.nonempty_of_card_le
    (by rw [hF]; norm_num : Fintype.card (Fin 3) ≤ Fintype.card F))
  have hM : FSGrinding.childAttempts ≤ Fintype.card F := by
    rw [hF]
    have hb := FSGrinding.checked.1
    have hn : FSGrinding.totalQueries ≤ 2^128 := by unfold FSGrinding.totalQueries; decide
    omega
  have hR : FSGrinding.parentAttempts ≤ Fintype.card F := by
    rw [hF]
    have hb := FSGrinding.checked.1
    have hn : FSGrinding.totalQueries ≤ 2^128 := by unfold FSGrinding.totalQueries; decide
    omega
  have hk : 1 ≤ C.instance.r + C.instance.w := by change 1 ≤ 512; decide
  have ht := geometry_exists_failure_tree D (ConstraintLayout.logicalPrefix 1 511)
    1 64 81 (by decide) (by decide) ((0 : Fin 1), (0 : Fin 1)) (by decide)
    vals vals.injective C p cp hk (FSGrindingInstance.retunedVariedRow D) (FSGrindingInstance.retunedVariedColumn D)
    FSGrinding.parentAttempts FSGrinding.childAttempts 8 hR hM FSGrinding.checked.2.1
  obtain ⟨tree, hlower⟩ := ht
  have havoid : grindingAvoidance C = FSGrinding.terminalSuccess := by
    rw [grindingAvoidance_eq C (by change 0 < 8192; decide : 0 < C.instance.n)]
    rfl
  have hcount : (2+FSGrinding.childAttempts)+FSGrinding.parentAttempts = FSGrinding.totalQueries := by
    have h := FSGrinding.checked.1
    omega
  let finalTree := reindexTree hcount tree
  have hscalar : FSGrinding.candidateLower =
      (FSGrinding.parentAttempts * (3 / (Fintype.card F : ℚ) - 2 / (Fintype.card F : ℚ)^2) -
        (FSGrinding.parentAttempts.choose 2 : ℚ) *
          (3 / (Fintype.card F : ℚ) - 2 / (Fintype.card F : ℚ)^2)^2) *
        (1 - 1 / (∑ k ∈ range (8+1), (FSGrinding.childAttempts.choose k : ℚ) *
          ((Nat.choose 3071 81 : ℚ) / Nat.choose 8192 81)^k)) * grindingAvoidance C := by
    rw [hF, havoid]
    rfl
  have hlow : FSGrinding.candidateLower ≤ Bcs.FiniteProbability.density (fun H =>
      failure C p cp (GrindingAlgebra.contradictoryStatement ((0 : Fin 1),(0 : Fin 1)))
        (fun _ => False) H (tree.run H).1) := hscalar.symm ▸ hlower

  refine ⟨p, cp, GrindingAlgebra.contradictoryStatement ((0 : Fin 1),(0 : Fin 1)), finalTree, ?_, ?_⟩
  · intro witness hs
    exact GrindingAlgebra.contradictoryStatement_false ((0 : Fin 1),(0 : Fin 1)) ⟨witness,hs⟩
  · rw [herr]
    change FSGrinding.noLossUpper < _
    have hcandidate : (423 : ℚ) / 10000 < FSGrinding.candidateLower :=
      FSGrinding.checked.2.2.2.2.2.2.2.1
    have hupper : FSGrinding.noLossUpper < (413 : ℚ) / 10000 :=
      FSGrinding.checked.2.2.2.2.2.2.2.2.1
    have hsep : FSGrinding.noLossUpper < FSGrinding.candidateLower :=
      hupper.trans ((by norm_num : (413 : ℚ) / 10000 < 423 / 10000).trans hcandidate)

    have hevent : Bcs.FiniteProbability.density (fun H =>
        failure C p cp (GrindingAlgebra.contradictoryStatement ((0 : Fin 1),(0 : Fin 1)))
          (fun _ => False) H (finalTree.run H).1) =
      Bcs.FiniteProbability.density (fun H =>
        failure C p cp (GrindingAlgebra.contradictoryStatement ((0 : Fin 1),(0 : Fin 1)))
          (fun _ => False) H (tree.run H).1) := by
      apply congrArg Bcs.FiniteProbability.density
      funext H
      exact congrArg (fun d => failure C p cp
        (GrindingAlgebra.contradictoryStatement ((0 : Fin 1),(0 : Fin 1)))
        (fun _ => False) H d) (congrArg Prod.fst (run_reindexTree hcount tree H))
    exact (hsep.trans_le hlow).trans_eq hevent.symm

/-- An actual inhabited field and code domain remove every setup premise
from the counterexample. -/
theorem concrete_no_loss_violation :
    let I := FSGrindingInstance.concreteRetunedParent
    let C := FSGrindingInstance.concreteRetunedChild
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate C.instance,
    ∃ sigma : I.layer.Statement,
    ∃ tree : Tree (HashInput C) (Answer C) (Proof C) FSGrinding.totalQueries,
      (∀ witness, ¬ I.layer.satisfies sigma witness) ∧
      (FSGrinding.totalQueries + 1 : ℕ) * twoError p.error cp.error <
        Bcs.FiniteProbability.density (fun H =>
          failure C p cp sigma (fun _ => False) H (tree.run H).1) :=
  exists_no_loss_violation FSGrindingInstance.field128_card FSGrindingInstance.concreteDomain

/-- The same explicit instance violates the no-loss soundness bound for
false-statement acceptance itself, independently of extraction syntax. -/
theorem concrete_no_loss_soundness_violation :
    let I := FSGrindingInstance.concreteRetunedParent
    let C := FSGrindingInstance.concreteRetunedChild
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate C.instance,
    ∃ sigma : I.layer.Statement,
    ∃ tree : Tree (HashInput C) (Answer C) (Proof C) FSGrinding.totalQueries,
      (∀ witness, ¬ I.layer.satisfies sigma witness) ∧
      (FSGrinding.totalQueries + 1 : ℕ) * twoError p.error cp.error <
        Bcs.FiniteProbability.density (fun H => accepts C sigma H (tree.run H).1) := by
  obtain ⟨p, cp, sigma, tree, hfalse, hfailure⟩ := concrete_no_loss_violation
  refine ⟨p, cp, sigma, tree, hfalse, hfailure.trans_le ?_⟩
  exact Bcs.FiniteProbability.density_mono (fun H hf => hf.1)

end RecursivePolygero.Instances.FSGrindingObstruction
