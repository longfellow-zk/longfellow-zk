import polygero.Protocol.Instance
import polygero.Local.RowWitness
import polygero.Algebra.RowAgreement

/-! Witness-row tuples, their logical evaluations, and projection from all rows.
Masks are absent from the extracted witness tuple. -/
namespace RecursivePolygero
open Polynomial Finset Codes LigeroFamily RecursivePolygero.Local RecursivePolygero.Local.Polygero
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def coreRowEquiv (nw nq : ℕ) : CoreRow nw nq ≃ Fin (Fintype.card (CoreRow nw nq)) :=
  Fintype.equivFin _

noncomputable def Instance.coreWords (I : Instance F) (W : I.layer.Oracle) :
    Fin (Fintype.card (CoreRow I.nw I.nq)) → Word F I.n := fun i =>
  let r := (coreRowEquiv I.nw I.nq).symm i
  W.ordinary.core r.1 r.2

noncomputable def Instance.coreProjection (I : Instance F)
    (f : Fin (rowCount I.nw I.nq) → DegreeLT F (I.r+I.w)) :
    Fin (Fintype.card (CoreRow I.nw I.nq)) → DegreeLT F (I.r+I.w) := fun i =>
  let r := (coreRowEquiv I.nw I.nq).symm i
  f (coreIndex r.1 r.2)

noncomputable def Instance.coreWitness (I : Instance F)
    (g : Fin (Fintype.card (CoreRow I.nw I.nq)) → DegreeLT F (I.r+I.w)) :
    I.layer.Witness := fun block row a =>
  (g (coreRowEquiv I.nw I.nq ⟨block,row⟩) : F[X]).eval
    (I.domain.point (logicalWitnessPosition I.layout a))

theorem Instance.coreWitness_projection (I : Instance F)
    (f : Fin (rowCount I.nw I.nq) → DegreeLT F (I.r+I.w)) :
    I.coreWitness (I.coreProjection f) = rowWitness (D := I.domain) I.layout f := by
  funext block row a
  dsimp only [coreWitness, coreProjection]
  rw [Equiv.symm_apply_apply]
  simp only [rowWitness, PolynomialDirect.decodedMessages, extendRows_core]

theorem Instance.agreement_subset_core (I : Instance F) (W : I.layer.Oracle)
    (f : Fin (rowCount I.nw I.nq) → DegreeLT F (I.r+I.w)) :
    rowAgreement (PolynomialDirect.primaryCode I.domain I.primary_le) (oracleWords W.ordinary) f ⊆
      rowAgreement (PolynomialDirect.primaryCode I.domain I.primary_le) (I.coreWords W)
        (I.coreProjection f) := by
  classical
  intro j hj
  simp only [rowAgreement, mem_filter, mem_univ, true_and] at hj ⊢
  intro i
  have h := hj
  let r := (coreRowEquiv I.nw I.nq).symm i
  simpa [coreWords, coreProjection, r] using h (coreIndex r.1 r.2)

end RecursivePolygero
