import LfzkV2.Current.ZeroKnowledge.Backend

/-! The simulator's public correction is ordinary Lagrange interpolation.
The abstract existence choice in PolygeroMasking does not hide a witness
search: exactly k public nodes (the logical witness suffix and the opening
positions) determine its base polynomial uniquely. The adjustment of honest
private coins belongs only to the distribution coupling. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Backend
open Polynomial LigeroFamily MultiplicativeCode Finset
open scoped Classical

variable {F : Type} [Field F] {r w n : ℕ}
variable (G : PolygeroZk.Geometry F r w 0 n)

def correctionNodes (w : ℕ) (Q : QuerySet n r) : Finset (Position r w n) :=
  witnessPositions r w n ∪ codePositions Q.coordinates

theorem correctionNodes_card (Q : QuerySet n r) :
    (correctionNodes w Q).card = r+w := by
  rw [correctionNodes,card_witnessPositions_union_codePositions,QuerySet.card_coordinates]
  omega

def correctionValues (pivot : Fin w) (target : F) : Position r w n → F
  | .inl (.inr i) => if i = pivot then target else 0
  | _ => 0

def correctionPolynomial (Q : QuerySet n r) (pivot : Fin w) (target : F) : F[X] :=
  Lagrange.interpolate (correctionNodes w Q) G.domain.point (correctionValues pivot target)

theorem correctionPolynomial_degree (Q : QuerySet n r) (pivot : Fin w) (target : F) :
    correctionPolynomial G Q pivot target ∈ Polynomial.degreeLT F (r+w) := by
  rw [Polynomial.mem_degreeLT]
  have h := Lagrange.degree_interpolate_lt (s := correctionNodes w Q)
    (correctionValues pivot target) G.domain.injective.injOn
  simpa only [correctionPolynomial,correctionNodes_card] using h

theorem correctionPolynomial_eval (Q : QuerySet n r) (pivot : Fin w) (target : F)
    (i : Position r w n) (hi : i ∈ correctionNodes w Q) :
    (correctionPolynomial G Q pivot target).eval (G.domain.point i) = correctionValues pivot target i :=
  Lagrange.eval_interpolate_at_node (correctionValues pivot target) G.domain.injective.injOn hi

/-- Identification with the actual simulator, with no extra assumption
about its abstract interpolation implementation. -/
theorem correctionBase_eq_polynomial (Q : QuerySet n r) (pivot : Fin w) (target : F) :
    PolygeroMasking.correctionBase G.code Q (ConstraintLayout.identity w) pivot target =
      fun i => (correctionPolynomial G Q pivot target).eval (G.domain.point i) := by
  have hsource := PolygeroMasking.correctionBase_properties G.code Q
    (ConstraintLayout.identity w) pivot target
  have htarget : (fun i => (correctionPolynomial G Q pivot target).eval (G.domain.point i)) ∈ G.code.base :=
    (ReedSolomon.mem_evaluationSpace G.domain).mpr
      ⟨_,correctionPolynomial_degree G Q pivot target,fun _ => rfl⟩
  apply G.code.base_unique hsource.1 htarget (correctionNodes w Q)
    (by rw [correctionNodes_card]; rfl)
  intro i hi
  rw [correctionPolynomial_eval G Q pivot target i hi]
  rcases mem_union.mp hi with hi | hi
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hi
    rw [hsource.2.1]
    rfl
  · obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    exact hsource.2.2 j hj

theorem correction_eq_polynomial (Q : QuerySet n r) (pivot : Fin w) (target : F)
    (i : Position r w n) :
    PolygeroMasking.correction G.code Q (ConstraintLayout.identity w) pivot target i =
      G.code.zR i * (correctionPolynomial G Q pivot target).eval (G.domain.point i) := by
  change G.code.zR i *
    PolygeroMasking.correctionBase G.code Q (ConstraintLayout.identity w) pivot target i = _
  rw [correctionBase_eq_polynomial]

end LfzkV2.Current.ZeroKnowledge.Backend
