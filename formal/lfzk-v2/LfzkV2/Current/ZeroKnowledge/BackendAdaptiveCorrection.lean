import LfzkV2.Current.ZeroKnowledge.BackendInterpolation

/-! Public changes between the backend simulator's response fibers.

The frontend, affine statement and all batching challenges are fixed here.
They are sampled before either backend response in the current protocol.
Changing the eventual opening set changes only the public arithmetic
correction. Its base has the same witness coordinates at every opening set.
Their difference is therefore a legal addition to the zero-sum mask row m.
The existing additive fstar translation preserves the primary response too.

This is a triangular equivalence of the actual mask tapes. It uses public
Lagrange interpolation, not conditioning by rejection, witness search, or
an assumed inverse of the complete Fiat--Shamir computation. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Backend.Adaptive
open Polynomial LigeroFamily MultiplicativeCode RecursivePolygero.Local
open scoped Classical

variable {F : Type} [Field F] {r w n nw s : ℕ}
variable (G : PolygeroZk.Geometry F r w 0 n)

def baseDelta (reference selected : QuerySet n r) (pivot : Fin w) (target : F) :
    EvaluationRow F r w n :=
  PolygeroMasking.correctionBase G.code reference (ConstraintLayout.identity w) pivot target -
    PolygeroMasking.correctionBase G.code selected (ConstraintLayout.identity w) pivot target

theorem baseDelta_mem (reference selected : QuerySet n r) (pivot : Fin w) (target : F) :
    baseDelta G reference selected pivot target ∈ G.code.base :=
  G.code.base.sub_mem
    (PolygeroMasking.correctionBase_properties G.code reference (ConstraintLayout.identity w) pivot target).1
    (PolygeroMasking.correctionBase_properties G.code selected (ConstraintLayout.identity w) pivot target).1

theorem baseDelta_witness (reference selected : QuerySet n r) (pivot : Fin w) (target : F)
    (i : Fin w) : baseDelta G reference selected pivot target (witnessPosition i) = 0 := by
  have first := (PolygeroMasking.correctionBase_properties G.code reference
    (ConstraintLayout.identity w) pivot target).2.1 i
  have second := (PolygeroMasking.correctionBase_properties G.code selected
    (ConstraintLayout.identity w) pivot target).2.1 i
  simp only [baseDelta,Pi.sub_apply,first,second,sub_self]

/-- The u row stays unchanged. The m adjustment vanishes at every witness
coordinate, which is stronger than its required zero-sum condition. -/
def maskDelta (reference selected : QuerySet n r) (pivot : Fin w) (target : F) :
    PolygeroMasking.Tape G.code (PolygeroZk.sumFunctional F w) where
  vCoefficient := 0
  zRCoefficient := ⟨baseDelta G reference selected pivot target,
    baseDelta_mem G reference selected pivot target,by simp,by
      have zero : witnessValues (baseDelta G reference selected pivot target) = 0 := by
        funext i
        exact baseDelta_witness G reference selected pivot target i
      rw [zero,map_zero]⟩

theorem maskDelta_response (reference selected : QuerySet n r) (pivot : Fin w) (target : F) :
    PolygeroMasking.response G.code G.basis (PolygeroZk.sumFunctional F w)
        (maskDelta G reference selected pivot target) =
      PolygeroMasking.correction G.code reference (ConstraintLayout.identity w) pivot target -
        PolygeroMasking.correction G.code selected (ConstraintLayout.identity w) pivot target := by
  funext i
  simp only [PolygeroMasking.response,linearMaskMap,maskDelta,baseDelta,
    PolygeroMasking.correction,rowMul,Pi.add_apply,Pi.sub_apply,Submodule.coe_zero,
    Pi.zero_apply,mul_zero,zero_add,mul_sub]

variable {Equations : Type} [Fintype Equations]
variable (statement : ConstraintSystem F nw 0 w Equations)
variable (coin : Polygero.Coin F Equations nw 0 s)

/-- Move from the reference opening simulator to the selected one. The
primary pad is adjusted after m, so the inverse first recovers the old m. -/
def normalize (reference selected : QuerySet n r) (pivot : Fin w) :
    Tape G nw s ≃ Tape G nw s :=
  Equiv.prodCongrRight fun core =>
    ((Equiv.addRight (maskDelta G reference selected pivot (statement.combinedTarget coin.1))).prodCongr
      (Equiv.refl _)).trans
      (Equiv.prodCongrRight fun masks =>
        PolygeroPrimaryMasking.translate G.positive coin.2
          (PolygeroZk.ordinaryRows G 0 core
            (masks - maskDelta G reference selected pivot (statement.combinedTarget coin.1)))
          (PolygeroZk.ordinaryRows G 0 core masks))

theorem normalize_apply (reference selected : QuerySet n r) (pivot : Fin w)
    (tape : Tape G nw s) :
    normalize G statement coin reference selected pivot tape =
      (tape.1,
       tape.2.1 + maskDelta G reference selected pivot (statement.combinedTarget coin.1),
       PolygeroPrimaryMasking.translate G.positive coin.2
         (PolygeroZk.ordinaryRows G 0 tape.1 tape.2.1)
         (PolygeroZk.ordinaryRows G 0 tape.1
           (tape.2.1 + maskDelta G reference selected pivot (statement.combinedTarget coin.1)))
         tape.2.2) := by
  change (tape.1,
    tape.2.1 + maskDelta G reference selected pivot (statement.combinedTarget coin.1),
    PolygeroPrimaryMasking.translate G.positive coin.2
      (PolygeroZk.ordinaryRows G 0 tape.1
        ((tape.2.1 + maskDelta G reference selected pivot (statement.combinedTarget coin.1)) -
          maskDelta G reference selected pivot (statement.combinedTarget coin.1)))
      (PolygeroZk.ordinaryRows G 0 tape.1
        (tape.2.1 + maskDelta G reference selected pivot (statement.combinedTarget coin.1)))
      tape.2.2) = _
  rw [add_sub_cancel_right]

theorem normalize_arithmetic (reference selected : QuerySet n r) (pivot : Fin w)
    (tape : Tape G nw s) :
    PolygeroZk.correctedArithmeticRow G selected pivot statement coin.1
        (normalize G statement coin reference selected pivot tape) =
      PolygeroZk.correctedArithmeticRow G reference pivot statement coin.1 tape := by
  apply Subtype.ext
  rw [normalize_apply]
  change (DirectVerifier.linearCore G.code (ConstraintLayout.identity w) statement coin.1
      (PolygeroZk.core G 0 tape.1) +
    PolygeroMasking.response G.code G.basis (PolygeroZk.sumFunctional F w)
      (tape.2.1 + maskDelta G reference selected pivot (statement.combinedTarget coin.1))) +
      PolygeroMasking.correction G.code selected (ConstraintLayout.identity w) pivot
        (statement.combinedTarget coin.1) = _
  rw [PolygeroMasking.response_add,maskDelta_response]
  change (_ + (_ + (_ - _))) + _ = (_ + _) + _
  abel

/-- Both complete response polynomials are preserved. In particular this
does not condition merely on H while permitting Z to change. -/
theorem normalize_payload (reference selected : QuerySet n r) (pivot : Fin w)
    (tape : Tape G nw s) :
    PolygeroZk.simPayload G G.positive selected pivot statement coin
        (normalize G statement coin reference selected pivot tape) =
      PolygeroZk.simPayload G G.positive reference pivot statement coin tape := by
  apply congrArg₂ LigeroPayload.mk
  · rw [normalize_apply]
    exact PolygeroPrimaryMasking.translate_response G.positive coin.2 _ _ tape.2.2
  · exact congrArg (fun row : G.code.response =>
      PolynomialDirect.responsePolynomial G.domain G.k_le_n row.1 row.2)
      (normalize_arithmetic G statement coin reference selected pivot tape)

/-- Restricting normalization gives an explicit bijection of the two
complete-response fibers. Uniform reference-fiber coins therefore yield
uniform selected-fiber coins, without a conditional sampler or extra draws. -/
def normalizeFiber (reference selected : QuerySet n r) (pivot : Fin w)
    (response : LigeroPayload F (r+w) s) :
    {tape : Tape G nw s //
      PolygeroZk.simPayload G G.positive reference pivot statement coin tape = response} ≃
    {tape : Tape G nw s //
      PolygeroZk.simPayload G G.positive selected pivot statement coin tape = response} where
  toFun tape := ⟨normalize G statement coin reference selected pivot tape.val,
    (normalize_payload G statement coin reference selected pivot tape.val).trans tape.property⟩
  invFun tape := ⟨(normalize G statement coin reference selected pivot).symm tape.val,by
    have preserved := normalize_payload G statement coin reference selected pivot
      ((normalize G statement coin reference selected pivot).symm tape.val)
    rw [Equiv.apply_symm_apply] at preserved
    exact preserved.symm.trans tape.property⟩
  left_inv tape := Subtype.ext ((normalize G statement coin reference selected pivot).symm_apply_apply tape.val)
  right_inv tape := Subtype.ext ((normalize G statement coin reference selected pivot).apply_symm_apply tape.val)

/-- The public m adjustment is explicitly the difference of two degree-k
Lagrange interpolants. This identifies the finite interpolation algorithm
used by normalization without choosing or searching for a private witness. -/
theorem baseDelta_eq_polynomial (reference selected : QuerySet n r) (pivot : Fin w)
    (target : F) (i : Position r w n) :
    baseDelta G reference selected pivot target i =
      (correctionPolynomial G reference pivot target).eval (G.domain.point i) -
        (correctionPolynomial G selected pivot target).eval (G.domain.point i) := by
  simp only [baseDelta,Pi.sub_apply,correctionBase_eq_polynomial]

end LfzkV2.Current.ZeroKnowledge.Backend.Adaptive
