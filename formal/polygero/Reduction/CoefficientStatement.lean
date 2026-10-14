import polygero.Protocol.Verifier
import Mathlib.Data.Finset.Sort

/-! Coefficient-vector substitution. Inner statements have only linear
constraints. Their coefficients and targets are computed from the outer
challenge and its requested openings. -/

namespace RecursivePolygero
open Polynomial Finset LigeroFamily MultiplicativeCode RecursivePolygero.Local RecursivePolygero.Local.Polygero
attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [DecidableEq F]
variable {k s d slots : ℕ}

abbrev CoefficientIndex (k s : ℕ) := Fin (k+s) ⊕ Fin (2*k)
abbrev Slots (d slots : ℕ) := Fin d × Fin slots

/-- Public injective placement of the two coefficient vectors in inner rows. -/
abbrev Packing (k s d slots : ℕ) := CoefficientIndex k s ↪ Slots d slots

noncomputable def unpackPrimary (P : Packing k s d slots) :
    (Slots d slots → F) →ₗ[F] DegreeLT F (k+s) :=
  (Polynomial.degreeLTEquiv F (k+s)).symm.toLinearMap.comp
    (LinearMap.pi fun i => LinearMap.proj (P (.inl i)))

noncomputable def unpackArithmetic (P : Packing k s d slots) :
    (Slots d slots → F) →ₗ[F] DegreeLT F (2*k) :=
  (Polynomial.degreeLTEquiv F (2*k)).symm.toLinearMap.comp
    (LinearMap.pi fun i => LinearMap.proj (P (.inr i)))

noncomputable def unpack (P : Packing k s d slots) (v : Slots d slots → F) : LigeroPayload F k s :=
  ⟨unpackPrimary P v,unpackArithmetic P v⟩

def flatten (w : CoreMessages F d 0 slots) : Slots d slots → F := fun j => w .linear j.1 j.2

def unflatten (v : Slots d slots → F) : CoreMessages F d 0 slots
  | .linear, row, j => v (row,j)
  | .left, row, _ => row.elim0
  | .right, row, _ => row.elim0
  | .output, row, _ => row.elim0

omit [Field F] [DecidableEq F] in
@[simp] theorem flatten_unflatten (v : Slots d slots → F) : flatten (unflatten v) = v := rfl

/-- Turn public linear functionals into the existing Polygero statement type. -/
noncomputable def linearStatement {E : Type} (forms : E → (Slots d slots → F) →ₗ[F] F)
    (targets : E → F) : ConstraintSystem F d 0 slots E where
  coefficient eq block := match block with
    | .linear => fun row j => forms eq (Pi.single (row,j) 1)
    | .left => fun row _ => row.elim0
    | .right => fun row _ => row.elim0
    | .output => fun row _ => row.elim0
  target := targets

omit [DecidableEq F] in
theorem linearStatement_value {E : Type} [Fintype E]
    (forms : E → (Slots d slots → F) →ₗ[F] F) (targets : E → F)
    (w : CoreMessages F d 0 slots) (e : E) :
    (linearStatement forms targets).linearValue w e = forms e (flatten w) := by
  have hdecomp : (∑ j : Slots d slots, (flatten w j) • Pi.single j (1 : F)) = flatten w := by
    funext j
    simp [Pi.single_apply, Pi.smul_apply]
  rw [← hdecomp, map_sum]
  simp only [map_smul, smul_eq_mul]
  unfold ConstraintSystem.linearValue
  rw [sum_eq_single_of_mem CoreBlock.linear (mem_univ _)]
  · simp only [linearStatement,CoreBlock.rowCount,flatten,Fintype.sum_prod_type,mul_comm]
    rfl
  · intro b _ hb
    cases b
    · exact (hb rfl).elim
    all_goals simp [CoreBlock.rowCount]

omit [DecidableEq F] in
theorem linearStatement_satisfies {E : Type} [Fintype E]
    (forms : E → (Slots d slots → F) →ₗ[F] F) (targets : E → F)
    (w : CoreMessages F d 0 slots) :
    (linearStatement forms targets).Satisfies w ↔ ∀ e, forms e (flatten w) = targets e := by
  simp only [ConstraintSystem.Satisfies,linearStatement_value]
  exact and_iff_left (fun row => row.elim0)

noncomputable def pack (P : Packing k s d slots) (payload : LigeroPayload F k s) : Slots d slots → F :=
  fun j => if h : ∃ i, P i = j then
    Sum.elim (Polynomial.degreeLTEquiv F (k+s) payload.primary)
      (Polynomial.degreeLTEquiv F (2*k) payload.arithmetic) (Classical.choose h)
    else 0

omit [DecidableEq F] in
@[simp] theorem pack_apply (P : Packing k s d slots) (payload : LigeroPayload F k s)
    (i : CoefficientIndex k s) : pack P payload (P i) =
      Sum.elim (Polynomial.degreeLTEquiv F (k+s) payload.primary)
        (Polynomial.degreeLTEquiv F (2*k) payload.arithmetic) i := by
  unfold pack
  rw [dif_pos ⟨i,rfl⟩]
  congr 1
  exact P.injective (Classical.choose_spec (show ∃ j, P j = P i from ⟨i,rfl⟩))

omit [DecidableEq F] in
theorem unpack_pack (P : Packing k s d slots) (payload : LigeroPayload F k s) :
    unpack P (pack P payload) = payload := by
  have hp : unpackPrimary P (pack P payload) = payload.primary := by
    apply (Polynomial.degreeLTEquiv F (k+s)).injective
    simp only [unpackPrimary,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply]
    funext i
    exact pack_apply P payload (.inl i)
  have ha : unpackArithmetic P (pack P payload) = payload.arithmetic := by
    apply (Polynomial.degreeLTEquiv F (2*k)).injective
    simp only [unpackArithmetic,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply]
    funext i
    exact pack_apply P payload (.inr i)
  cases payload
  simp only [unpack,hp,ha]

abbrev InnerEquations (t : ℕ) := Fin t ⊕ (Fin t ⊕ Unit)

noncomputable def evalPrimary (P : Packing k s d slots) (x : F) : (Slots d slots → F) →ₗ[F] F :=
  (Polynomial.leval x).comp ((degreeLT F (k+s)).subtype.comp (unpackPrimary P))
noncomputable def evalArithmetic (P : Packing k s d slots) (x : F) : (Slots d slots → F) →ₗ[F] F :=
  (Polynomial.leval x).comp ((degreeLT F (2*k)).subtype.comp (unpackArithmetic P))

variable {Equations : Type} [Fintype Equations]
variable {q r w n nw nq t : ℕ}

noncomputable def queryColumn (Q : QuerySet n t) (j : Fin t) : Fin n :=
  Q.coordinates.orderEmbOfFin Q.card_coordinates j

theorem queryColumn_mem (Q : QuerySet n t) (j : Fin t) : queryColumn Q j ∈ Q.coordinates :=
  Q.coordinates.orderEmbOfFin_mem Q.card_coordinates j

theorem exists_queryColumn (Q : QuerySet n t) (j : Fin n) (hj : j ∈ Q.coordinates) :
    ∃ i, queryColumn Q i = j := by
  change j ∈ Set.range (Q.coordinates.orderEmbOfFin Q.card_coordinates)
  rw [range_orderEmbOfFin]
  exact hj

/-- The response constraints use openings alone. Multiplication tests remain
at the parent; they do not become inner witness constraints. -/
noncomputable def coefficientForms (D : ReedSolomon.Domain F r w n)
    (layout : ConstraintLayout F q w) (P : Packing (r+w) s d slots)
    (Q : QuerySet n t) : InnerEquations t → (Slots d slots → F) →ₗ[F] F
  | .inl j => evalPrimary P (D.point (codePosition (queryColumn Q j)))
  | .inr (.inl j) => evalArithmetic P (D.point (codePosition (queryColumn Q j)))
  | .inr (.inr _) => ∑ i : Fin q, evalArithmetic P (D.point (logicalWitnessPosition layout i))

noncomputable def coefficientTargets (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (_P : Packing (r+w) s d slots) (coin : Coin F Equations nw nq s)
    (Q : QuerySet n t) (opening : Opening F nw nq n t Q) : InnerEquations t → F
  | .inl j =>
    let col : Q.coordinates := ⟨queryColumn Q j, queryColumn_mem Q j⟩
    (∑ i, (coin.2 i : F[X]).eval (D.point (codePosition col.1)) * columnValues (opening.1 col) i) + opening.2 col
  | .inr (.inl j) =>
    let col : Q.coordinates := ⟨queryColumn Q j, queryColumn_mem Q j⟩
    linearPointwise D hk layout statement coin.1 col.1 (columnValues (opening.1 col))
  | .inr (.inr _) => statement.combinedTarget coin.1

noncomputable def coefficientStatement (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (P : Packing (r+w) s d slots) (coin : Coin F Equations nw nq s)
    (Q : QuerySet n t) (opening : Opening F nw nq n t Q) :
    ConstraintSystem F d 0 slots (InnerEquations t) :=
  linearStatement (coefficientForms D layout P Q) (coefficientTargets D hk layout statement P coin Q opening)

def directProducts (Q : QuerySet n t) (opening : Opening F nw nq n t Q) : Prop :=
  ∀ j : Q.coordinates, ∀ g : Fin nq,
    (opening.1 j).core .left g * (opening.1 j).core .right g = (opening.1 j).core .output g

def responseEquations (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (coin : Coin F Equations nw nq s) (payload : LigeroPayload F (r+w) s)
    (Q : QuerySet n t) (opening : Opening F nw nq n t Q) : Prop :=
  globalCheck D layout statement coin.1 payload ∧ ∀ j : Q.coordinates,
    (payload.primary : F[X]).eval (D.point (codePosition j.1)) =
      (∑ i, (coin.2 i : F[X]).eval (D.point (codePosition j.1)) * columnValues (opening.1 j) i) + opening.2 j ∧
    (payload.arithmetic : F[X]).eval (D.point (codePosition j.1)) =
      linearPointwise D hk layout statement coin.1 j.1 (columnValues (opening.1 j))

omit [DecidableEq F] in
/-- Exact translation: the child constrains the parent response coefficients
with no extra nonlinear relation. Unused slots are ignored. -/
theorem coefficientStatement_satisfies
    (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (P : Packing (r+w) s d slots) (coin : Coin F Equations nw nq s)
    (Q : QuerySet n t) (opening : Opening F nw nq n t Q) (witness : CoreMessages F d 0 slots) :
    (coefficientStatement D hk layout statement P coin Q opening).Satisfies witness ↔
      responseEquations D hk layout statement coin (unpack P (flatten witness)) Q opening := by
  rw [coefficientStatement,linearStatement_satisfies]
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · have hh := h (.inr (.inr ()))
      simpa only [coefficientForms,coefficientTargets,LinearMap.sum_apply,
        evalArithmetic, LinearMap.comp_apply, Polynomial.leval_apply,Submodule.subtype_apply,
        unpack,globalCheck] using hh
    · intro j
      obtain ⟨i,hi⟩ := exists_queryColumn Q j.1 j.2
      have hp := h (.inl i)
      have ha := h (.inr (.inl i))
      change (unpackPrimary P (flatten witness) : F[X]).eval (D.point (codePosition (queryColumn Q i))) = _ at hp
      change (unpackArithmetic P (flatten witness) : F[X]).eval (D.point (codePosition (queryColumn Q i))) = _ at ha
      simpa only [coefficientTargets,hi,unpack] using And.intro hp ha
  · rintro ⟨hglobal,hlocal⟩ e
    cases e with
    | inl i => exact (hlocal ⟨queryColumn Q i,queryColumn_mem Q i⟩).1
    | inr e => cases e with
      | inl i => exact (hlocal ⟨queryColumn Q i,queryColumn_mem Q i⟩).2
      | inr u =>
        simpa only [coefficientForms,coefficientTargets,LinearMap.sum_apply,
          evalArithmetic, LinearMap.comp_apply, Polynomial.leval_apply,Submodule.subtype_apply,
          unpack,globalCheck] using hglobal

/-- The parent verifier factors into its retained multiplication tests and
the child's coefficient constraints for every child witness. -/
theorem verifier_factorization
    (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (P : Packing (r+w) s d slots) (coin : Coin F Equations nw nq s)
    (Q : QuerySet n t) (opening : Opening F nw nq n t Q) (witness : CoreMessages F d 0 slots) :
    directProducts Q opening ∧
      (coefficientStatement D hk layout statement P coin Q opening).Satisfies witness ↔
    verify D hk layout statement coin (unpack P (flatten witness)) Q opening = true := by
  rw [coefficientStatement_satisfies]
  simp only [verify,decide_eq_true_eq,responseEquations,directProducts]
  constructor
  · rintro ⟨hproducts, hglobal, hlocal⟩
    exact ⟨hglobal, fun j => ⟨(hlocal j).1, (hlocal j).2, hproducts j⟩⟩
  · rintro ⟨hglobal, hlocal⟩
    exact ⟨fun j => (hlocal j).2.2, hglobal,
      fun j => ⟨(hlocal j).1, (hlocal j).2.1⟩⟩

/-- Every accepted ordinary response has a packed child witness satisfying
the exact coefficient statement. This is the substitution's completeness
direction; the honest pack operation fills unused slots with zero. -/
theorem packed_response_satisfies
    (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (P : Packing (r+w) s d slots) (coin : Coin F Equations nw nq s)
    (Q : QuerySet n t) (opening : Opening F nw nq n t Q) (payload : LigeroPayload F (r+w) s)
    (h : verify D hk layout statement coin payload Q opening = true) :
    directProducts Q opening ∧
      (coefficientStatement D hk layout statement P coin Q opening).Satisfies
        (unflatten (pack P payload)) := by
  apply (verifier_factorization D hk layout statement P coin Q opening _).mpr
  simpa only [flatten_unflatten,unpack_pack] using h

end RecursivePolygero
