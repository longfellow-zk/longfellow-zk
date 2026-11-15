import LfzkV2.PolygeroPrimaryMasking

/-!
# Polygero's ordinary and product-row padding

Product inputs use the smaller interpolation dimension `r+p`, while ordinary
rows use `r+w`. The product output is their pointwise product and has no
independent random prefix. Restricting the witness domain lets both input
prefixes use V1's checked opening-preserving interpolation equivalence.
-/

namespace LfzkV2.PolygeroCoreMasking

open Polynomial LigeroFamily MultiplicativeCode
open RecursivePolygero.Local

variable {F : Type} [Field F] {r w p n nw nq : ℕ}

/-- The Rust product-input dimension is `ceil((r+w)/2)`, with the same `r`
random positions as an ordinary row. -/
def productWidth (r w : ℕ) : ℕ := (r+w+1)/2-r

theorem productWidth_bounds (hshape : r < w) :
    productWidth r w ≤ w ∧ 0 < r + productWidth r w ∧
      2*(r + productWidth r w)-1 ≤ r+w := by
  unfold productWidth
  omega

def productEmbedding (hshape : r < w) : Fin (productWidth r w) ↪ Fin w :=
  ⟨Fin.castLE (productWidth_bounds hshape).1,
    fun _ _ h => Fin.ext (congrArg (fun i : Fin w => i.val) h)⟩

def positionEmbedding (e : Fin p ↪ Fin w) : Position r p n ↪ Position r w n :=
  ((Function.Embedding.refl (Fin r)).sumMap e).sumMap (Function.Embedding.refl (Fin n))

def shortDomain (D : ReedSolomon.Domain F r w n) (e : Fin p ↪ Fin w) :
    ReedSolomon.Domain F r p n where
  point i := D.point (positionEmbedding e i)
  injective := D.injective.comp (positionEmbedding e).injective

theorem short_dimension_le (e : Fin p ↪ Fin w) : p ≤ w := by
  simpa using Fintype.card_le_of_injective e e.injective

noncomputable def shortCode (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) : MultiplicativeCode F r p n :=
  ReedSolomon.multiplicativeCode (shortDomain D e)
    (Nat.le_trans (Nat.add_le_add_left (short_dimension_le e) r) hk)

/-- The smaller input code's interpolation polynomial, evaluated also at the
ordinary code's additional witness positions. -/
noncomputable def inputPolynomial (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) (padding : Fin r → F) (values : Fin p → F) : DegreeLT F (r+p) :=
  ⟨Classical.choose ((ReedSolomon.mem_evaluationSpace (shortDomain D e)).mp
      ((shortCode D hk e).encode_mem padding values)),
    (Classical.choose_spec ((ReedSolomon.mem_evaluationSpace (shortDomain D e)).mp
      ((shortCode D hk e).encode_mem padding values))).1⟩

theorem inputPolynomial_eval (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) (padding : Fin r → F) (values : Fin p → F)
    (i : Position r p n) :
    (inputPolynomial D hk e padding values : F[X]).eval ((shortDomain D e).point i) =
      (shortCode D hk e).encode padding values i :=
  ((Classical.choose_spec ((ReedSolomon.mem_evaluationSpace (shortDomain D e)).mp
    ((shortCode D hk e).encode_mem padding values))).2 i).symm

noncomputable def input (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) (padding : Fin r → F) (values : Fin p → F) : EvaluationRow F r w n :=
  fun i => (inputPolynomial D hk e padding values : F[X]).eval (D.point i)

theorem input_mem (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) (padding : Fin r → F) (values : Fin p → F) :
    input D hk e padding values ∈ (ReedSolomon.multiplicativeCode D hk).base := by
  apply (ReedSolomon.mem_evaluationSpace D).mpr
  exact ⟨inputPolynomial D hk e padding values,
    degreeLT_mono (Nat.add_le_add_left (short_dimension_le e) r)
      (inputPolynomial D hk e padding values).2, fun _ => rfl⟩

theorem input_code (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) (padding : Fin r → F) (values : Fin p → F) (j : Fin n) :
    input D hk e padding values (codePosition j) =
      (shortCode D hk e).encode padding values (codePosition j) :=
  inputPolynomial_eval D hk e padding values (codePosition j)

theorem input_witness (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) (padding : Fin r → F) (values : Fin p → F) (i : Fin p) :
    input D hk e padding values (witnessPosition (e i)) = values i := by
  exact (inputPolynomial_eval D hk e padding values (witnessPosition i)).trans
    ((shortCode D hk e).encode_witness padding values i)

/-- With half-degree inputs, the derived product remains an ordinary row. -/
theorem product_mem (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) (hpositive : 0 < r+p) (hproduct : 2*(r+p)-1 ≤ r+w)
    (leftPad rightPad : Fin r → F) (leftValues rightValues : Fin p → F) :
    rowMul (input D hk e leftPad leftValues) (input D hk e rightPad rightValues) ∈
      (ReedSolomon.multiplicativeCode D hk).base := by
  apply (ReedSolomon.mem_evaluationSpace D).mpr
  refine ⟨(inputPolynomial D hk e leftPad leftValues : F[X]) *
    (inputPolynomial D hk e rightPad rightValues : F[X]), ?_, ?_⟩
  · apply degreeLT_mono hproduct
    convert! mul_mem_degreeLT_add_sub_one hpositive hpositive
      (inputPolynomial D hk e leftPad leftValues).2
      (inputPolynomial D hk e rightPad rightValues).2 using 1
    congr 1
    omega
  · intro i
    simp only [rowMul_apply, input, eval_mul]

/-- The committed logical values. Product outputs are derived, never padded
independently. Product witness positions may be a strict subset of the ordinary
witness positions. -/
structure Messages (F : Type) (w p nw nq : ℕ) where
  ordinary : Fin nw → Fin w → F
  left : Fin nq → Fin p → F
  right : Fin nq → Fin p → F

instance : Zero (Messages F w p nw nq) := ⟨⟨0,0,0⟩⟩

abbrev Tape (F : Type) (r nw nq : ℕ) :=
  (Fin nw → Fin r → F) × (Fin nq → Fin r → F) × (Fin nq → Fin r → F)

noncomputable def encoding (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) (messages : Messages F w p nw nq) (tape : Tape F r nw nq) :
    PolygeroMasking.CoreRows F r w n nw nq
  | .linear, row => (ReedSolomon.multiplicativeCode D hk).encode
      (tape.1 row) (messages.ordinary row)
  | .left, row => input D hk e (tape.2.1 row) (messages.left row)
  | .right, row => input D hk e (tape.2.2 row) (messages.right row)
  | .output, row => rowMul (input D hk e (tape.2.1 row) (messages.left row))
      (input D hk e (tape.2.2 row) (messages.right row))

theorem encoding_mem (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) (hpositive : 0 < r+p) (hproduct : 2*(r+p)-1 ≤ r+w)
    (messages : Messages F w p nw nq) (tape : Tape F r nw nq)
    (block : CoreBlock) (row : Fin (block.rowCount nw nq)) :
    encoding D hk e messages tape block row ∈ (ReedSolomon.multiplicativeCode D hk).base := by
  cases block with
  | linear => exact (ReedSolomon.multiplicativeCode D hk).encode_mem _ _
  | left => exact input_mem D hk e _ _
  | right => exact input_mem D hk e _ _
  | output => exact product_mem D hk e hpositive hproduct _ _ _ _

theorem encoding_product (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) (messages : Messages F w p nw nq) (tape : Tape F r nw nq)
    (row : Fin nq) (i : Position r w n) :
    encoding D hk e messages tape .left row i * encoding D hk e messages tape .right row i =
      encoding D hk e messages tape .output row i := rfl

/-- The zero-message simulator has zero ordinary witness values and zero
product witness values at the product layout. Extra evaluations of a short
input polynomial are not asserted to be zero. -/
theorem zero_encoding_active (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) (tape : Tape F r nw nq)
    (block : CoreBlock) (row : Fin (block.rowCount nw nq)) (col : Fin w)
    (hactive : block = .linear ∨ col ∈ Set.range e) :
    encoding D hk e 0 tape block row (witnessPosition col) = 0 := by
  cases block with
  | linear => exact (ReedSolomon.multiplicativeCode D hk).encode_witness _ _ col
  | left =>
      obtain ⟨i, rfl⟩ := hactive.resolve_left (by decide)
      exact input_witness D hk e _ _ i
  | right =>
      obtain ⟨i, rfl⟩ := hactive.resolve_left (by decide)
      exact input_witness D hk e _ _ i
  | output =>
      obtain ⟨i, rfl⟩ := hactive.resolve_left (by decide)
      simp only [encoding, rowMul_apply, input_witness]
      change (0 : F) * 0 = 0
      exact zero_mul 0

/-- The zero-message simulator's arithmetic core has zero linear value for
every statement whose product coefficients use the actual product slots. -/
theorem zero_encoding_linearValue {Equations : Type} [Fintype Equations]
    (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) (tape : Tape F r nw nq)
    (statement : ConstraintSystem F nw nq w Equations)
    (hsupport : ∀ equation block row col,
      ¬ (block = .linear ∨ col ∈ Set.range e) → statement.coefficient equation block row col = 0)
    (equation : Equations) :
    statement.linearValue
      (layoutCoreMessages (ConstraintLayout.identity w) (encoding D hk e 0 tape)) equation = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro block _
  apply Finset.sum_eq_zero
  intro row _
  apply Finset.sum_eq_zero
  intro col _
  by_cases hactive : block = .linear ∨ col ∈ Set.range e
  · change _ * encoding D hk e 0 tape block row (witnessPosition col) = 0
    rw [zero_encoding_active D hk e tape block row col hactive, mul_zero]
  · rw [hsupport equation block row col hactive, zero_mul]

noncomputable def translate (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) (Q : QuerySet n r) (source target : Messages F w p nw nq) :
    Tape F r nw nq ≃ Tape F r nw nq :=
  (Equiv.piCongrRight fun row => translateCorePaddingEquiv
      (ReedSolomon.multiplicativeCode D hk) Q (source.ordinary row) (target.ordinary row)).prodCongr
    ((Equiv.piCongrRight fun row => translateCorePaddingEquiv (shortCode D hk e) Q
        (source.left row) (target.left row)).prodCongr
      (Equiv.piCongrRight fun row => translateCorePaddingEquiv (shortCode D hk e) Q
        (source.right row) (target.right row)))

/-- All core openings, including the virtual product output, are preserved. -/
theorem translate_openings (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (e : Fin p ↪ Fin w) (Q : QuerySet n r) (source target : Messages F w p nw nq)
    (tape : Tape F r nw nq) (block : CoreBlock) (row : Fin (block.rowCount nw nq))
    (j : ↥Q.coordinates) :
    encoding D hk e target (translate D hk e Q source target tape) block row (codePosition j.1) =
      encoding D hk e source tape block row (codePosition j.1) := by
  have hleft (row : Fin nq) : input D hk e ((translate D hk e Q source target tape).2.1 row)
      (target.left row) (codePosition j.1) =
      input D hk e (tape.2.1 row) (source.left row) (codePosition j.1) := by
    rw [input_code, input_code]
    exact congrFun (translateCorePadding_opening (shortCode D hk e) Q
      (source.left row) (target.left row) (tape.2.1 row)) j
  have hright (row : Fin nq) : input D hk e ((translate D hk e Q source target tape).2.2 row)
      (target.right row) (codePosition j.1) =
      input D hk e (tape.2.2 row) (source.right row) (codePosition j.1) := by
    rw [input_code, input_code]
    exact congrFun (translateCorePadding_opening (shortCode D hk e) Q
      (source.right row) (target.right row) (tape.2.2 row)) j
  cases block with
  | linear =>
      exact congrFun (translateCorePadding_opening (ReedSolomon.multiplicativeCode D hk) Q
        (source.ordinary row) (target.ordinary row) (tape.1 row)) j
  | left => exact hleft row
  | right => exact hright row
  | output => exact congrArg₂ (· * ·) (hleft row) (hright row)

end LfzkV2.PolygeroCoreMasking
