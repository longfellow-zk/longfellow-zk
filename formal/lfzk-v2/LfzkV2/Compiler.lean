import LfzkV2.Constraints

/-!
# Lowering V2 constraints to the committed witness

This models `runtime/v2/zk/src/constraint_compiler.rs`. The backend's sparse
linear equations are grouped into rows; term order, repeated coordinates, and
zero coefficients are retained. The input row emits private-input terms before
pad terms, and substitutes public inputs into the constant.
-/

namespace LfzkV2

open SumcheckV2

variable {F Pad Slot : Type} [Field F]

abbrev LinearRow (Slot F : Type) := PadExpression Slot F

def mapTerms (terms : List (Pad × F)) (coordinate : Pad → Slot) : List (Slot × F) :=
  terms.map fun t => (coordinate t.1, t.2)

def compileLayer (c : LayerConstraint Pad Slot F) (coordinate : Pad → Slot) :
    LinearRow Slot F :=
  ⟨c.expression.constant, mapTerms c.expression.terms coordinate ++ [(c.productSlot, -1)]⟩

theorem eval_compileLayer (c : LayerConstraint Pad Slot F) (coordinate : Pad → Slot)
    (witness : Slot → F) :
    (compileLayer c coordinate).eval witness =
      c.expression.eval (witness ∘ coordinate) - witness c.productSlot := by
  simp [compileLayer, PadExpression.eval, mapTerms, Function.comp_def, sub_eq_add_neg,
    add_assoc]

/-- These equations are fixed when committing, separately from the transcript-dependent rows. -/
def ProductsHold (cs : Constraints Pad Slot F) (coordinate : Pad → Slot)
    (witness : Slot → F) : Prop :=
  ∀ c ∈ cs.layers,
    witness c.productSlot = witness (coordinate c.padA) * witness (coordinate c.padB)

/-- The product checks can be fixed from the layout before any messages or challenges.
The builder preserves their order and both pad operands. -/
theorem productsHold_iff (ts : List (LayerTranscript Pad Slot F))
    (cs : Constraints Pad Slot F) (hbuild : buildConstraints ts = some cs)
    (coordinate : Pad → Slot) (witness : Slot → F) :
    ProductsHold cs coordinate witness ↔
      ∀ t ∈ ts,
        witness t.productSlot = witness (coordinate t.padA) * witness (coordinate t.padB) := by
  have hkeys := buildFrom_products zeroClaim ts cs hbuild
  have h := congrArg (fun keys : List (Pad × Pad × Slot) =>
    ∀ key ∈ keys, witness key.2.2 = witness (coordinate key.1) * witness (coordinate key.2.1)) hkeys
  simpa only [ProductsHold, List.forall_mem_map] using iff_of_eq h

def compileInput {nPublic nPrivate : ℕ} (claim : PadExpression Pad F)
    (coordinate : Pad → Slot) (privateCoordinate : Fin nPrivate → Slot)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F) :
    LinearRow Slot F :=
  ⟨claim.constant - dot publicWeights publicInputs,
    List.ofFn (fun j => (privateCoordinate j, -privateWeights j)) ++
      mapTerms claim.terms coordinate⟩

theorem eval_compileInput {nPublic nPrivate : ℕ} (claim : PadExpression Pad F)
    (coordinate : Pad → Slot) (privateCoordinate : Fin nPrivate → Slot)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F)
    (witness : Slot → F) :
    (compileInput claim coordinate privateCoordinate publicWeights publicInputs privateWeights).eval
        witness =
      claim.eval (witness ∘ coordinate) -
        dot (Sum.elim publicWeights privateWeights)
          (Sum.elim publicInputs (witness ∘ privateCoordinate)) := by
  simp only [compileInput, PadExpression.eval, mapTerms, List.map_append, List.sum_append,
    List.map_ofFn, List.sum_ofFn, List.map_map, Function.comp_def]
  simp only [dot, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib]
  ring

def compile {nPublic nPrivate : ℕ} (cs : Constraints Pad Slot F)
    (coordinate : Pad → Slot) (privateCoordinate : Fin nPrivate → Slot)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F) :
    List (LinearRow Slot F) :=
  cs.layers.map (fun c => compileLayer c coordinate) ++
    [compileInput cs.inputClaim coordinate privateCoordinate publicWeights publicInputs privateWeights]

def RowsHold (rows : List (LinearRow Slot F)) (witness : Slot → F) : Prop :=
  ∀ row ∈ rows, row.eval witness = 0

/-- Each layer contributes one row, followed by one input row even for a zero-layer proof. -/
theorem compile_length {nPublic nPrivate : ℕ} (cs : Constraints Pad Slot F)
    (coordinate : Pad → Slot) (privateCoordinate : Fin nPrivate → Slot)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F) :
    (compile cs coordinate privateCoordinate publicWeights publicInputs privateWeights).length =
      cs.layers.length + 1 := by
  simp [compile]

/-- With the committed products checked, compiled rows are exactly the symbolic equations. -/
theorem compile_correct {nPublic nPrivate : ℕ} (cs : Constraints Pad Slot F)
    (coordinate : Pad → Slot) (privateCoordinate : Fin nPrivate → Slot)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F)
    (witness : Slot → F) (hproducts : ProductsHold cs coordinate witness) :
    RowsHold (compile cs coordinate privateCoordinate publicWeights publicInputs privateWeights)
        witness ↔
      cs.Holds (witness ∘ coordinate)
        (dot (Sum.elim publicWeights privateWeights)
          (Sum.elim publicInputs (witness ∘ privateCoordinate))) := by
  simp only [RowsHold, compile, List.forall_mem_append, List.forall_mem_map,
    List.forall_mem_singleton]
  constructor
  · rintro ⟨hlayers, hinput⟩
    constructor
    · intro c hc
      have h := hlayers c hc
      rw [eval_compileLayer, sub_eq_zero, hproducts c hc] at h
      exact h
    · rwa [eval_compileInput, sub_eq_zero] at hinput
  · rintro ⟨hlayers, hinput⟩
    constructor
    · intro c hc
      rw [eval_compileLayer, sub_eq_zero, hproducts c hc]
      exact hlayers c hc
    · rwa [eval_compileInput, sub_eq_zero]

/-- End-to-end algebraic correspondence for the builder and compiler. The product
premise is indispensable; accepting affine rows alone does not verify sumcheck. -/
theorem compiled_iff_clear {nPublic nPrivate : ℕ}
    (ts : List (LayerTranscript Pad Slot F)) (cs : Constraints Pad Slot F)
    (hbuild : buildConstraints ts = some cs)
    (coordinate : Pad → Slot) (privateCoordinate : Fin nPrivate → Slot)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F)
    (witness : Slot → F) (hproducts : ProductsHold cs coordinate witness) :
    RowsHold (compile cs coordinate privateCoordinate publicWeights publicInputs privateWeights)
        witness ↔
      ClearAccepts (witness ∘ coordinate) 0 ts
        (dot (Sum.elim publicWeights privateWeights)
          (Sum.elim publicInputs (witness ∘ privateCoordinate))) := by
  rw [compile_correct cs coordinate privateCoordinate publicWeights publicInputs privateWeights
    witness hproducts]
  have h := buildConstraints_correct ts (witness ∘ coordinate)
    (dot (Sum.elim publicWeights privateWeights)
      (Sum.elim publicInputs (witness ∘ privateCoordinate)))
  simpa only [hbuild, Option.some.injEq, exists_eq_left'] using h

end LfzkV2
