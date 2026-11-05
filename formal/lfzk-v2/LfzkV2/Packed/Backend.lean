import DualPacking.ArtinSchreierBackend
import LfzkV2.Backend
import LfzkV2.Native.Events

/-! The packing rows use the original committed vector, including its pad suffix.
They are ordinary Polygero equations; no separate packed witness or authentication
assumption is introduced at this boundary. -/

namespace LfzkV2.Packed

open Finset Module SumcheckV2 DualPacking DualPacking.ArtinSchreier
open scoped Classical

variable {K F I J Slot : Type} [Field K] [Fintype K] [Field F] [Fintype F]
  [Algebra K F] [Fintype I] [DecidableEq I] [Fintype J]

/-- Public coordinates and source equation, fixed before the packing challenge.
The target is affine in the already committed pad cells. -/
structure Statement (K F I J Slot : Type) [Field K] [Field F] [Algebra K F] where
  basis : Basis I K F
  pivot : I
  word : J → Slot
  mask : {i : I // i ≠ pivot} → Slot
  random : Slot
  frobeniusCell : Slot
  coefficients : J → I → F
  target : LinearRow Slot F

namespace Statement

variable (S : Statement K F I J Slot)

noncomputable def realize (values : Slot → F) : ArtinSchreier.Instance K F I J where
  basis := S.basis
  pivot := S.pivot
  words := values ∘ S.word
  coefficients := S.coefficients
  target := S.target.eval values
  masks := values ∘ S.mask
  r := values S.random
  b := values S.frobeniusCell

noncomputable def terms {A : Type} [Fintype A] (coordinate : A → Slot)
    (coefficient : A → F) : List (Slot × F) :=
  univ.toList.map fun a => (coordinate a, coefficient a)

omit [Fintype F] in
theorem eval_terms {A : Type} [Fintype A] (coordinate : A → Slot)
    (coefficient : A → F) (values : Slot → F) :
    ((terms coordinate coefficient).map fun t => t.2 * values t.1).sum =
      ∑ a, coefficient a * values (coordinate a) := by
  simp [terms, List.map_map, Function.comp_def]

noncomputable def targetCoefficient (delta : I → F) : F :=
  ∑ k, frobenius K F (delta k) * S.basis.traceDual k

noncomputable def wordCoefficient (delta : I → F) (j : J) : F :=
  ∑ k, frobenius K F (delta k) * coefficient S.basis S.coefficients j k

noncomputable def maskCoefficient (delta : I → F) (j : {i : I // i ≠ S.pivot}) : F :=
  delta j.1 + delta S.pivot * S.basis j.1

/-- `A = r + delta dot t`, after eliminating the dependent mask. -/
noncomputable def firstRow (delta : I → F) (A : F) : LinearRow Slot F :=
  ⟨-A, (S.random, 1) :: terms S.mask (S.maskCoefficient delta)⟩

/-- The trace equation, with the affine target expanded on its original cells. -/
noncomputable def secondRow (U delta : I → F) (A : F) : LinearRow Slot F :=
  ⟨frobenius K F A - (∑ k, frobenius K F (delta k) * U k) -
      S.targetCoefficient delta * S.target.constant,
    terms S.word (S.wordCoefficient delta) ++
      S.target.terms.map (fun t => (t.1, -(S.targetCoefficient delta * t.2))) ++
      terms S.mask (fun j => -S.maskCoefficient (fun k => frobenius K F (delta k)) j) ++
      [(S.frobeniusCell, -1)]⟩

noncomputable def rows (U delta : I → F) (A : F) : List (LinearRow Slot F) :=
  [S.firstRow delta A, S.secondRow U delta A]

omit [Fintype K] [Fintype F] [Fintype J] in
theorem firstRow_iff (values : Slot → F) (delta : I → F) (A : F) :
    (S.firstRow delta A).eval values = 0 ↔ (S.realize values).nativeOne delta A := by
  simp only [firstRow, PadExpression.eval, List.map_cons, List.sum_cons,
    one_mul, eval_terms, realize, ArtinSchreier.Instance.nativeOne,
    maskCoefficient, Function.comp_apply]
  constructor <;> intro h <;> linear_combination (norm := ring_nf) -h <;>
    simp only [add_comm, sub_eq_zero]
  all_goals
    apply Finset.sum_congr
    · ext x; simp
    · intro x _; rfl

theorem secondRow_iff (values : Slot → F) (U delta : I → F) (A : F) :
    (S.secondRow U delta A).eval values = 0 ↔ (S.realize values).nativeTwo U delta A := by
  have hterms (ts : List (Slot × F)) :
      (ts.map (fun t => -(S.targetCoefficient delta * t.2) * values t.1)).sum =
        -(S.targetCoefficient delta * (ts.map fun t => t.2 * values t.1).sum) := by
    induction ts with
    | nil => simp
    | cons t ts ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        ring
  simp only [secondRow, PadExpression.eval, List.map_append, List.sum_append,
    eval_terms, List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, neg_one_mul]
  rw [hterms]
  simp only [realize, ArtinSchreier.Instance.nativeTwo, ArtinSchreier.Instance.wordCoeff,
    ArtinSchreier.Instance.targetCoeff, PadExpression.eval, wordCoefficient,
    targetCoefficient, maskCoefficient, Function.comp_apply, neg_mul, sum_neg_distrib]
  constructor <;> intro h <;> linear_combination (norm := ring_nf) -h <;>
    simp only [add_comm, ← sub_eq_add_neg, sub_eq_zero]
  all_goals
    apply Finset.sum_congr
    · ext x; simp
    · intro x _; rfl

/-- Algebraic equivalence of the actual two authenticated rows. In particular,
the optional `b = sigma(r)` check is not smuggled into backend satisfaction. -/
theorem rows_iff_native (values : Slot → F) (U delta : I → F) (A : F)
    (htrace : ∀ k, traceF K (U k) = 0) :
    RowsHold (S.rows U delta A) values ↔ (S.realize values).nativeLinearVerify U delta A := by
  simp [RowsHold, rows, firstRow_iff, secondRow_iff,
    ArtinSchreier.Instance.nativeLinearVerify, htrace]

/-- Both reductions read the same committed cells. Product checks remain
separate from the affine rows, exactly as in the runtime. -/
theorem rows_and_products {Pad : Type} (cs : Constraints Pad Slot F)
    (coordinate : Pad → Slot) (values : Slot → F) (U delta : I → F) (A : F)
    (htrace : ∀ k, traceF K (U k) = 0)
    (hrows : RowsHold
      (cs.layers.map (fun c => compileLayer c coordinate) ++ S.rows U delta A) values)
    (hproducts : ProductsHold cs coordinate values) :
    (S.realize values).nativeLinearVerify U delta A ∧
      (∀ c ∈ cs.layers, c.Holds (values ∘ coordinate)) := by
  have hr : RowsHold (S.rows U delta A) values := by
    intro row hrow
    exact hrows row (List.mem_append_right _ hrow)
  refine ⟨(S.rows_iff_native values U delta A htrace).mp hr, ?_⟩
  intro c hc
  have hl := hrows (compileLayer c coordinate)
    (List.mem_append_left _ (List.mem_map.mpr ⟨c,hc,rfl⟩))
  rw [eval_compileLayer, sub_eq_zero, hproducts c hc] at hl
  exact hl

/-- The implication used for every member of Polygero's fixed candidate list. -/
theorem satisfies_rows {Pad : Type} {nw nq q : ℕ}
    (cs : Constraints Pad Slot F) (coordinate : Pad → Slot)
    (primary : Slot → Fin nw × Fin q)
    (product : Fin cs.layers.length → Fin nq × Fin q)
    (U delta : I → F) (A : F) (core : LigeroFamily.CoreMessages F nw nq q)
    (htrace : ∀ k, traceF K (U k) = 0)
    (hsat : (Backend.statement (Backend.rows
      (cs.layers.map (fun c => compileLayer c coordinate) ++ S.rows U delta A)
      cs coordinate primary product)).Satisfies core) :
    let values := Backend.read core ∘ Backend.linearAddress primary
    (S.realize values).nativeLinearVerify U delta A ∧
      (∀ c ∈ cs.layers, c.Holds (values ∘ coordinate)) := by
  intro values
  have h := Backend.satisfies_compiled _ cs coordinate primary product core hsat
  exact S.rows_and_products cs coordinate values U delta A htrace h.1 h.2

/-- The existing Polygero witness extractor supplies both packing equations and
the unchanged sumcheck layer/product equations on exactly the same vector. -/
theorem decoded_rows {Pad : Type} [DecidableEq F]
    (B : RecursivePolygero.Instance F) (cs : Constraints Pad Slot F)
    (coordinate : Pad → Slot) (primary : Slot → Fin B.nw × Fin B.q)
    (product : Fin cs.layers.length → Fin B.nq × Fin B.q)
    (U delta : I → F) (A : F)
    (eqns : B.Equations ≃ Backend.Equation
      (cs.layers.map (fun c => compileLayer c coordinate) ++ S.rows U delta A).length
      cs.layers.length)
    (oracle : B.layer.Oracle) (coin : B.layer.Coin) (response : B.layer.Payload)
    (g : (RecursivePolygero.Counting.tupleCounts B).Index)
    (htrace : ∀ k, traceF K (U k) = 0)
    (hdecode : RecursivePolygero.scanRecoverAt B
      (Backend.statement (Backend.rows
        (cs.layers.map (fun c => compileLayer c coordinate) ++ S.rows U delta A)
        cs coordinate primary product ∘ eqns)) oracle coin response = some g) :
    let values := Backend.read ((RecursivePolygero.Counting.tupleCounts B).witness g) ∘
      Backend.linearAddress primary
    (S.realize values).nativeLinearVerify U delta A ∧
      (∀ c ∈ cs.layers, c.Holds (values ∘ coordinate)) := by
  intro values
  have h := Backend.decoded_compiled B _ cs coordinate primary product eqns
    oracle coin response g hdecode
  exact S.rows_and_products cs coordinate values U delta A htrace h.1 h.2

end Statement
end LfzkV2.Packed
