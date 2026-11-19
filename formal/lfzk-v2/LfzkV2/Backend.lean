import LfzkV2.Compiler
import polygero.Local.Decoder

/-!
# The Polygero arithmetic boundary

The ordinary tableau holds the committed vector. Product tableau entries are
copies of the two claim pads and their product slot; explicit copy equations
tie them to that same vector. This file constructs the actual
`LigeroFamily.ConstraintSystem` consumed by Polygero and proves that satisfaction
implies all compiled linear rows and pad-product checks. It also connects the
existing Polygero row decoder to this implication.
-/

namespace LfzkV2.Backend

open SumcheckV2 LigeroFamily Classical

variable {F Pad Slot : Type} [Field F]

noncomputable def coefficients {ι : Type} (terms : List (ι × F)) (i : ι) : F :=
  (terms.map fun term => if i = term.1 then term.2 else 0).sum

theorem coefficients_dot {ι : Type} [Fintype ι] (terms : List (ι × F)) (values : ι → F) :
    dot (coefficients terms) values = (terms.map fun term => term.2 * values term.1).sum := by
  induction terms with
  | nil => simp [coefficients, dot]
  | cons term terms ih =>
      simp only [coefficients, List.map_cons, List.sum_cons, dot, add_mul, Finset.sum_add_distrib]
      rw [show (∑ i, (if i = term.1 then term.2 else 0) * values i) =
        term.2 * values term.1 by simp [ite_mul]]
      exact congrArg (fun x => term.2 * values term.1 + x) ih

abbrev Address (nw nq q : ℕ) := (block : CoreBlock) × (Fin (block.rowCount nw nq) × Fin q)

def read {nw nq q : ℕ} (core : CoreMessages F nw nq q) (address : Address nw nq q) : F :=
  core address.1 address.2.1 address.2.2

noncomputable def statement {nw nq q : ℕ} {Equation : Type}
    (rows : Equation → LinearRow (Address nw nq q) F) : ConstraintSystem F nw nq q Equation where
  coefficient e block row col := coefficients (rows e).terms ⟨block, row, col⟩
  target e := -(rows e).constant

theorem linearValue_eq {nw nq q : ℕ} {Equation : Type} [Fintype Equation]
    (rows : Equation → LinearRow (Address nw nq q) F) (core : CoreMessages F nw nq q)
    (e : Equation) :
    (statement rows).linearValue core e =
      ((rows e).terms.map fun term => term.2 * read core term.1).sum := by
  have h := coefficients_dot (rows e).terms (read core)
  simpa only [dot, Fintype.sum_sigma, Fintype.sum_prod_type, read,
    ConstraintSystem.linearValue, statement] using h

theorem statement_satisfies_iff {nw nq q : ℕ} {Equation : Type} [Fintype Equation]
    (rows : Equation → LinearRow (Address nw nq q) F) (core : CoreMessages F nw nq q) :
    (statement rows).Satisfies core ↔
      (∀ e, (rows e).eval (read core) = 0) ∧
        ∀ row col, core .left row col * core .right row col = core .output row col := by
  unfold ConstraintSystem.Satisfies
  apply and_congr_left
  intro _
  apply forall_congr'
  intro e
  rw [linearValue_eq]
  change _ = -(rows e).constant ↔ (rows e).constant + _ = 0
  exact (eq_neg_iff_add_eq_zero).trans (by rw [add_comm])

def remap {ι κ : Type} (row : LinearRow ι F) (coordinate : ι → κ) : LinearRow κ F :=
  ⟨row.constant, mapTerms row.terms coordinate⟩

theorem eval_remap {ι κ : Type} (row : LinearRow ι F) (coordinate : ι → κ)
    (values : κ → F) : (remap row coordinate).eval values = row.eval (values ∘ coordinate) := by
  simp [remap, mapTerms, PadExpression.eval, Function.comp_def]

inductive CopyKind where
  | left
  | right
  | product
  deriving DecidableEq, Fintype

def CopyKind.slot (kind : CopyKind) (c : LayerConstraint Pad Slot F) (coordinate : Pad → Slot) : Slot :=
  match kind with
  | .left => coordinate c.padA
  | .right => coordinate c.padB
  | .product => c.productSlot

def linearAddress {nw nq q : ℕ} (coordinate : Slot → Fin nw × Fin q) (slot : Slot) :
    Address nw nq q := ⟨.linear, coordinate slot⟩

def productAddress {nw nq q : ℕ} (position : Fin nq × Fin q) (kind : CopyKind) :
    Address nw nq q := by
  cases kind
  · exact ⟨.left, position⟩
  · exact ⟨.right, position⟩
  · exact ⟨.output, position⟩

def copyRow {nw nq q : ℕ} (c : LayerConstraint Pad Slot F) (coordinate : Pad → Slot)
    (primary : Slot → Fin nw × Fin q) (position : Fin nq × Fin q) (kind : CopyKind) :
    LinearRow (Address nw nq q) F :=
  ⟨0, [(productAddress position kind, 1),
    (linearAddress primary (kind.slot c coordinate), -1)]⟩

theorem eval_copyRow {nw nq q : ℕ} (c : LayerConstraint Pad Slot F) (coordinate : Pad → Slot)
    (primary : Slot → Fin nw × Fin q) (position : Fin nq × Fin q) (kind : CopyKind)
    (core : CoreMessages F nw nq q) :
    (copyRow c coordinate primary position kind).eval (read core) =
      read core (productAddress position kind) -
        read core (linearAddress primary (kind.slot c coordinate)) := by
  simp [copyRow, PadExpression.eval, sub_eq_add_neg]

abbrev Equation (rows products : ℕ) := Fin rows ⊕ (Fin products × CopyKind)

def rows {nw nq q : ℕ} (linear : List (LinearRow Slot F)) (cs : Constraints Pad Slot F)
    (coordinate : Pad → Slot) (primary : Slot → Fin nw × Fin q)
    (product : Fin cs.layers.length → Fin nq × Fin q) :
    Equation linear.length cs.layers.length → LinearRow (Address nw nq q) F
  | .inl i => remap (linear.get i) (linearAddress primary)
  | .inr (i, kind) => copyRow (cs.layers.get i) coordinate primary (product i) kind

/-- Backend satisfaction enforces the affine equations and the products on one
and the same committed vector. Product copies cannot be chosen independently. -/
theorem satisfies_compiled {nw nq q : ℕ} (linear : List (LinearRow Slot F))
    (cs : Constraints Pad Slot F) (coordinate : Pad → Slot)
    (primary : Slot → Fin nw × Fin q) (product : Fin cs.layers.length → Fin nq × Fin q)
    (core : CoreMessages F nw nq q)
    (hsat : (statement (rows linear cs coordinate primary product)).Satisfies core) :
    RowsHold linear (read core ∘ linearAddress primary) ∧
      ProductsHold cs coordinate (read core ∘ linearAddress primary) := by
  obtain ⟨hrows, hproducts⟩ := (statement_satisfies_iff _ core).mp hsat
  constructor
  · intro row hrow
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hrow
    have h := hrows (.inl i)
    change (remap (linear.get i) (linearAddress primary)).eval (read core) = 0 at h
    rwa [eval_remap, hi] at h
  · intro c hc
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hc
    have hcopy (kind : CopyKind) := hrows (.inr (i, kind))
    simp only [rows, eval_copyRow, sub_eq_zero, hi] at hcopy
    have hp := hproducts (product i).1 (product i).2
    change read core (productAddress (product i) .left) *
      read core (productAddress (product i) .right) =
      read core (productAddress (product i) .product) at hp
    rw [hcopy .left, hcopy .right, hcopy .product] at hp
    exact hp.symm

/-- The existing Polygero extractor returns a witness of this exact arithmetic
system. This theorem only states extraction validity, not its FS failure rate. -/
theorem decoded_compiled [Fintype F] [DecidableEq F]
    (I : RecursivePolygero.Instance F) (linear : List (LinearRow Slot F))
    (cs : Constraints Pad Slot F) (coordinate : Pad → Slot)
    (primary : Slot → Fin I.nw × Fin I.q)
    (product : Fin cs.layers.length → Fin I.nq × Fin I.q)
    (eqns : I.Equations ≃ Equation linear.length cs.layers.length)
    (oracle : I.layer.Oracle) (coin : I.layer.Coin) (response : I.layer.Payload)
    (g : (RecursivePolygero.Counting.tupleCounts I).Index)
    (hdecode : RecursivePolygero.scanRecoverAt I
      (statement (rows linear cs coordinate primary product ∘ eqns)) oracle coin response = some g) :
    RowsHold linear (read ((RecursivePolygero.Counting.tupleCounts I).witness g) ∘ linearAddress primary) ∧
      ProductsHold cs coordinate
        (read ((RecursivePolygero.Counting.tupleCounts I).witness g) ∘ linearAddress primary) := by
  have hs := RecursivePolygero.scanRecoverAt_valid I _ oracle coin response g hdecode
  apply satisfies_compiled linear cs coordinate primary product _
  obtain ⟨hl, hp⟩ := (statement_satisfies_iff _ _).mp hs
  exact (statement_satisfies_iff _ _).mpr ⟨fun e => by simpa using hl (eqns.symm e), hp⟩

end LfzkV2.Backend
