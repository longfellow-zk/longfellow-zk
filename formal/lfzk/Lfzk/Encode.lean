import Lfzk.LigeroSystem
import LigeroFamily.Protocol.Basic

open Sumcheck

/-!
# Encoding a `LigeroSystem` as a `LigeroFamily.ConstraintSystem`

`lfzk` states its two Ligero assumptions over `LigeroSystem ninp M F` — a list of linear rows on
the committed columns and the pad, plus a list of *arbitrary* pad triples `pad z = pad x * pad y`.
The proved analysis in `ligero/` states everything over `ConstraintSystem F nw nq w Equations` — a
tableau of `nw` linear rows and `nq` quadratic rows, each `w` wide, whose quadratic constraints are
**positional**: `msgs .left row i * msgs .right row i = msgs .output row i`.

This file is the translation, and it is the whole of the impedance mismatch between the two
developments.  Everything else in the wiring is assembly.

## The two design decisions

**The packing is a parameter.**  `Placement` carries an arbitrary injective map from lfzk's
`ninp + M` scalars into the linear block, and an arbitrary injective map from triple indices into
quadratic cells.  Nothing below uses anything about those maps except injectivity, so the
correctness of the bridge is independent of how densely the tableau is packed.  `w = 1`,
`nw = ninp + M`, `nq = nt` is a legal `Placement`; so is any denser one, at no proof cost.  Since
neither `nw` nor `nq` nor `Fintype.card Equations` appears in `selectedMCASoundnessBound`, the
packing is free in the soundness error and costs only prover work.

**Triples get copy rows.**  lfzk's triples name arbitrary pad indices and *do* repeat — consecutive
layers share the claim-pad triple (`claim_pad_overlap`, `ZkHiding.lean`) — so no injective
placement can align a pad slot with the quadratic cell that must hold it.  Instead triple `j` is
given its own quadratic cell and three equations tie that cell's three components back to the
linear cells holding `pad x`, `pad y`, `pad z`.

## Why rows are indexed by `Fin` rather than by a list

`buildSystemMulti`'s row count varies with the run (`hnl : ∀ ω, (T ω).length ≤ nl`), but
`Equations` must be one fixed type for ligero's theorems to apply to a single statement type.  So
the rows come in as `Fin nlin → LigeroRow` and the triples as `Fin nt → Option _`, with `none`
and the zero row available as padding.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.Encode

open LigeroFamily

variable {F : Type} [Field F] {ninp M w nw nq nt nlin : ℕ}

/-! ## The placement -/

/-- Where lfzk's scalars and triples live in the tableau.

`cell` places the `ninp` committed columns and the `M` pad slots into the linear block; `qcell`
gives triple `j` its own cell in the quadratic blocks.  Both are injective and nothing else about
them is ever used. -/
structure Placement (ninp M w nw nq nt : ℕ) where
  cell : Fin ninp ⊕ Fin M → Fin nw × Fin w
  cell_inj : Function.Injective cell
  qcell : Fin nt → Fin nq × Fin w
  qcell_inj : Function.Injective qcell

/-- The three quadratic blocks, as a type of their own.

`CoreBlock` has a fourth constructor, and indexing the copy equations by it would leave a
degenerate `.linear` case in every definition and every case split below.  `QSide` is the
three-element index the copy rows actually range over. -/
inductive QSide
  | left
  | right
  | output
  deriving DecidableEq, Fintype

/-- Read a tableau at one of the three quadratic blocks.  Stated by matching on the side rather
than as `msgs side.block`, so that the row index is `Fin nq` without a dependent rewrite. -/
def qval {F : Type} {nw nq w : ℕ} (msgs : CoreMessages F nw nq w) : QSide → Fin nq → Fin w → F
  | .left => msgs .left
  | .right => msgs .right
  | .output => msgs .output

/-- The pad index a triple contributes on a given side. -/
def QSide.slot {M : ℕ} (t : Fin M × Fin M × Fin M) : QSide → Fin M
  | .left => t.1
  | .right => t.2.1
  | .output => t.2.2

/-! ## Summing over the four blocks -/

/-- `∑ b : CoreBlock` unfolded.  `CoreBlock` is a four-constructor enumeration, so this is `rfl`
up to the order `deriving Fintype` picks. -/
lemma sum_coreBlock {A : Type} [AddCommMonoid A] (f : CoreBlock → A) :
    ∑ b : CoreBlock, f b = f .linear + f .left + f .right + f .output := by
  have huniv : (Finset.univ : Finset CoreBlock)
      = {CoreBlock.linear, CoreBlock.left, CoreBlock.right, CoreBlock.output} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

/-! ## Spreading a vector over the cells

`spread` is the inverse of `Placement.cell`: it reads the value belonging to a cell, and returns
`0` at cells no scalar was placed in.  It is used twice — once to build the tableau from an
lfzk assignment (`embed`), and once to build a row's coefficient vector (`rowCoeff`). -/

open Classical in
/-- The value at a linear cell: the scalar placed there, or `0`. -/
noncomputable def spread (pl : Placement ninp M w nw nq nt) (v : Fin ninp ⊕ Fin M → F)
    (c : Fin nw × Fin w) : F :=
  if h : ∃ s, pl.cell s = c then v (Classical.choose h) else 0

/-- The defining property of `spread`, and the only one used: injectivity of `cell` makes the
classical choice the placed scalar. -/
@[simp] lemma spread_cell (pl : Placement ninp M w nw nq nt) (v : Fin ninp ⊕ Fin M → F)
    (s : Fin ninp ⊕ Fin M) : spread pl v (pl.cell s) = v s := by
  classical
  have h : ∃ s', pl.cell s' = pl.cell s := ⟨s, rfl⟩
  rw [spread, dif_pos h]
  exact congrArg v (pl.cell_inj (Classical.choose_spec h))

open Classical in
/-- The value at a quadratic cell: the relevant component of the triple placed there, or `0`. -/
noncomputable def qspread (pl : Placement ninp M w nw nq nt)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) (v : Fin ninp ⊕ Fin M → F)
    (side : QSide) (c : Fin nq × Fin w) : F :=
  if h : ∃ j, pl.qcell j = c then
    match tri (Classical.choose h) with
    | none => 0
    | some t => v (.inr (side.slot t))
  else 0

@[simp] lemma qspread_qcell (pl : Placement ninp M w nw nq nt)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) (v : Fin ninp ⊕ Fin M → F)
    (side : QSide) (j : Fin nt) :
    qspread pl tri v side (pl.qcell j)
      = match tri j with
        | none => 0
        | some t => v (.inr (side.slot t)) := by
  classical
  have h : ∃ j', pl.qcell j' = pl.qcell j := ⟨j, rfl⟩
  have hj : Classical.choose h = j := pl.qcell_inj (Classical.choose_spec h)
  rw [qspread, dif_pos h, hj]

/-- A quadratic cell no triple was placed in holds `0` on every side. -/
lemma qspread_of_not_mem (pl : Placement ninp M w nw nq nt)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) (v : Fin ninp ⊕ Fin M → F)
    (side : QSide) {c : Fin nq × Fin w} (hc : ¬ ∃ j, pl.qcell j = c) :
    qspread pl tri v side c = 0 := by
  rw [qspread, dif_neg hc]

/-! ## The tableau built from an lfzk assignment -/

/-- The `CoreMessages` an lfzk assignment `v = wcol ⊕ pad` produces: the scalars in the linear
block at their cells, each triple's three pad values in the three quadratic blocks at its cell,
and `0` everywhere else.  Unused quadratic cells hold `0`, which satisfies `0 * 0 = 0`. -/
noncomputable def embed (pl : Placement ninp M w nw nq nt)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) (v : Fin ninp ⊕ Fin M → F) :
    CoreMessages F nw nq w
  | .linear => fun r c => spread pl v (r, c)
  | .left => fun r c => qspread pl tri v .left (r, c)
  | .right => fun r c => qspread pl tri v .right (r, c)
  | .output => fun r c => qspread pl tri v .output (r, c)

/-- `embed` at a quadratic block, uniformly in the side. -/
@[simp] lemma qval_embed (pl : Placement ninp M w nw nq nt)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) (v : Fin ninp ⊕ Fin M → F)
    (side : QSide) (r : Fin nq) (c : Fin w) :
    qval (embed pl tri v) side r c = qspread pl tri v side (r, c) := by
  cases side <;> rfl

/-- Read an lfzk assignment back out of a tableau.  Only the linear block is read, so an
extractor's values at the quadratic cells are irrelevant — the copy rows are what tie them
down. -/
def decodeVec (pl : Placement ninp M w nw nq nt) (msgs : CoreMessages F nw nq w) :
    Fin ninp ⊕ Fin M → F :=
  fun s => msgs .linear (pl.cell s).1 (pl.cell s).2

@[simp] lemma decodeVec_embed (pl : Placement ninp M w nw nq nt)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) (v : Fin ninp ⊕ Fin M → F) :
    decodeVec pl (embed pl tri v) = v := by
  funext s
  show spread pl v ((pl.cell s).1, (pl.cell s).2) = v s
  rw [Prod.mk.eta, spread_cell]

/-! ## Two sums over the tableau

`ConstraintSystem.linearValue` is `∑ block, ∑ row, ∑ i`.  Both kinds of equation this file emits
are supported on few cells, so both sums collapse; these two lemmas are where that happens. -/

/-- A coefficient supported on the image of `cell` sums to the corresponding sum over lfzk's own
index type.  This is the only place `cell_inj` does real work. -/
lemma sum_spread (pl : Placement ninp M w nw nq nt) (v : Fin ninp ⊕ Fin M → F)
    (g : Fin nw → Fin w → F) :
    ∑ r : Fin nw, ∑ c : Fin w, spread pl v (r, c) * g r c
      = ∑ s : Fin ninp ⊕ Fin M, v s * g (pl.cell s).1 (pl.cell s).2 := by
  classical
  have hprod : ∑ r : Fin nw, ∑ c : Fin w, spread pl v (r, c) * g r c
      = ∑ p : Fin nw × Fin w, spread pl v p * g p.1 p.2 :=
    (Fintype.sum_prod_type (f := fun p : Fin nw × Fin w => spread pl v p * g p.1 p.2)).symm
  have himage : ∑ p ∈ Finset.univ.image pl.cell, spread pl v p * g p.1 p.2
      = ∑ s : Fin ninp ⊕ Fin M, v s * g (pl.cell s).1 (pl.cell s).2 := by
    rw [Finset.sum_image (fun a _ b _ h => pl.cell_inj h)]
    exact Finset.sum_congr rfl (fun s _ => by rw [spread_cell])
  have hfull : ∑ p ∈ Finset.univ.image pl.cell, spread pl v p * g p.1 p.2
      = ∑ p : Fin nw × Fin w, spread pl v p * g p.1 p.2 := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro p _ hp
    have hne : ¬ ∃ s, pl.cell s = p := by
      rintro ⟨s, rfl⟩
      exact hp (Finset.mem_image_of_mem _ (Finset.mem_univ s))
    rw [spread, dif_neg hne, zero_mul]
  rw [hprod, ← hfull, himage]

/-- A coefficient supported on one cell picks that cell out. -/
lemma sum_single {m : ℕ} (a : F) (p : Fin m × Fin w) (g : Fin m → Fin w → F) :
    ∑ r : Fin m, ∑ c : Fin w, (if (r, c) = p then a else 0) * g r c = a * g p.1 p.2 := by
  classical
  rw [← Fintype.sum_prod_type
    (f := fun q : Fin m × Fin w => (if q = p then a else 0) * g q.1 q.2)]
  simp

/-! ## The coefficients

Two shapes of equation, and each is defined block by block so that the row index is
`Fin nw` or `Fin nq` definitionally and no dependent rewriting is ever needed. -/

/-- An lfzk linear row, as a tableau coefficient: its `cw`/`cp` entries at their cells in the
linear block, and zero on the quadratic blocks. -/
noncomputable def rowCoeff (pl : Placement ninp M w nw nq nt) (row : LigeroRow ninp M F) :
    (b : CoreBlock) → Fin (b.rowCount nw nq) → Fin w → F
  | .linear => fun r c => spread pl (Sum.elim row.cw row.cp) (r, c)
  | .left | .right | .output => fun _ _ => 0

/-- One copy equation: `+1` at quadratic cell `qc` of block `side`, `-1` at linear cell `lc`,
zero elsewhere.  Read against a tableau it says "the `side` component of this triple's cell equals
the pad slot placed at `lc`". -/
def copyCoeff (side : QSide) (lc : Fin nw × Fin w) (qc : Fin nq × Fin w) :
    (b : CoreBlock) → Fin (b.rowCount nw nq) → Fin w → F
  | .linear => fun r c => if (r, c) = lc then -1 else 0
  | .left => fun r c => if side = .left ∧ (r, c) = qc then 1 else 0
  | .right => fun r c => if side = .right ∧ (r, c) = qc then 1 else 0
  | .output => fun r c => if side = .output ∧ (r, c) = qc then 1 else 0

/-- Triple `j`'s copy equation on one side, or the trivial equation if slot `j` carries no
triple.  Factored out of `encodeSystem` so the `Option` match is on an argument rather than
under a structure field, which is what makes `copyRow_some` a `rfl` lemma. -/
noncomputable def copyRow (pl : Placement ninp M w nw nq nt) (j : Fin nt) (side : QSide) :
    Option (Fin M × Fin M × Fin M) → (b : CoreBlock) → Fin (b.rowCount nw nq) → Fin w → F
  | none => fun _ _ _ => 0
  | some t => copyCoeff side (pl.cell (.inr (side.slot t))) (pl.qcell j)

@[simp] lemma copyRow_none (pl : Placement ninp M w nw nq nt) (j : Fin nt) (side : QSide) :
    copyRow (F := F) pl j side none = fun _ _ _ => 0 := rfl

@[simp] lemma copyRow_some (pl : Placement ninp M w nw nq nt) (j : Fin nt) (side : QSide)
    (t : Fin M × Fin M × Fin M) :
    copyRow (F := F) pl j side (some t)
      = copyCoeff side (pl.cell (.inr (side.slot t))) (pl.qcell j) := rfl

/-- The whole system: one equation per lfzk linear row, three copy equations per triple. -/
noncomputable def encodeSystem (pl : Placement ninp M w nw nq nt)
    (lin : Fin nlin → LigeroRow ninp M F)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) :
    ConstraintSystem F nw nq w (Fin nlin ⊕ (Fin nt × QSide)) where
  coefficient
    | .inl e => rowCoeff pl (lin e)
    | .inr (j, side) => copyRow pl j side (tri j)
  target
    | .inl e => (lin e).rhs
    | .inr _ => 0

/-! ## What the two equation shapes evaluate to -/

/-- A linear row's equation reads exactly lfzk's row, against the decoded assignment. -/
lemma linearValue_rowCoeff (pl : Placement ninp M w nw nq nt) (row : LigeroRow ninp M F)
    (msgs : CoreMessages F nw nq w) :
    (∑ b : CoreBlock, ∑ r : Fin (b.rowCount nw nq), ∑ c : Fin w,
        rowCoeff pl row b r c * msgs b r c)
      = (∑ i, row.cw i * decodeVec pl msgs (.inl i))
        + (∑ j, row.cp j * decodeVec pl msgs (.inr j)) := by
  rw [sum_coreBlock]
  have hzero : ∀ (b : CoreBlock) (_ : b ≠ .linear),
      (∑ r : Fin (b.rowCount nw nq), ∑ c : Fin w, rowCoeff pl row b r c * msgs b r c) = 0 := by
    intro b hb
    cases b with
    | linear => exact absurd rfl hb
    | left | right | output => simp [rowCoeff]
  rw [hzero .left (by simp), hzero .right (by simp), hzero .output (by simp)]
  simp only [add_zero]
  rw [show (∑ r : Fin ((CoreBlock.linear).rowCount nw nq), ∑ c : Fin w,
      rowCoeff pl row .linear r c * msgs .linear r c)
      = ∑ r : Fin nw, ∑ c : Fin w,
          spread pl (Sum.elim row.cw row.cp) (r, c) * msgs .linear r c from rfl]
  rw [sum_spread]
  exact Fintype.sum_sum_type _

/-- One quadratic block's contribution to a copy equation: the cell if this is the side the
equation is about, and nothing otherwise. -/
lemma sum_qblock (side other : QSide) (qc : Fin nq × Fin w) (g : Fin nq → Fin w → F) :
    (∑ r : Fin nq, ∑ c : Fin w, (if side = other ∧ (r, c) = qc then (1 : F) else 0) * g r c)
      = if side = other then g qc.1 qc.2 else 0 := by
  by_cases h : side = other
  · simp only [h, true_and, if_true]
    rw [sum_single]
    ring
  · simp [h]

/-- A copy equation reads the difference of the two cells it ties together. -/
lemma linearValue_copyCoeff (side : QSide) (lc : Fin nw × Fin w) (qc : Fin nq × Fin w)
    (msgs : CoreMessages F nw nq w) :
    (∑ b : CoreBlock, ∑ r : Fin (b.rowCount nw nq), ∑ c : Fin w,
        copyCoeff side lc qc b r c * msgs b r c)
      = qval msgs side qc.1 qc.2 - msgs .linear lc.1 lc.2 := by
  rw [sum_coreBlock]
  have hlin : (∑ r : Fin ((CoreBlock.linear).rowCount nw nq), ∑ c : Fin w,
      copyCoeff side lc qc .linear r c * msgs .linear r c) = -msgs .linear lc.1 lc.2 := by
    rw [show (∑ r : Fin ((CoreBlock.linear).rowCount nw nq), ∑ c : Fin w,
        copyCoeff side lc qc .linear r c * msgs .linear r c)
        = ∑ r : Fin nw, ∑ c : Fin w,
            (if (r, c) = lc then (-1 : F) else 0) * msgs .linear r c from rfl]
    rw [sum_single]
    ring
  rw [hlin,
    show (∑ r : Fin ((CoreBlock.left).rowCount nw nq), ∑ c : Fin w,
        copyCoeff side lc qc .left r c * msgs .left r c)
      = ∑ r : Fin nq, ∑ c : Fin w,
          (if side = QSide.left ∧ (r, c) = qc then (1 : F) else 0) * msgs .left r c from rfl,
    show (∑ r : Fin ((CoreBlock.right).rowCount nw nq), ∑ c : Fin w,
        copyCoeff side lc qc .right r c * msgs .right r c)
      = ∑ r : Fin nq, ∑ c : Fin w,
          (if side = QSide.right ∧ (r, c) = qc then (1 : F) else 0) * msgs .right r c from rfl,
    show (∑ r : Fin ((CoreBlock.output).rowCount nw nq), ∑ c : Fin w,
        copyCoeff side lc qc .output r c * msgs .output r c)
      = ∑ r : Fin nq, ∑ c : Fin w,
          (if side = QSide.output ∧ (r, c) = qc then (1 : F) else 0) * msgs .output r c from rfl,
    sum_qblock, sum_qblock, sum_qblock]
  cases side <;> simp [qval] <;> ring

/-! ## The two directions

`RowsSat` is lfzk's `LigeroSystem.Sat` on the `Fin`-indexed row data, with the assignment carried
as one function on `Fin ninp ⊕ Fin M` rather than as a pair. -/

/-- lfzk's satisfaction predicate, on `Fin`-indexed rows. -/
def RowsSat (lin : Fin nlin → LigeroRow ninp M F)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) (v : Fin ninp ⊕ Fin M → F) : Prop :=
  (∀ e, (∑ i, (lin e).cw i * v (.inl i)) + (∑ j, (lin e).cp j * v (.inr j)) = (lin e).rhs) ∧
  (∀ j t, tri j = some t → v (.inr t.2.2) = v (.inr t.1) * v (.inr t.2.1))

lemma encodeSystem_coeff_inl (pl : Placement ninp M w nw nq nt)
    (lin : Fin nlin → LigeroRow ninp M F)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) (e : Fin nlin) :
    (encodeSystem pl lin tri).coefficient (.inl e) = rowCoeff pl (lin e) := rfl

lemma encodeSystem_coeff_inr (pl : Placement ninp M w nw nq nt)
    (lin : Fin nlin → LigeroRow ninp M F)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) (j : Fin nt) (side : QSide) :
    (encodeSystem pl lin tri).coefficient (.inr (j, side)) = copyRow pl j side (tri j) := rfl

lemma encodeSystem_target_inr (pl : Placement ninp M w nw nq nt)
    (lin : Fin nlin → LigeroRow ninp M F)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) (j : Fin nt) (side : QSide) :
    (encodeSystem pl lin tri).target (.inr (j, side)) = 0 := rfl

/--
**Soundness direction.**  Anything satisfying the encoded system decodes to an assignment
satisfying lfzk's rows.

This is the direction the extraction bridge consumes: ligero's extractor returns a `CoreMessages`,
and this turns it into the `(wcol, pad)` pair `IsLigeroSound.sound` has to produce.  Note what it
does *not* assume about `msgs` — the quadratic cells may hold anything; the copy equations are
what pin them to the pad.
-/
theorem rowsSat_of_satisfies (pl : Placement ninp M w nw nq nt)
    (lin : Fin nlin → LigeroRow ninp M F)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) (msgs : CoreMessages F nw nq w)
    (h : (encodeSystem pl lin tri).Satisfies msgs) :
    RowsSat lin tri (decodeVec pl msgs) := by
  obtain ⟨hlin, hquad⟩ := h
  constructor
  · intro e
    have h1 := hlin (.inl e)
    rw [show (encodeSystem pl lin tri).linearValue msgs (.inl e)
        = ∑ b : CoreBlock, ∑ r : Fin (b.rowCount nw nq), ∑ c : Fin w,
            rowCoeff pl (lin e) b r c * msgs b r c from rfl,
      linearValue_rowCoeff] at h1
    exact h1
  · intro j t htri
    -- each copy equation identifies one quadratic cell with one linear cell
    have hside : ∀ side : QSide,
        qval msgs side (pl.qcell j).1 (pl.qcell j).2 = decodeVec pl msgs (.inr (side.slot t)) := by
      intro side
      have h1 := hlin (.inr (j, side))
      rw [show (encodeSystem pl lin tri).linearValue msgs (.inr (j, side))
          = ∑ b : CoreBlock, ∑ r : Fin (b.rowCount nw nq), ∑ c : Fin w,
              (encodeSystem pl lin tri).coefficient (.inr (j, side)) b r c * msgs b r c from rfl,
        encodeSystem_coeff_inr, htri, copyRow_some, linearValue_copyCoeff,
        encodeSystem_target_inr, sub_eq_zero] at h1
      exact h1
    -- `QSide.slot t .left` is `t.1` definitionally, so these retypings are free
    have hL : msgs .left (pl.qcell j).1 (pl.qcell j).2 = decodeVec pl msgs (.inr t.1) :=
      hside .left
    have hR : msgs .right (pl.qcell j).1 (pl.qcell j).2 = decodeVec pl msgs (.inr t.2.1) :=
      hside .right
    have hO : msgs .output (pl.qcell j).1 (pl.qcell j).2 = decodeVec pl msgs (.inr t.2.2) :=
      hside .output
    have hprod := hquad (pl.qcell j).1 (pl.qcell j).2
    rw [← hL, ← hR, ← hO]
    exact hprod.symm

/--
**Completeness direction.**  An lfzk assignment satisfying the rows embeds to a tableau
satisfying the encoded system.

This is the direction the zero-knowledge bridge consumes: `IsLigeroZeroKnowledge.close` is
hypothesised on `cs.Sat wcol pad`, and ligero's zero-knowledge theorem is hypothesised on
`statement.Satisfies messages`.
-/
theorem satisfies_of_rowsSat (pl : Placement ninp M w nw nq nt)
    (lin : Fin nlin → LigeroRow ninp M F)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) (v : Fin ninp ⊕ Fin M → F)
    (h : RowsSat lin tri v) :
    (encodeSystem pl lin tri).Satisfies (embed pl tri v) := by
  obtain ⟨hlin, hquad⟩ := h
  constructor
  · rintro (e | ⟨j, side⟩)
    · rw [show (encodeSystem pl lin tri).linearValue (embed pl tri v) (.inl e)
          = ∑ b : CoreBlock, ∑ r : Fin (b.rowCount nw nq), ∑ c : Fin w,
              rowCoeff pl (lin e) b r c * embed pl tri v b r c from rfl,
        linearValue_rowCoeff, decodeVec_embed]
      exact hlin e
    · rw [show (encodeSystem pl lin tri).linearValue (embed pl tri v) (.inr (j, side))
          = ∑ b : CoreBlock, ∑ r : Fin (b.rowCount nw nq), ∑ c : Fin w,
              (encodeSystem pl lin tri).coefficient (.inr (j, side)) b r c
                * embed pl tri v b r c from rfl,
        encodeSystem_coeff_inr, encodeSystem_target_inr]
      cases htri : tri j with
      | none => simp
      | some t =>
        rw [copyRow_some, linearValue_copyCoeff]
        have e1 : qval (embed pl tri v) side (pl.qcell j).1 (pl.qcell j).2
            = v (.inr (side.slot t)) := by
          rw [qval_embed, Prod.mk.eta, qspread_qcell, htri]
        have e2 : embed pl tri v .linear (pl.cell (.inr (side.slot t))).1
              (pl.cell (.inr (side.slot t))).2 = v (.inr (side.slot t)) := by
          show spread pl v ((pl.cell (.inr (side.slot t))).1,
            (pl.cell (.inr (side.slot t))).2) = _
          rw [Prod.mk.eta, spread_cell]
        rw [e1, e2, sub_self]
  · intro r c
    show qspread pl tri v .left (r, c) * qspread pl tri v .right (r, c)
      = qspread pl tri v .output (r, c)
    by_cases hc : ∃ j, pl.qcell j = (r, c)
    · obtain ⟨j, hj⟩ := hc
      rw [← hj, qspread_qcell, qspread_qcell, qspread_qcell]
      cases htri : tri j with
      | none => simp
      | some t => exact (hquad j t htri).symm
    · rw [qspread_of_not_mem _ _ _ _ hc, qspread_of_not_mem _ _ _ _ hc,
        qspread_of_not_mem _ _ _ _ hc, mul_zero]

/-! ## Back to lfzk's own `LigeroSystem`

The two theorems above are stated on `Fin`-indexed row data because `Equations` has to be one
fixed type while `buildSystemMulti`'s row count varies with the run.  This section connects that
form to `LigeroSystem.Sat`, with padding allowed in both directions. -/

/-- The padding row: satisfied by every assignment, so it may fill unused linear slots. -/
def zeroRow (ninp M : ℕ) (F : Type) [Field F] : LigeroRow ninp M F :=
  { cw := fun _ => 0, cp := fun _ => 0, rhs := 0 }

/-- Every emitted slot carries something `S` implies: a row of `S` or the zero row, a triple of
`S` or nothing.  This is all the *completeness* direction needs, and it holds of a truncating
presentation with no length side condition — which is what lets the zero-knowledge bridge quantify
over every `LigeroSystem`. -/
structure Covers (S : LigeroSystem ninp M F) (lin : Fin nlin → LigeroRow ninp M F)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) : Prop where
  lin_mem : ∀ e, lin e ∈ S.linear ∨ lin e = zeroRow ninp M F
  tri_mem : ∀ j t, tri j = some t → t ∈ S.quad

/-- Every row and triple of `S` occupies some slot.  This is what the *soundness* direction
needs, and it is where the length side conditions live. -/
structure Reaches (S : LigeroSystem ninp M F) (lin : Fin nlin → LigeroRow ninp M F)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) : Prop where
  lin_cov : ∀ row ∈ S.linear, ∃ e, lin e = row
  tri_cov : ∀ t ∈ S.quad, ∃ j, tri j = some t

/-- Half of the translation: `S`'s satisfaction implies the emitted rows'. -/
theorem rowsSat_of_sat {S : LigeroSystem ninp M F} {lin : Fin nlin → LigeroRow ninp M F}
    {tri : Fin nt → Option (Fin M × Fin M × Fin M)} (hc : Covers S lin tri)
    {wcol : Fin ninp → F} {pad : Fin M → F} (h : S.Sat wcol pad) :
    RowsSat lin tri (Sum.elim wcol pad) := by
  obtain ⟨hlin, hquad⟩ := h
  refine ⟨fun e => ?_, fun j t htri => ?_⟩
  · rcases hc.lin_mem e with hm | hm
    · simpa [LigeroRow.Sat] using hlin (lin e) hm
    · rw [hm]
      simp [zeroRow]
  · simpa using hquad t (hc.tri_mem j t htri)

/-- The other half: the emitted rows' satisfaction implies `S`'s. -/
theorem sat_of_rowsSat {S : LigeroSystem ninp M F} {lin : Fin nlin → LigeroRow ninp M F}
    {tri : Fin nt → Option (Fin M × Fin M × Fin M)} (hr : Reaches S lin tri)
    {wcol : Fin ninp → F} {pad : Fin M → F} (h : RowsSat lin tri (Sum.elim wcol pad)) :
    S.Sat wcol pad := by
  obtain ⟨hlin, hquad⟩ := h
  refine ⟨fun row hrow => ?_, fun t ht => ?_⟩
  · obtain ⟨e, he⟩ := hr.lin_cov row hrow
    have he' := hlin e
    rw [he] at he'
    simpa [LigeroRow.Sat] using he'
  · obtain ⟨j, hj⟩ := hr.tri_cov t ht
    simpa using hquad j t hj

/-- The extracted assignment, in the pair form `IsLigeroSound` uses. -/
def decode (pl : Placement ninp M w nw nq nt) (msgs : CoreMessages F nw nq w) :
    LigeroAssignment ninp M F :=
  (fun i => decodeVec pl msgs (.inl i), fun j => decodeVec pl msgs (.inr j))

omit [Field F] in
@[simp] lemma elim_decode (pl : Placement ninp M w nw nq nt) (msgs : CoreMessages F nw nq w) :
    Sum.elim (decode pl msgs).1 (decode pl msgs).2 = decodeVec pl msgs := by
  funext s
  cases s <;> rfl

/--
**The soundness bridge, at lfzk's own types.**  A tableau satisfying the encoded system decodes
to an assignment satisfying `S`.
-/
theorem sat_decode_of_satisfies (pl : Placement ninp M w nw nq nt) {S : LigeroSystem ninp M F}
    {lin : Fin nlin → LigeroRow ninp M F} {tri : Fin nt → Option (Fin M × Fin M × Fin M)}
    (hr : Reaches S lin tri) (msgs : CoreMessages F nw nq w)
    (h : (encodeSystem pl lin tri).Satisfies msgs) :
    S.Sat (decode pl msgs).1 (decode pl msgs).2 := by
  refine sat_of_rowsSat hr ?_
  rw [elim_decode]
  exact rowsSat_of_satisfies pl lin tri msgs h

/--
**The zero-knowledge bridge, at lfzk's own types.**  An assignment satisfying `S` embeds to a
tableau satisfying the encoded system.
-/
theorem satisfies_embed_of_sat (pl : Placement ninp M w nw nq nt) {S : LigeroSystem ninp M F}
    {lin : Fin nlin → LigeroRow ninp M F} {tri : Fin nt → Option (Fin M × Fin M × Fin M)}
    (hc : Covers S lin tri) (wcol : Fin ninp → F) (pad : Fin M → F)
    (h : S.Sat wcol pad) :
    (encodeSystem pl lin tri).Satisfies (embed pl tri (Sum.elim wcol pad)) :=
  satisfies_of_rowsSat pl lin tri _ (rowsSat_of_sat hc h)

/-! ## The standard presentation

Reading the rows straight off the lists, truncating at `nlin` / `nt` and padding with the zero row
and `none`.  `Covers` holds unconditionally — truncation only *drops* rows — which is what lets
the zero-knowledge bridge quantify over every `LigeroSystem`.  `Reaches` is where the length
side conditions appear. -/

/-- Slot `e` of `S`'s linear rows, or the zero row. -/
def presentLin (nlin : ℕ) (S : LigeroSystem ninp M F) (e : Fin nlin) : LigeroRow ninp M F :=
  (S.linear[e.val]?).getD (zeroRow ninp M F)

/-- Slot `j` of `S`'s triples, or nothing. -/
def presentTri (nt : ℕ) (S : LigeroSystem ninp M F) (j : Fin nt) :
    Option (Fin M × Fin M × Fin M) :=
  S.quad[j.val]?

theorem covers_present (nlin nt : ℕ) (S : LigeroSystem ninp M F) :
    Covers S (presentLin nlin S) (presentTri nt S) where
  lin_mem e := by
    rcases h : S.linear[e.val]? with _ | row
    · right; simp [presentLin, h]
    · left; simpa [presentLin, h] using List.mem_of_getElem? h
  tri_mem j t ht := List.mem_of_getElem? ht

theorem reaches_present {nlin nt : ℕ} {S : LigeroSystem ninp M F}
    (hlin : S.linear.length ≤ nlin) (hquad : S.quad.length ≤ nt) :
    Reaches S (presentLin nlin S) (presentTri nt S) where
  lin_cov row hrow := by
    obtain ⟨i, hlt, hi⟩ := List.getElem_of_mem hrow
    exact ⟨⟨i, lt_of_lt_of_le hlt hlin⟩, by
      simp [presentLin, List.getElem?_eq_getElem hlt, hi]⟩
  tri_cov t ht := by
    obtain ⟨i, hlt, hi⟩ := List.getElem_of_mem ht
    exact ⟨⟨i, lt_of_lt_of_le hlt hquad⟩, by
      simp [presentTri, List.getElem?_eq_getElem hlt, hi]⟩

/-! ### The standard encoding

`encodeSystem` at the standard presentation.  Both bridges use this; the zero-knowledge one gets
its obligation unconditionally, the soundness one pays the two length bounds. -/

/-- An lfzk system as a `ConstraintSystem`, rows read off the lists. -/
noncomputable def encodeLig (pl : Placement ninp M w nw nq nt) (nlin : ℕ)
    (S : LigeroSystem ninp M F) :
    ConstraintSystem F nw nq w (Fin nlin ⊕ (Fin nt × QSide)) :=
  encodeSystem pl (presentLin nlin S) (presentTri nt S)

/-- An lfzk assignment as a tableau. -/
noncomputable def embedLig (pl : Placement ninp M w nw nq nt) (S : LigeroSystem ninp M F)
    (wcol : Fin ninp → F) (pad : Pad M F) : CoreMessages F nw nq w :=
  embed pl (presentTri nt S) (Sum.elim wcol pad)

/-- **Completeness at the standard encoding**, with no side condition on the system's size. -/
theorem satisfies_encodeLig (pl : Placement ninp M w nw nq nt) (nlin : ℕ)
    (S : LigeroSystem ninp M F) (wcol : Fin ninp → F) (pad : Pad M F) (h : S.Sat wcol pad) :
    (encodeLig pl nlin S).Satisfies (embedLig pl S wcol pad) :=
  satisfies_embed_of_sat pl (covers_present nlin nt S) wcol pad h

/-- **Soundness at the standard encoding.**  Here the tableau must be big enough to hold every
row and triple, or the encoding would silently drop constraints. -/
theorem sat_decode_encodeLig (pl : Placement ninp M w nw nq nt) {nlin : ℕ}
    {S : LigeroSystem ninp M F} (hlin : S.linear.length ≤ nlin) (hquad : S.quad.length ≤ nt)
    (msgs : CoreMessages F nw nq w) (h : (encodeLig pl nlin S).Satisfies msgs) :
    S.Sat (decode pl msgs).1 (decode pl msgs).2 :=
  sat_decode_of_satisfies pl (reaches_present hlin hquad) msgs h

/-! ## A concrete placement

`Placement` is a hypothesis of every theorem above, so a witness is needed for them not to be
vacuous.  This is the `w = 1` one — one scalar per row, one triple per quadratic row — which is
the loosest packing and the cheapest to check.  A denser packing is a different `Placement` and
changes no proof. -/

/-- One scalar per tableau row: `w = 1`, `nw = ninp + M`, `nq = nt`. -/
def flatPlacement (ninp M nt : ℕ) : Placement ninp M 1 (ninp + M) nt nt where
  cell := fun s => (finSumFinEquiv s, 0)
  cell_inj := fun _ _ h => finSumFinEquiv.injective (congrArg Prod.fst h)
  qcell := fun j => (j, 0)
  qcell_inj := fun _ _ h => congrArg Prod.fst h

/--
**The dense packing**, which is the one a parameter point actually uses: the `ninp + M` scalars
laid row-major into the `nw × w` linear block and the `nt` triples into the `nq × w` quadratic
block, legal exactly when each block is big enough.

The two blocks are independent, so both may be full.  Since the soundness bound depends on the
code parameters and not on `nw` or `nq`, this changes the prover's work and nothing else.
-/
def packedPlacement (ninp M w nw nq nt : ℕ) (hlin : ninp + M ≤ nw * w) (hquad : nt ≤ nq * w) :
    Placement ninp M w nw nq nt where
  cell := fun s => finProdFinEquiv.symm (Fin.castLE hlin (finSumFinEquiv s))
  cell_inj := fun _ _ h =>
    finSumFinEquiv.injective (Fin.castLE_injective hlin (finProdFinEquiv.symm.injective h))
  qcell := fun j => finProdFinEquiv.symm (Fin.castLE hquad j)
  qcell_inj := fun _ _ h => Fin.castLE_injective hquad (finProdFinEquiv.symm.injective h)

end Lfzk.Encode
