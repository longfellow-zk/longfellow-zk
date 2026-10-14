import polygero.Protocol.Tableau
import polygero.Protocol.Legacy.Verifier

/-! Physical row indices for polynomial challenges. The legacy zero-blind
coordinate exists only inside the arithmetic adapter, never in the sampled coin. -/
namespace RecursivePolygero.Local.Polygero
open Polynomial Finset Codes LigeroFamily MultiplicativeCode
variable {F : Type} {nw nq n : ℕ}

abbrev BatchedRow (nw nq : ℕ) :=
  CoreRow nw nq ⊕ LinearConstraintMask
abbrev rowCount (nw nq : ℕ) := Fintype.card (BatchedRow nw nq)
/-- Every physical ordinary row gets one challenge; there is no dummy slot. -/
theorem rowCount_eq (nw nq : ℕ) : rowCount nw nq = Fintype.card (CoreRow nw nq) + 2 := by
  simp only [rowCount, BatchedRow, Fintype.card_sum,
    show Fintype.card LinearConstraintMask = 2 from by decide]

noncomputable def rowEquiv (nw nq : ℕ) : Fin (rowCount nw nq) ≃ BatchedRow nw nq :=
  (Fintype.equivFin _).symm
noncomputable def indexOf (row : BatchedRow nw nq) : Fin (rowCount nw nq) :=
  (rowEquiv nw nq).symm row
@[simp] theorem rowEquiv_indexOf (row : BatchedRow nw nq) :
    rowEquiv nw nq (indexOf row) = row := (rowEquiv nw nq).apply_symm_apply row
noncomputable def coreIndex (block : CoreBlock) (row : Fin (block.rowCount nw nq)) :=
  indexOf (Sum.inl ⟨block,row⟩)
noncomputable def maskIndex (kind : LinearConstraintMask) : Fin (rowCount nw nq) :=
  indexOf (Sum.inr kind)
noncomputable def leftIndex (row : Fin nq) : Fin (rowCount nw nq) := coreIndex .left row
noncomputable def rightIndex (row : Fin nq) : Fin (rowCount nw nq) := coreIndex .right row
noncomputable def outputIndex (row : Fin nq) : Fin (rowCount nw nq) := coreIndex .output row

noncomputable def oracleWords (oracle : Tableau F nw nq n) : Fin (rowCount nw nq) → Word F n :=
  fun i => match rowEquiv nw nq i with
  | .inl core => oracle.core core.1 core.2
  | .inr kind => oracle.checkedMask kind
@[simp] theorem oracleWords_core (oracle : Tableau F nw nq n)
    (block : CoreBlock) (row : Fin (block.rowCount nw nq)) (j : Fin n) :
    oracleWords oracle (coreIndex block row) j = oracle.core block row j := by
  simp [oracleWords, coreIndex]
@[simp] theorem oracleWords_mask (oracle : Tableau F nw nq n)
    (kind : LinearConstraintMask) (j : Fin n) :
    oracleWords oracle (maskIndex kind) j = oracle.checkedMask kind j := by
  simp [oracleWords, maskIndex]

/-- Supply the legacy arithmetic API's missing coordinate deterministically. -/
noncomputable def extendRows {V : Type*} [Zero V] (rows : Fin (rowCount nw nq) → V) :
    Fin (PolynomialDirect.rowCount nw nq) → V := fun i =>
  match PolynomialDirect.rowEquiv nw nq i with
  | .inl (.inl core) => rows (coreIndex core.1 core.2)
  | .inl (.inr mask) => rows (maskIndex mask.2)
  | .inr _ => 0

@[simp] theorem extendRows_core {V : Type*} [Zero V] (rows : Fin (rowCount nw nq) → V)
    (block : CoreBlock) (row : Fin (block.rowCount nw nq)) :
    extendRows rows (PolynomialDirect.coreIndex block row) = rows (coreIndex block row) := by
  simp [extendRows, PolynomialDirect.coreIndex]
@[simp] theorem extendRows_mask {V : Type*} [Zero V] (rows : Fin (rowCount nw nq) → V)
    (kind : LinearConstraintMask) :
    extendRows rows (PolynomialDirect.maskIndex kind) = rows (maskIndex kind) := by
  simp [extendRows, PolynomialDirect.maskIndex]

theorem extendRows_map {V W : Type*} [Zero V] [Zero W]
    (f : V → W) (hf : f 0 = 0) (rows : Fin (rowCount nw nq) → V) :
    extendRows (fun i => f (rows i)) = fun i => f (extendRows rows i) := by
  funext i
  unfold extendRows
  cases PolynomialDirect.rowEquiv nw nq i with
  | inl row => cases row <;> rfl
  | inr u => exact hf.symm

section Arithmetic
variable [Field F] [DecidableEq F]
variable {Equations : Type} [Fintype Equations] {q r w s : ℕ}

noncomputable def linearPointwise (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F) (j : Fin n) (values : Fin (rowCount nw nq) → F) : F :=
  PolynomialDirect.linearPointwise D hk layout statement weights j (extendRows values)

/-- Arithmetic ignores the polynomial challenge; only the ordinary physical
rows are supplied by the list-MCA candidate. -/
noncomputable def responseSemantics (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (hprimary : r+w+s ≤ n) (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations) (weights : Equations → F) :
    ResponseSemantics (PolynomialDirect.primaryCode D hprimary) (rowCount nw nq)
      (r+w) s (2*(r+w)) where
  pointwise _ j values := linearPointwise D hk layout statement weights j values
  canonical _ rows := (PolynomialDirect.responseSemantics D hk hprimary layout statement weights).canonical
    0 (extendRows rows)
  canonical_eval := by
    intro B rows j
    have he := (PolynomialDirect.responseSemantics D hk hprimary layout statement weights).canonical_eval
      0 (extendRows rows) j
    dsimp only [PolynomialDirect.responseSemantics] at he ⊢
    rw [he]
    dsimp only [linearPointwise]
    have hm := extendRows_map (nw := nw) (nq := nq)
      (fun p : DegreeLT F (r+w) => (p : F[X]).eval ((PolynomialDirect.primaryCode D hprimary).node j))
      (show ((0 : DegreeLT F (r+w)) : F[X]).eval _ = 0 from eval_zero) rows
    exact congrArg (PolynomialDirect.linearPointwise D hk layout statement weights j) hm.symm
end Arithmetic
end RecursivePolygero.Local.Polygero
