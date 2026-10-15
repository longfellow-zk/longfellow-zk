import polygero.Protocol.Rows
import LigeroFamily.Protocol.Finite

/-!
# Polygero with an additive polynomial-response mask

Two responses, masked linear arithmetic, and individual product checks.
The ordinary tableau contains the core rows and two degree-`<k` checked arithmetic
masks. One degree-`<k+s` proximity mask is added with coefficient one.
There are no other blinding rows; random-padding mask values are unrestricted.
-/
namespace RecursivePolygero.Local.Polygero
open Polynomial Finset Codes LigeroFamily MultiplicativeCode
open LigeroFamily.PolynomialDirect
variable {F Equations : Type} [Field F] [DecidableEq F] [Fintype Equations]
variable {q r w n nw nq s : ℕ}

structure Oracle (F : Type) (nw nq n : ℕ) where
  ordinary : Tableau F nw nq n
  proximityMask : Word F n

abbrev Coin (F Equations : Type) [Field F] (nw nq s : ℕ) :=
  (Equations → F) × Challenge F (rowCount nw nq) s

noncomputable def goodColumns (D : ReedSolomon.Domain F r w n)
    (hk : r+w ≤ n) (hprimary : r+w+s ≤ n)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (oracle : Oracle F nw nq n) (coin : Coin F Equations nw nq s)
    (payload : LigeroPayload F (r+w) s) : Finset (Fin n) := by
  classical
  exact univ.filter fun j =>
    (payload.primary : F[X]).eval (D.point (codePosition j)) =
      response (primaryCode D hprimary) (oracleWords oracle.ordinary) coin.2 j +
        oracle.proximityMask j ∧
    (payload.arithmetic : F[X]).eval (D.point (codePosition j)) =
      linearPointwise D hk layout statement coin.1 j (fun i => oracleWords oracle.ordinary i j) ∧
    ∀ g : Fin nq, oracle.ordinary.core .left g j * oracle.ordinary.core .right g j =
      oracle.ordinary.core .output g j

def globalCheck (D : ReedSolomon.Domain F r w n)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F) (payload : LigeroPayload F (r+w) s) : Prop :=
  (∑ i : Fin q, (payload.arithmetic : F[X]).eval
    (D.point (logicalWitnessPosition layout i))) = statement.combinedTarget weights

noncomputable def Accepts (D : ReedSolomon.Domain F r w n)
    (hk : r+w ≤ n) (hprimary : r+w+s ≤ n)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (oracle : Oracle F nw nq n) (coin : Coin F Equations nw nq s)
    (payload : LigeroPayload F (r+w) s) (Q : Finset (Fin n)) : Prop :=
  globalCheck D layout statement coin.1 payload ∧
    Q ⊆ goodColumns D hk hprimary layout statement oracle coin payload

abbrev Opening (F : Type) (nw nq n t : ℕ) (Q : QuerySet n t) :=
  (↥Q.coordinates → Column F nw nq) ×
    (↥Q.coordinates → F)

def openOracle {t : ℕ} (oracle : Oracle F nw nq n) (Q : QuerySet n t) : Opening F nw nq n t Q :=
  (openTableau oracle.ordinary Q, fun j => oracle.proximityMask j.1)

omit [Field F] [DecidableEq F] in
/-- Openings determine every ordinary entry used by the verifier. -/
theorem oracleWords_eq_of_opening {t : ℕ}
    {o o' : SchemeOracle F LinearConstraintMask NoMask nw nq n 1} {Q : QuerySet n t}
    (h : openSchemeOracle o Q = openSchemeOracle o' Q)
    (i : Fin (rowCount nw nq)) (j : ↥Q.coordinates) :
    oracleWords (Tableau.ofLegacy o) i j.1 =
      oracleWords (Tableau.ofLegacy o') i j.1 := by
  have hc := congrFun h j
  unfold oracleWords
  cases rowEquiv nw nq i with
  | inl core => exact congrArg (fun c => c.core core.1 core.2) hc
  | inr kind => exact congrArg (fun c => c.checkedMask 0 kind) hc


noncomputable def columnValues (column : Column F nw nq)
    (i : Fin (rowCount nw nq)) : F :=
  match rowEquiv nw nq i with
  | .inl core => column.core core.1 core.2
  | .inr kind => column.checkedMask kind

omit [Field F] [DecidableEq F] in
@[simp] theorem columnValues_open {t : ℕ} (oracle : Oracle F nw nq n) (Q : QuerySet n t)
    (j : ↥Q.coordinates) (i : Fin (rowCount nw nq)) :
    columnValues ((openOracle oracle Q).1 j) i = oracleWords oracle.ordinary i j.1 := by
  unfold columnValues oracleWords
  cases rowEquiv nw nq i with
  | inl core => rfl
  | inr u => rfl

/-- The opening-only Boolean predicate consumes only the public coin, the two bounded
responses, and the requested column openings. -/
noncomputable def verify {t : ℕ} (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (coin : Coin F Equations nw nq s) (payload : LigeroPayload F (r+w) s)
    (Q : QuerySet n t) (opening : Opening F nw nq n t Q) : Bool := by
  classical
  exact decide (globalCheck D layout statement coin.1 payload ∧ ∀ j : ↥Q.coordinates,
    (payload.primary : F[X]).eval (D.point (codePosition j.1)) =
      (∑ i, (coin.2 i : F[X]).eval (D.point (codePosition j.1)) * columnValues (opening.1 j) i) +
        opening.2 j ∧
    (payload.arithmetic : F[X]).eval (D.point (codePosition j.1)) =
      linearPointwise D hk layout statement coin.1 j.1 (columnValues (opening.1 j)) ∧
    ∀ g : Fin nq, (opening.1 j).core .left g * (opening.1 j).core .right g =
      (opening.1 j).core .output g)

/-- End-to-end identification of the counted event with the opening-only verifier. -/
theorem verify_openOracle_iff {t : ℕ} (D : ReedSolomon.Domain F r w n)
    (hk : r+w ≤ n) (hprimary : r+w+s ≤ n)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (oracle : Oracle F nw nq n) (coin : Coin F Equations nw nq s)
    (payload : LigeroPayload F (r+w) s) (Q : QuerySet n t) :
    verify D hk layout statement coin payload Q (openOracle oracle Q) = true ↔
      Accepts D hk hprimary layout statement oracle coin payload Q.coordinates := by
  classical
  simp only [verify, decide_eq_true_eq]
  have hf (j : ↥Q.coordinates) : columnValues ((openOracle oracle Q).1 j) =
      fun i => oracleWords oracle.ordinary i j.1 := funext (columnValues_open oracle Q j)
  simp_rw [hf]
  simp only [Accepts, goodColumns, subset_iff, mem_filter,
    mem_univ, true_and, Subtype.forall, response, primaryCode,
    openOracle, openTableau, Tableau.column]

end RecursivePolygero.Local.Polygero
