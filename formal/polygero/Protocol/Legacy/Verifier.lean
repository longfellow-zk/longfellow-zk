import polygero.Protocol.Legacy.PolynomialRows

/-! Legacy row adapter and exact shared-column verifier semantics. -/

namespace LigeroFamily.PolynomialDirect
open Finset Polynomial
open MultiplicativeCode
open RecursivePolygero.Local
variable {F Equations : Type*} [Field F] [DecidableEq F]
variable [Fintype Equations]
variable {q r w n nw nq s : Nat}

/-- Actual V3 masked-linear local equation, evaluated at one committed
column. -/
noncomputable def linearPointwise
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F) (z : Fin n)
    (values : Fin (rowCount nw nq) → F) : F :=
  (∑ block : CoreBlock, ∑ row : Fin (block.rowCount nw nq),
      DirectVerifier.coefficientRow (ReedSolomon.multiplicativeCode D hk)
          layout statement weights block row (codePosition z) *
        values (coreIndex block row)) +
    (ReedSolomon.maskingBasis D hk).vanishing (codePosition z) *
      values (maskIndex .vCoefficient) +
    (ReedSolomon.multiplicativeCode D hk).zR (codePosition z) *
      values (maskIndex .zRCoefficient)

/-- The concrete `ResponseSemantics` instance consumed by polynomial
attribution--pinning.  Polynomial challenges affect the primary response;
the auxiliary V3 linear weights determine this arithmetic response. -/
noncomputable def responseSemantics
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (hprimary : r + w + s ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F) :
    ResponseSemantics (primaryCode D hprimary) (rowCount nw nq)
      (r + w) s (2 * (r + w)) where
  pointwise _B z values := linearPointwise D hk layout statement weights z values
  canonical _B rows := responsePolynomial D hk
    (linearRow D hk layout statement weights rows)
    (linearRow_mem D hk layout statement weights rows)
  canonical_eval := by
    intro B rows z
    change ((responsePolynomial D hk
      (linearRow D hk layout statement weights rows)
      (linearRow_mem D hk layout statement weights rows) :
        DegreeLT F (2 * (r + w))) : F[X]).eval
          (D.point (codePosition z)) = _
    rw [responsePolynomial_eval D hk _ _ (codePosition z)]
    simp only [linearPointwise, linearRow, DirectVerifier.linearResponse,
      DirectVerifier.linearCore, DirectVerifier.linearMask, Pi.add_apply,
      Finset.sum_apply, rowMul_apply, decodedCore, decodedMask, evaluationRow]
    simp only [primaryCode]
    ring

/-- Convert the actual committed V3 oracle into the row tuple consumed by
polynomial correlated agreement. -/
noncomputable def oracleWords
    (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq n 1) :
    Fin (rowCount nw nq) → Codes.Word F n := fun i =>
  match rowEquiv nw nq i with
  | Sum.inl tested => oracle.testedRow tested
  | Sum.inr _ => oracle.proximityBlind 0

omit [Field F] [DecidableEq F] in
@[simp] theorem oracleWords_core
    (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq n 1)
    (block : CoreBlock) (row : Fin (block.rowCount nw nq)) (z : Fin n) :
    oracleWords oracle (coreIndex block row) z = oracle.core block row z := by
  simp [oracleWords, coreIndex, SchemeOracle.testedRow]

omit [Field F] [DecidableEq F] in
@[simp] theorem oracleWords_mask
    (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq n 1)
    (kind : LinearConstraintMask) (z : Fin n) :
    oracleWords oracle (maskIndex kind) z = oracle.checkedMask 0 kind z := by
  simp [oracleWords, maskIndex, SchemeOracle.testedRow]

omit [Field F] [DecidableEq F] in
@[simp] theorem oracleWords_blind
    (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq n 1) (z : Fin n) :
    oracleWords oracle blindIndex z = oracle.proximityBlind 0 z := by
  simp [oracleWords, blindIndex]

noncomputable def leftIndex (row : Fin nq) : Fin (rowCount nw nq) :=
  coreIndex .left row

noncomputable def rightIndex (row : Fin nq) : Fin (rowCount nw nq) :=
  coreIndex .right row

noncomputable def outputIndex (row : Fin nq) : Fin (rowCount nw nq) :=
  coreIndex .output row

/-- The concrete shared-column verifier for polynomial-batched V3. -/
noncomputable def sharedVerifier
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (hprimary : r + w + s ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F) :
    SharedColumnVerifier (primaryCode D hprimary) (rowCount nw nq) (r + w) s :=
  SharedColumnVerifier.directProduct
    (responseSemantics D hk hprimary layout statement weights)
    leftIndex rightIndex outputIndex

/-- All local checks made by the polynomial-batched V3 verifier on one
opened column. -/
noncomputable def LocalAccepts
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (hprimary : r + w + s ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq n 1)
    (weights : Equations → F)
    (B : Challenge F (rowCount nw nq) s)
    (payload : LigeroPayload F (r + w) s)
    (query : Finset (Fin n)) : Prop :=
  ∀ z, z ∈ query →
    (payload.primary : F[X]).eval (D.point (codePosition z)) =
        RecursivePolygero.Local.response (primaryCode D hprimary) (oracleWords oracle) B z ∧
    (payload.arithmetic : F[X]).eval (D.point (codePosition z)) =
        linearPointwise D hk layout statement weights z
          (fun i => oracleWords oracle i z) ∧
    ∀ row : Fin nq,
      oracle.core .left row z * oracle.core .right row z =
        oracle.core .output row z

/-- Full polynomial-batched V3 acceptance: the global linear target check and
all local equations use the same response payload. -/
noncomputable def Accepts
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (hprimary : r + w + s ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq n 1)
    (weights : Equations → F)
    (B : Challenge F (rowCount nw nq) s)
    (payload : LigeroPayload F (r + w) s)
    (query : Finset (Fin n)) : Prop :=
  (∑ i : Fin q, (payload.arithmetic : F[X]).eval
      (D.point (logicalWitnessPosition layout i))) =
      statement.combinedTarget weights ∧
    LocalAccepts D hk hprimary layout statement oracle weights B payload query

omit [DecidableEq F] in
/-- Polynomial-direct acceptance only reads committed columns in the opened
set.  This is the locality lemma used by the serialized Merkle compiler. -/
theorem accepts_of_columns_eq_on
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (hprimary : r + w + s ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (first second : SchemeOracle F LinearConstraintMask NoMask nw nq n 1)
    (weights : Equations → F)
    (B : Challenge F (rowCount nw nq) s)
    (payload : LigeroPayload F (r + w) s)
    (query : Finset (Fin n))
    (hcolumns : ∀ z ∈ query, first.column z = second.column z)
    (haccept : Accepts D hk hprimary layout statement first weights B payload query) :
    Accepts D hk hprimary layout statement second weights B payload query := by
  refine ⟨haccept.1, ?_⟩
  intro z hz
  have hcolumn := hcolumns z hz
  have hcore : ∀ (block : CoreBlock) (row : Fin (block.rowCount nw nq)),
      first.core block row z = second.core block row z := by
    intro block row
    exact congrArg (fun column ↦ column.core block row) hcolumn
  have hmask : ∀ (h : Fin 1) (kind : LinearConstraintMask),
      first.checkedMask h kind z = second.checkedMask h kind z := by
    intro h kind
    exact congrArg (fun column ↦ column.checkedMask h kind) hcolumn
  have hblind : ∀ h : Fin 1,
      first.proximityBlind h z = second.proximityBlind h z := by
    intro h
    exact congrArg (fun column ↦ column.proximityBlind h) hcolumn
  have hwords : ∀ i : Fin (rowCount nw nq),
      oracleWords first i z = oracleWords second i z := by
    intro i
    rcases hrow : rowEquiv nw nq i with (tested | _)
    · rcases tested with (core | mask)
      · simpa [oracleWords, hrow, SchemeOracle.testedRow] using
          hcore core.1 core.2
      · simpa [oracleWords, hrow, SchemeOracle.testedRow] using
          hmask mask.1 mask.2
    · simpa [oracleWords, hrow] using hblind 0
  rcases haccept.2 z hz with ⟨hprimaryLocal, harithmetic, hproduct⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [RecursivePolygero.Local.response, hwords] using hprimaryLocal
  · simpa only [linearPointwise, hwords] using harithmetic
  · intro row
    simpa only [hcore] using hproduct row

/-- The explicit local verifier is exactly containment in the joint good set
used by attribution--pinning. -/
theorem localAccepts_iff_subset_goodColumns
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (hprimary : r + w + s ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq n 1)
    (weights : Equations → F)
    (B : Challenge F (rowCount nw nq) s)
    (payload : LigeroPayload F (r + w) s)
    (query : Finset (Fin n)) :
    LocalAccepts D hk hprimary layout statement oracle weights B payload query ↔
      query ⊆ (sharedVerifier D hk hprimary layout statement weights).goodColumns
        (oracleWords oracle) B payload := by
  constructor
  · intro haccept z hz
    rw [SharedColumnVerifier.mem_goodColumns]
    rcases haccept z hz with ⟨hprimaryLocal, harithmetic, hproduct⟩
    refine ⟨?_, harithmetic, ?_⟩
    · simpa [primaryCode] using hprimaryLocal
    · apply (SharedColumnVerifier.directProductExtra_eq_true_iff
        leftIndex rightIndex outputIndex z
          (fun i => oracleWords oracle i z)).mpr
      intro row
      simpa [leftIndex, rightIndex, outputIndex] using hproduct row
  · intro hsubset z hz
    have hgood := (SharedColumnVerifier.mem_goodColumns
      (sharedVerifier D hk hprimary layout statement weights)
      (oracleWords oracle) B payload z).mp (hsubset hz)
    refine ⟨?_, hgood.2.1, ?_⟩
    · simpa [primaryCode] using hgood.1
    · have hproduct :=
        (SharedColumnVerifier.directProductExtra_eq_true_iff
          leftIndex rightIndex outputIndex z
            (fun i => oracleWords oracle i z)).mp hgood.2.2
      intro row
      simpa [leftIndex, rightIndex, outputIndex] using hproduct row

theorem accepts_query_subset_goodColumns
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (hprimary : r + w + s ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq n 1)
    (weights : Equations → F)
    (B : Challenge F (rowCount nw nq) s)
    (payload : LigeroPayload F (r + w) s)
    (query : Finset (Fin n))
    (haccept : Accepts D hk hprimary layout statement oracle weights B payload query) :
    query ⊆ (sharedVerifier D hk hprimary layout statement weights).goodColumns
      (oracleWords oracle) B payload :=
  (localAccepts_iff_subset_goodColumns D hk hprimary layout statement oracle
    weights B payload query).mp haccept.2

end LigeroFamily.PolynomialDirect
