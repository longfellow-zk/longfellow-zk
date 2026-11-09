import LfzkV2.PolygeroCoreMasking
import polygero.Protocol.Verifier

/-!
# Algebraic coupling for the Fiat–Shamir backend simulator

The change of variables acts on the complete prover tape: ordinary and
product-input prefixes, the two checked arithmetic masks, and the additive
primary mask. Product outputs are derived. Statements and batching coins may
depend on the complete opened columns, as required after Merkle hiding.
-/

namespace LfzkV2.PolygeroZk

open Polynomial LigeroFamily MultiplicativeCode
open RecursivePolygero.Local

variable {F : Type} [Field F] {r w p n nw nq s : ℕ}

structure Geometry (F : Type) [Field F] (r w p n : ℕ) where
  domain : ReedSolomon.Domain F r w n
  k_le_n : r+w ≤ n
  productSlots : Fin p ↪ Fin w
  short_positive : 0 < r+p
  product_degree : 2*(r+p)-1 ≤ r+w

namespace Geometry

def runtime (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n) (hshape : r < w) :
    Geometry F r w (PolygeroCoreMasking.productWidth r w) n :=
  ⟨D, hk, PolygeroCoreMasking.productEmbedding hshape,
    (PolygeroCoreMasking.productWidth_bounds hshape).2.1,
    (PolygeroCoreMasking.productWidth_bounds hshape).2.2⟩

noncomputable abbrev code (G : Geometry F r w p n) :=
  ReedSolomon.multiplicativeCode G.domain G.k_le_n

noncomputable abbrev basis (G : Geometry F r w p n) :=
  ReedSolomon.maskingBasis G.domain G.k_le_n

theorem positive (G : Geometry F r w p n) : 0 < r+w := by
  have hp := PolygeroCoreMasking.short_dimension_le G.productSlots
  have hs := G.short_positive
  omega

end Geometry

def sumFunctional (F : Type) [Field F] (w : ℕ) : (Fin w → F) →ₗ[F] F :=
  logicalSumLinearMap (ConstraintLayout.identity w)

abbrev Tape (G : Geometry F r w p n) (nw nq s : ℕ) :=
  PolygeroCoreMasking.Tape F r nw nq ×
    PolygeroMasking.Tape G.code (sumFunctional F w) × DegreeLT F (r+w+s)

variable (G : Geometry F r w p n)

noncomputable def core (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (tape : PolygeroCoreMasking.Tape F r nw nq) : PolygeroMasking.CoreRows F r w n nw nq :=
  PolygeroCoreMasking.encoding G.domain G.k_le_n G.productSlots messages tape

theorem core_mem (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (tape : PolygeroCoreMasking.Tape F r nw nq) (block : CoreBlock)
    (row : Fin (block.rowCount nw nq)) : core G messages tape block row ∈ G.code.base :=
  PolygeroCoreMasking.encoding_mem G.domain G.k_le_n G.productSlots
    G.short_positive G.product_degree messages tape block row

noncomputable def basePolynomial (row : G.code.base) : DegreeLT F (r+w) :=
  ⟨Classical.choose ((ReedSolomon.mem_evaluationSpace G.domain).mp row.2),
    (Classical.choose_spec ((ReedSolomon.mem_evaluationSpace G.domain).mp row.2)).1⟩

theorem basePolynomial_eval (row : G.code.base) (i : Position r w n) :
    (basePolynomial G row : F[X]).eval (G.domain.point i) = row.1 i :=
  ((Classical.choose_spec ((ReedSolomon.mem_evaluationSpace G.domain).mp row.2)).2 i).symm

noncomputable def ordinaryRows (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (coreTape : PolygeroCoreMasking.Tape F r nw nq)
    (masks : PolygeroMasking.Tape G.code (sumFunctional F w)) :
    Fin (Polygero.rowCount nw nq) → DegreeLT F (r+w) := fun i =>
  match Polygero.rowEquiv nw nq i with
  | .inl ⟨block,row⟩ => basePolynomial G ⟨core G messages coreTape block row,
      core_mem G messages coreTape block row⟩
  | .inr .vCoefficient => basePolynomial G ⟨masks.vCoefficient.1, masks.vCoefficient.2.1⟩
  | .inr .zRCoefficient => basePolynomial G ⟨masks.zRCoefficient.1, masks.zRCoefficient.2.1⟩

noncomputable def oracle (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (tape : Tape G nw nq s) : Polygero.Oracle F nw nq n where
  ordinary :=
    { core := fun block row j => core G messages tape.1 block row (codePosition j)
      checkedMask := fun kind j => PolygeroMasking.maskRows tape.2.1 kind (codePosition j) }
  proximityMask j := (tape.2.2 : F[X]).eval (G.domain.point (codePosition j))

theorem ordinaryRows_eval (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (tape : Tape G nw nq s) (i : Fin (Polygero.rowCount nw nq)) (j : Fin n) :
    (ordinaryRows G messages tape.1 tape.2.1 i : F[X]).eval (G.domain.point (codePosition j)) =
      Polygero.oracleWords (oracle G messages tape).ordinary i j := by
  unfold ordinaryRows Polygero.oracleWords
  cases Polygero.rowEquiv nw nq i with
  | inl row => exact basePolynomial_eval G _ _
  | inr kind => cases kind <;> exact basePolynomial_eval G _ _

section Responses

variable {Equations : Type} [Fintype Equations]

noncomputable def arithmeticRow (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (tape : Tape G nw nq s) : G.code.response :=
  ⟨DirectVerifier.linearCore G.code (ConstraintLayout.identity w) statement weights
      (core G messages tape.1) +
    PolygeroMasking.response G.code G.basis (sumFunctional F w) tape.2.1,
    G.code.response.add_mem
      (PolygeroMasking.linearCore_mem G.code (ConstraintLayout.identity w) statement weights
        (core G messages tape.1) (core_mem G messages tape.1))
      (linearMaskMap G.code G.basis ∅ (sumFunctional F w) tape.2.1).2.1⟩

noncomputable def correctedArithmeticRow (Q : QuerySet n r) (pivot : Fin w)
    (statement : ConstraintSystem F nw nq w Equations) (weights : Equations → F)
    (tape : Tape G nw nq s) : G.code.response :=
  arithmeticRow G statement weights 0 tape +
    ⟨PolygeroMasking.correction G.code Q (ConstraintLayout.identity w) pivot
        (statement.combinedTarget weights),
      (PolygeroMasking.correction_properties G.code Q (ConstraintLayout.identity w) pivot
        (statement.combinedTarget weights)).1⟩

noncomputable def payload (hk : 0 < r+w)
    (statement : ConstraintSystem F nw nq w Equations)
    (coin : Polygero.Coin F Equations nw nq s)
    (messages : PolygeroCoreMasking.Messages F w p nw nq) (tape : Tape G nw nq s) :
    LigeroPayload F (r+w) s where
  primary := PolygeroPrimaryMasking.response hk coin.2 (ordinaryRows G messages tape.1 tape.2.1) tape.2.2
  arithmetic := PolynomialDirect.responsePolynomial G.domain G.k_le_n
    (arithmeticRow G statement coin.1 messages tape).1 (arithmeticRow G statement coin.1 messages tape).2

noncomputable def simPayload (hk : 0 < r+w) (Q : QuerySet n r) (pivot : Fin w)
    (statement : ConstraintSystem F nw nq w Equations)
    (coin : Polygero.Coin F Equations nw nq s) (tape : Tape G nw nq s) :
    LigeroPayload F (r+w) s where
  primary := PolygeroPrimaryMasking.response hk coin.2 (ordinaryRows G 0 tape.1 tape.2.1) tape.2.2
  arithmetic := PolynomialDirect.responsePolynomial G.domain G.k_le_n
    (correctedArithmeticRow G Q pivot statement coin.1 tape).1
    (correctedArithmeticRow G Q pivot statement coin.1 tape).2

theorem arithmeticRow_code (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (tape : Tape G nw nq s) (j : Fin n) :
    (arithmeticRow G statement weights messages tape).1 (codePosition j) =
      Polygero.linearPointwise G.domain G.k_le_n (ConstraintLayout.identity w) statement weights j
        (fun i => Polygero.oracleWords (oracle G messages tape).ordinary i j) := by
  unfold Polygero.linearPointwise PolynomialDirect.linearPointwise
  simp only [Polygero.extendRows_core, Polygero.extendRows_mask,
    Polygero.oracleWords_core, Polygero.oracleWords_mask]
  simp only [arithmeticRow, PolygeroMasking.response_eq_linearMask,
    DirectVerifier.linearCore, DirectVerifier.linearMask, Pi.add_apply,
    Finset.sum_apply, rowMul_apply, oracle]
  ring

theorem arithmeticRow_sum (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (tape : Tape G nw nq s)
    (hsat : statement.Satisfies
      (layoutCoreMessages (ConstraintLayout.identity w) (core G messages tape.1))) :
    sumFunctional F w (witnessValues (arithmeticRow G statement weights messages tape).1) =
      statement.combinedTarget weights := by
  change sumFunctional F w
    (witnessValues (DirectVerifier.linearCore G.code (ConstraintLayout.identity w) statement weights
      (core G messages tape.1)) +
      witnessValues (PolygeroMasking.response G.code G.basis (sumFunctional F w) tape.2.1)) = _
  rw [map_add]
  have hcore := PolygeroMasking.linearCore_sum_of_satisfies G.code
    (ConstraintLayout.identity w) statement weights (core G messages tape.1) hsat
  change sumFunctional F w (witnessValues
    (DirectVerifier.linearCore G.code (ConstraintLayout.identity w) statement weights
      (core G messages tape.1))) = _ at hcore
  rw [hcore]
  exact add_eq_left.mpr (linearMaskMap G.code G.basis ∅ (sumFunctional F w) tape.2.1).2.2.2.2

/-- The real payload is the honest bounded response consumed by the actual
opening-only Polygero verifier. -/
theorem payload_verifies [DecidableEq F] (hprimary : r+w+s ≤ n) (Q : QuerySet n r)
    (statement : ConstraintSystem F nw nq w Equations)
    (coin : Polygero.Coin F Equations nw nq s)
    (messages : PolygeroCoreMasking.Messages F w p nw nq) (tape : Tape G nw nq s)
    (hsat : statement.Satisfies
      (layoutCoreMessages (ConstraintLayout.identity w) (core G messages tape.1))) :
    Polygero.verify G.domain G.k_le_n (ConstraintLayout.identity w) statement coin
      (payload G G.positive statement coin messages tape) Q
      (Polygero.openOracle (oracle G messages tape) Q) = true := by
  apply (Polygero.verify_openOracle_iff G.domain G.k_le_n hprimary
    (ConstraintLayout.identity w) statement (oracle G messages tape) coin _ Q).2
  constructor
  · unfold Polygero.globalCheck
    simp only [payload, PolynomialDirect.responsePolynomial_eval]
    exact arithmeticRow_sum G statement coin.1 messages tape hsat
  · intro j _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · change (PolygeroPrimaryMasking.response G.positive coin.2
        (ordinaryRows G messages tape.1 tape.2.1) tape.2.2 : F[X]).eval _ = _
      rw [PolygeroPrimaryMasking.response_eval]
      simp only [ordinaryRows_eval, RecursivePolygero.Local.response,
        PolynomialDirect.primaryCode, oracle]
    · change (PolynomialDirect.responsePolynomial G.domain G.k_le_n
        (arithmeticRow G statement coin.1 messages tape).1
        (arithmeticRow G statement coin.1 messages tape).2 : F[X]).eval _ = _
      rw [PolynomialDirect.responsePolynomial_eval, arithmeticRow_code]
    · intro row
      exact PolygeroCoreMasking.encoding_product G.domain G.k_le_n G.productSlots
        messages tape.1 row (codePosition j)

end Responses

section Translation

variable {Equations : Type} [Fintype Equations]

/-- Compatibility records the ordinary statement-validity requirement and
the public fact that product coefficients use the actual product slots. -/
structure Compatible (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (statement : ConstraintSystem F nw nq w Equations) : Prop where
  supported : ∀ equation block row col,
    ¬ (block = .linear ∨ col ∈ Set.range G.productSlots) →
      statement.coefficient equation block row col = 0
  satisfied : ∀ tape : PolygeroCoreMasking.Tape F r nw nq,
    statement.Satisfies (layoutCoreMessages (ConstraintLayout.identity w) (core G messages tape))

noncomputable def coreShift (Q : QuerySet n r)
    (messages : PolygeroCoreMasking.Messages F w p nw nq) :
    PolygeroCoreMasking.Tape F r nw nq ≃ PolygeroCoreMasking.Tape F r nw nq :=
  PolygeroCoreMasking.translate G.domain G.k_le_n G.productSlots Q messages 0

noncomputable def difference (Q : QuerySet n r) (pivot : Fin w)
    (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (statement : ConstraintSystem F nw nq w Equations) (h : Compatible G messages statement)
    (weights : Equations → F) (tape : PolygeroCoreMasking.Tape F r nw nq) :
    linearResponseKernel G.code Q.coordinates (sumFunctional F w) :=
  PolygeroMasking.arithmeticDifference G.code Q (ConstraintLayout.identity w) pivot statement weights
    (core G messages tape) (core G 0 (coreShift G Q messages tape))
    (core_mem G messages tape) (core_mem G 0 (coreShift G Q messages tape)) (h.satisfied tape)
    (PolygeroCoreMasking.zero_encoding_linearValue G.domain G.k_le_n G.productSlots
      (coreShift G Q messages tape) statement h.supported)
    (fun block row j => (PolygeroCoreMasking.translate_openings G.domain G.k_le_n G.productSlots
      Q messages 0 tape block row j).symm)

noncomputable def maskShift (Q : QuerySet n r) (pivot : Fin w)
    (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (statement : ConstraintSystem F nw nq w Equations) (h : Compatible G messages statement)
    (weights : Equations → F) (tape : PolygeroCoreMasking.Tape F r nw nq) :
    PolygeroMasking.Tape G.code (sumFunctional F w) ≃
      PolygeroMasking.Tape G.code (sumFunctional F w) :=
  PolygeroMasking.translate G.code G.basis Q (sumFunctional F w)
    (difference G Q pivot messages statement h weights tape)

noncomputable def toSim (Q : QuerySet n r) (pivot : Fin w)
    (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (statement : ConstraintSystem F nw nq w Equations) (h : Compatible G messages statement)
    (coin : Polygero.Coin F Equations nw nq s) (tape : Tape G nw nq s) : Tape G nw nq s :=
  let coreTape := coreShift G Q messages tape.1
  let masks := maskShift G Q pivot messages statement h coin.1 tape.1 tape.2.1
  (coreTape, masks, PolygeroPrimaryMasking.translate G.positive coin.2
    (ordinaryRows G messages tape.1 tape.2.1) (ordinaryRows G 0 coreTape masks) tape.2.2)

theorem ordinaryRows_shift_eval (Q : QuerySet n r) (pivot : Fin w)
    (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (statement : ConstraintSystem F nw nq w Equations) (h : Compatible G messages statement)
    (weights : Equations → F) (coreTape : PolygeroCoreMasking.Tape F r nw nq)
    (masks : PolygeroMasking.Tape G.code (sumFunctional F w))
    (i : Fin (Polygero.rowCount nw nq)) (j : ↥Q.coordinates) :
    (ordinaryRows G 0 (coreShift G Q messages coreTape)
        (maskShift G Q pivot messages statement h weights coreTape masks) i : F[X]).eval
        (G.domain.point (codePosition j.1)) =
      (ordinaryRows G messages coreTape masks i : F[X]).eval (G.domain.point (codePosition j.1)) := by
  unfold ordinaryRows
  cases Polygero.rowEquiv nw nq i with
  | inl row =>
      rw [basePolynomial_eval, basePolynomial_eval]
      exact PolygeroCoreMasking.translate_openings G.domain G.k_le_n G.productSlots
        Q messages 0 coreTape row.1 row.2 j
  | inr kind =>
      cases kind with
      | vCoefficient =>
          rw [basePolynomial_eval, basePolynomial_eval]
          exact (PolygeroMasking.translate_openings G.code G.basis Q (sumFunctional F w)
            (difference G Q pivot messages statement h weights coreTape) masks j).1
      | zRCoefficient =>
          rw [basePolynomial_eval, basePolynomial_eval]
          exact (PolygeroMasking.translate_openings G.code G.basis Q (sumFunctional F w)
            (difference G Q pivot messages statement h weights coreTape) masks j).2

theorem toSim_opening (Q : QuerySet n r) (pivot : Fin w)
    (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (statement : ConstraintSystem F nw nq w Equations) (h : Compatible G messages statement)
    (coin : Polygero.Coin F Equations nw nq s) (tape : Tape G nw nq s) :
    Polygero.openOracle (oracle G 0 (toSim G Q pivot messages statement h coin tape)) Q =
      Polygero.openOracle (oracle G messages tape) Q := by
  apply Prod.ext
  · funext j
    apply congrArg₂ Polygero.Column.mk
    · funext block row
      exact PolygeroCoreMasking.translate_openings G.domain G.k_le_n G.productSlots
        Q messages 0 tape.1 block row j
    · funext kind
      have hm := PolygeroMasking.translate_openings G.code G.basis Q (sumFunctional F w)
        (difference G Q pivot messages statement h coin.1 tape.1) tape.2.1 j
      cases kind with
      | vCoefficient => exact hm.1
      | zRCoefficient => exact hm.2
  · funext j
    exact PolygeroPrimaryMasking.translate_openings G.positive coin.2
      (ordinaryRows G messages tape.1 tape.2.1)
      (ordinaryRows G 0 (coreShift G Q messages tape.1)
        (maskShift G Q pivot messages statement h coin.1 tape.1 tape.2.1)) tape.2.2
      (fun j => G.domain.point (codePosition j)) Q
      (fun i j => (ordinaryRows_shift_eval G Q pivot messages statement h coin.1 tape.1 tape.2.1 i j).symm) j

theorem toSim_arithmetic (Q : QuerySet n r) (pivot : Fin w)
    (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (statement : ConstraintSystem F nw nq w Equations) (h : Compatible G messages statement)
    (coin : Polygero.Coin F Equations nw nq s) (tape : Tape G nw nq s) :
    correctedArithmeticRow G Q pivot statement coin.1 (toSim G Q pivot messages statement h coin tape) =
      arithmeticRow G statement coin.1 messages tape := by
  apply Subtype.ext
  exact PolygeroMasking.arithmetic_response_preserved G.code G.basis Q
    (ConstraintLayout.identity w) pivot statement coin.1 (core G messages tape.1)
    (core G 0 (coreShift G Q messages tape.1))
    (core_mem G messages tape.1) (core_mem G 0 (coreShift G Q messages tape.1)) (h.satisfied tape.1)
    (PolygeroCoreMasking.zero_encoding_linearValue G.domain G.k_le_n G.productSlots
      (coreShift G Q messages tape.1) statement h.supported)
    (fun block row j => (PolygeroCoreMasking.translate_openings G.domain G.k_le_n G.productSlots
      Q messages 0 tape.1 block row j).symm) tape.2.1

theorem toSim_payload (Q : QuerySet n r) (pivot : Fin w)
    (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (statement : ConstraintSystem F nw nq w Equations) (h : Compatible G messages statement)
    (coin : Polygero.Coin F Equations nw nq s) (tape : Tape G nw nq s) :
    simPayload G G.positive Q pivot statement coin (toSim G Q pivot messages statement h coin tape) =
      payload G G.positive statement coin messages tape := by
  apply congrArg₂ LigeroPayload.mk
  · exact PolygeroPrimaryMasking.translate_response G.positive coin.2 _ _ tape.2.2
  · exact congrArg (fun row : G.code.response =>
      PolynomialDirect.responsePolynomial G.domain G.k_le_n row.1 row.2)
      (toSim_arithmetic G Q pivot messages statement h coin tape)

theorem toSim_injective (Q : QuerySet n r) (pivot : Fin w)
    (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (statement : ConstraintSystem F nw nq w Equations) (h : Compatible G messages statement)
    (coin : Polygero.Coin F Equations nw nq s) :
    Function.Injective (toSim G Q pivot messages statement h coin) := by
  rintro ⟨ac,am,af⟩ ⟨bc,bm,bf⟩ heq
  have hc : ac = bc := (coreShift G Q messages).injective (congrArg Prod.fst heq)
  subst bc
  have hm : am = bm := (maskShift G Q pivot messages statement h coin.1 ac).injective
    (congrArg (fun t : Tape G nw nq s => t.2.1) heq)
  subst bm
  have hf : af = bf := (PolygeroPrimaryMasking.translate G.positive coin.2
    (ordinaryRows G messages ac am)
    (ordinaryRows G 0 (coreShift G Q messages ac)
      (maskShift G Q pivot messages statement h coin.1 ac am))).injective
    (congrArg (fun t : Tape G nw nq s => t.2.2) heq)
  subst bf
  rfl

end Translation

section Adaptive

variable {Equations : Type} [Fintype Equations]
variable (Q : QuerySet n r) (pivot : Fin w)
variable (messages : PolygeroCoreMasking.Messages F w p nw nq)
variable (statements : Polygero.Opening F nw nq n r Q → ConstraintSystem F nw nq w Equations)
variable (coins : Polygero.Opening F nw nq n r Q → Polygero.Coin F Equations nw nq s)
variable (hcompatible : ∀ opening, Compatible G messages (statements opening))

noncomputable def adaptiveMap (tape : Tape G nw nq s) : Tape G nw nq s :=
  let opening := Polygero.openOracle (oracle G messages tape) Q
  toSim G Q pivot messages (statements opening) (hcompatible opening) (coins opening) tape

theorem adaptiveMap_opening (tape : Tape G nw nq s) :
    Polygero.openOracle (oracle G 0 (adaptiveMap G Q pivot messages statements coins hcompatible tape)) Q =
      Polygero.openOracle (oracle G messages tape) Q :=
  toSim_opening G Q pivot messages _ _ _ tape

theorem adaptiveMap_injective :
    Function.Injective (adaptiveMap G Q pivot messages statements coins hcompatible) := by
  intro first second heq
  have hopen : Polygero.openOracle (oracle G messages first) Q =
      Polygero.openOracle (oracle G messages second) Q := by
    rw [← adaptiveMap_opening G Q pivot messages statements coins hcompatible first,
      ← adaptiveMap_opening G Q pivot messages statements coins hcompatible second, heq]
  have hsecond : adaptiveMap G Q pivot messages statements coins hcompatible second =
      toSim G Q pivot messages
        (statements (Polygero.openOracle (oracle G messages first) Q))
        (hcompatible (Polygero.openOracle (oracle G messages first) Q))
        (coins (Polygero.openOracle (oracle G messages first) Q)) second := by
    unfold adaptiveMap
    rw [hopen]
  exact toSim_injective G Q pivot messages _ _ _ (heq.trans hsecond)

noncomputable def adaptiveEquiv [Fintype F] : Tape G nw nq s ≃ Tape G nw nq s :=
  Equiv.ofBijective (adaptiveMap G Q pivot messages statements coins hcompatible)
    (adaptiveMap_injective G Q pivot messages statements coins hcompatible).bijective_of_finite

noncomputable def adaptiveRealPayload (tape : Tape G nw nq s) : LigeroPayload F (r+w) s :=
  let opening := Polygero.openOracle (oracle G messages tape) Q
  payload G G.positive (statements opening) (coins opening) messages tape

noncomputable def adaptiveSimPayload (tape : Tape G nw nq s) : LigeroPayload F (r+w) s :=
  let opening := Polygero.openOracle (oracle G 0 tape) Q
  simPayload G G.positive Q pivot (statements opening) (coins opening) tape

/-- One change of variables preserves the entire backend view, for an
adaptive statement and adaptive batching coin read from the opened columns. -/
theorem adaptive_translate [Fintype F] (tape : Tape G nw nq s) :
    Polygero.openOracle
        (oracle G 0 (adaptiveEquiv G Q pivot messages statements coins hcompatible tape)) Q =
      Polygero.openOracle (oracle G messages tape) Q ∧
    adaptiveSimPayload G Q pivot statements coins
        (adaptiveEquiv G Q pivot messages statements coins hcompatible tape) =
      adaptiveRealPayload G Q messages statements coins tape := by
  have hopen := adaptiveMap_opening G Q pivot messages statements coins hcompatible tape
  refine ⟨hopen, ?_⟩
  unfold adaptiveSimPayload adaptiveRealPayload
  change simPayload G G.positive Q pivot
      (statements (Polygero.openOracle
        (oracle G 0 (adaptiveMap G Q pivot messages statements coins hcompatible tape)) Q))
      (coins (Polygero.openOracle
        (oracle G 0 (adaptiveMap G Q pivot messages statements coins hcompatible tape)) Q)) _ = _
  rw [hopen]
  exact toSim_payload G Q pivot messages _ _ _ tape

end Adaptive

end LfzkV2.PolygeroZk
