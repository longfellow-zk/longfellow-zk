import LfzkV2.Joint.Backend
import LfzkV2.PolygeroPrimaryMasking

/-!
# Honest linear-only responses

Construct the response polynomials from encoded ordinary rows and the
existing two arithmetic masks. Every field checks the same query set, so
completeness holds for every shared query, not just a random one. There are
no product rows or product-consistency premises in this construction.
-/

namespace LfzkV2.Joint.Honest

open Polynomial LigeroFamily MultiplicativeCode RecursivePolygero RecursivePolygero.Local
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] (I : Instance F)

omit [Fintype F] [DecidableEq F] in
private theorem k_le_n : I.r+I.w ≤ I.n := by have := I.primary_le; omega

noncomputable abbrev code := ReedSolomon.multiplicativeCode I.domain (k_le_n I)
noncomputable abbrev basis := ReedSolomon.maskingBasis I.domain (k_le_n I)

structure Data where
  rows : (block : CoreBlock) → Fin (block.rowCount I.nw I.nq) → (code I).base
  masks : PolygeroMasking.Tape (code I) (logicalSumLinearMap I.layout)
  proximity : DegreeLT F (I.r+I.w+I.s)

def core (data : Data I) : PolygeroMasking.CoreRows F I.r I.w I.n I.nw I.nq := fun b i => (data.rows b i).1

noncomputable def basePolynomial (row : (code I).base) : DegreeLT F (I.r+I.w) :=
  ⟨Classical.choose ((ReedSolomon.mem_evaluationSpace I.domain).mp row.2),
    (Classical.choose_spec ((ReedSolomon.mem_evaluationSpace I.domain).mp row.2)).1⟩

omit [Fintype F] [DecidableEq F] in
theorem basePolynomial_eval (row : (code I).base) (i : Position I.r I.w I.n) :
    (basePolynomial I row : F[X]).eval (I.domain.point i) = row.1 i :=
  ((Classical.choose_spec ((ReedSolomon.mem_evaluationSpace I.domain).mp row.2)).2 i).symm

noncomputable def ordinaryRows (data : Data I) :
    Fin (Polygero.rowCount I.nw I.nq) → DegreeLT F (I.r+I.w) := fun i =>
  match Polygero.rowEquiv I.nw I.nq i with
  | .inl ⟨block,row⟩ => basePolynomial I (data.rows block row)
  | .inr .vCoefficient => basePolynomial I ⟨data.masks.vCoefficient.1, data.masks.vCoefficient.2.1⟩
  | .inr .zRCoefficient => basePolynomial I ⟨data.masks.zRCoefficient.1, data.masks.zRCoefficient.2.1⟩

noncomputable def oracle (data : Data I) : I.layer.Oracle where
  ordinary :=
    { core := fun block row j => core I data block row (codePosition j)
      checkedMask := fun kind j => PolygeroMasking.maskRows data.masks kind (codePosition j) }
  proximityMask j := (data.proximity : F[X]).eval (I.domain.point (codePosition j))

theorem ordinaryRows_eval (data : Data I) (i : Fin (Polygero.rowCount I.nw I.nq)) (j : Fin I.n) :
    (ordinaryRows I data i : F[X]).eval (I.domain.point (codePosition j)) =
      Polygero.oracleWords (oracle I data).ordinary i j := by
  unfold ordinaryRows Polygero.oracleWords
  cases Polygero.rowEquiv I.nw I.nq i with
  | inl row => exact basePolynomial_eval I _ _
  | inr kind => cases kind <;> exact basePolynomial_eval I _ _

noncomputable def arithmeticRow (statement : I.layer.Statement) (weights : I.Equations → F)
    (data : Data I) : (code I).response :=
  ⟨DirectVerifier.linearCore (code I) I.layout statement weights (core I data) +
    PolygeroMasking.response (code I) (basis I) (logicalSumLinearMap I.layout) data.masks,
    (code I).response.add_mem
      (PolygeroMasking.linearCore_mem (code I) I.layout statement weights (core I data)
        (fun b i => (data.rows b i).2))
      (linearMaskMap (code I) (basis I) ∅ (logicalSumLinearMap I.layout) data.masks).2.1⟩

noncomputable def payload (hk : 0 < I.r+I.w) (statement : I.layer.Statement)
    (coin : I.layer.Coin) (data : Data I) : I.layer.Payload where
  primary := PolygeroPrimaryMasking.response hk coin.2 (ordinaryRows I data) data.proximity
  arithmetic := PolynomialDirect.responsePolynomial I.domain (k_le_n I)
    (arithmeticRow I statement coin.1 data).1 (arithmeticRow I statement coin.1 data).2

theorem arithmeticRow_code (statement : I.layer.Statement) (weights : I.Equations → F)
    (data : Data I) (j : Fin I.n) :
    (arithmeticRow I statement weights data).1 (codePosition j) =
      Polygero.linearPointwise I.domain (k_le_n I) I.layout statement weights j
        (fun i => Polygero.oracleWords (oracle I data).ordinary i j) := by
  unfold Polygero.linearPointwise PolynomialDirect.linearPointwise
  simp only [Polygero.extendRows_core, Polygero.extendRows_mask,
    Polygero.oracleWords_core, Polygero.oracleWords_mask]
  simp only [arithmeticRow, PolygeroMasking.response_eq_linearMask,
    DirectVerifier.linearCore, DirectVerifier.linearMask, Pi.add_apply,
    Finset.sum_apply, rowMul_apply, oracle]
  ring

theorem arithmeticRow_sum (statement : I.layer.Statement) (weights : I.Equations → F)
    (data : Data I) (hsat : I.layer.satisfies statement (layoutCoreMessages I.layout (core I data))) :
    logicalSumLinearMap I.layout (witnessValues (arithmeticRow I statement weights data).1) =
      statement.combinedTarget weights := by
  change logicalSumLinearMap I.layout
    (witnessValues (DirectVerifier.linearCore (code I) I.layout statement weights (core I data)) +
      witnessValues (PolygeroMasking.response (code I) (basis I) (logicalSumLinearMap I.layout) data.masks)) = _
  rw [map_add, PolygeroMasking.linearCore_sum_of_satisfies (code I) I.layout statement weights _ hsat]
  exact add_eq_left.mpr
    (linearMaskMap (code I) (basis I) ∅ (logicalSumLinearMap I.layout) data.masks).2.2.2.2

/-- The real polynomials pass the real verifier for every column query. -/
theorem payload_verifies (hlinear : I.nq = 0) (hk : 0 < I.r+I.w)
    (statement : I.layer.Statement) (coin : I.layer.Coin) (data : Data I)
    (hsat : I.layer.satisfies statement (layoutCoreMessages I.layout (core I data))) (Q : I.layer.Query) :
    I.layer.verify statement (oracle I data) coin (payload I hk statement coin data) Q := by
  apply (Polygero.verify_openOracle_iff I.domain (k_le_n I) I.primary_le I.layout
    statement (oracle I data) coin _ Q).2
  constructor
  · unfold Polygero.globalCheck
    simp only [payload, PolynomialDirect.responsePolynomial_eval]
    exact arithmeticRow_sum I statement coin.1 data hsat
  · intro j _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · change (PolygeroPrimaryMasking.response hk coin.2 (ordinaryRows I data) data.proximity : F[X]).eval _ = _
      rw [PolygeroPrimaryMasking.response_eval]
      simp only [ordinaryRows_eval, RecursivePolygero.Local.response,
        PolynomialDirect.primaryCode, oracle]
    · change (PolynomialDirect.responsePolynomial I.domain (k_le_n I)
        (arithmeticRow I statement coin.1 data).1 (arithmeticRow I statement coin.1 data).2 : F[X]).eval _ = _
      rw [PolynomialDirect.responsePolynomial_eval, arithmeticRow_code]
    · intro row
      exact (Nat.not_lt_zero row.val (hlinear ▸ row.isLt)).elim

variable {k s n t : ℕ} (G : Family k s n t)

/-- The arbitrary finite family is complete on the very same query set.
The premise is ordinary statement satisfaction, not backend acceptance. -/
theorem family_verifies (hk : 0 < k) (statements : G.Statement) (coins : G.Coin)
    (data : (i : G.Index) → Data (G.participant i).backend)
    (hsat : ∀ i, (G.participant i).backend.layer.satisfies (statements i)
      (layoutCoreMessages (G.participant i).backend.layout (core _ (data i)))) (Q : QuerySet n t) :
    G.Verify statements (fun i => oracle _ (data i)) coins
      (fun i => payload _ (by rw [(G.participant i).dimension]; exact hk) (statements i) (coins i) (data i)) Q := by
  intro i
  exact payload_verifies (G.participant i).backend (G.participant i).linearOnly
    (by rw [(G.participant i).dimension]; exact hk) _ _ _ (hsat i) _

/-- The honest family and its actual salted Merkle opening satisfy the
compiled verifier. This also covers a singleton or repeated field types. -/
theorem compiled_complete {Salt D Enc : Type} [Inhabited D]
    (scheme : Merkle.MH.Scheme Salt G.Leaf D Enc) (nonce : Fin n → Salt)
    (ht : 0 < t) (hk : 0 < k) (statements : G.Statement) (coins : G.Coin)
    (data : (i : G.Index) → Data (G.participant i).backend)
    (hsat : ∀ i, (G.participant i).backend.layer.satisfies (statements i)
      (layoutCoreMessages (G.participant i).backend.layout (core _ (data i)))) (Q : QuerySet n t) :
    let W : G.Oracle := fun i => oracle _ (data i)
    let a := G.columnsEquiv W
    let response : G.Response := fun i => payload _
      (by rw [(G.participant i).dimension]; exact hk) (statements i) (coins i) (data i)
    (G.compiler ht).Accepts scheme statements (Merkle.MH.root scheme n nonce a) coins response Q
      ⟨Q.coordinates,a,Merkle.MH.openCore scheme n Q.coordinates nonce a⟩ := by
  intro W a response
  refine ⟨rfl,Merkle.MH.mh_core_completeness scheme n Q.coordinates
    ((G.compiler ht).indices_nonempty Q) nonce a,?_⟩
  change (G.compiler ht).protocol.verify statements coins response Q
    ((G.compiler ht).protocol.openOracle (G.columnsEquiv.symm (G.columnsEquiv W)) Q) = true
  rw [Equiv.symm_apply_apply]
  exact (G.compiler_verify ht _ _ _ _ _).mpr (family_verifies G hk statements coins data hsat Q)

end LfzkV2.Joint.Honest
