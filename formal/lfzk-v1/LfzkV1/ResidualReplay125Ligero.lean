import LfzkV1.ResidualReplay125
import LfzkV1.ReplayDecode125
import LfzkV1.Encode
import LigeroFamily.Protocol.MaskScheme

/-! The fixed-opening replay uses exactly the verifier's combined-target and opened-column checks. -/

open BigOperators MvPolynomial LigeroFamily

set_option autoImplicit false

namespace LfzkV1.ResidualReplay125

variable {σ : Type*} {F E : Type} [Field F] {r w n nw nq : ℕ}

noncomputable def evalStatement (x : σ → F) (S : ConstraintSystem (Poly σ F) nw nq w E) :
    ConstraintSystem F nw nq w E where
  coefficient e b row i := eval x (S.coefficient e b row i)
  target e := eval x (S.target e)

def StatementBounded (S : ConstraintSystem (Poly σ F) nw nq w E) (d : ℕ) : Prop :=
  (∀ e b row i, (S.coefficient e b row i).totalDegree ≤ d) ∧
  ∀ e, (S.target e).totalDegree ≤ d

section Place

variable {ninp M nt nlin : ℕ}

open Classical in
/-- Place the symbolic coefficients in the exact linear cells that `encodeSystem` uses. -/
noncomputable def encodeRows (pl : Encode.Placement ninp M w nw nq nt)
    (lin : Fin nlin → Row σ F ninp M)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) :
    ConstraintSystem (Poly σ F) nw nq w (Fin nlin ⊕ (Fin nt × Encode.QSide)) where
  coefficient
    | .inl e, .linear, row, i =>
        if h : ∃ s, pl.cell s = (row, i) then
          (Classical.choose h).elim (lin e).cw (lin e).cp
        else 0
    | .inl _, .left, _, _ | .inl _, .right, _, _
        | .inl _, .output, _, _ => 0
    | .inr (j, side), b, row, i => C (Encode.copyRow pl j side (tri j) b row i : F)
  target
    | .inl e => (lin e).rhs
    | .inr _ => 0

theorem eval_encodeRows (pl : Encode.Placement ninp M w nw nq nt)
    (lin : Fin nlin → Row σ F ninp M)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) (x : σ → F) :
    evalStatement x (encodeRows pl lin tri) = Encode.encodeSystem pl (fun e => (lin e).eval x) tri := by
  rw [evalStatement, Encode.encodeSystem, ConstraintSystem.mk.injEq]
  constructor
  · funext e b row i
    cases e with
    | inl e =>
      cases b
      · change Fin nw at row
        change eval x
              (if h : ∃ s, pl.cell s = (row, i) then
                (Classical.choose h).elim (lin e).cw (lin e).cp else 0) =
          Encode.spread pl (Sum.elim ((lin e).eval x).cw ((lin e).eval x).cp) (row, i)
        rw [Encode.spread]
        split_ifs with h
        · cases Classical.choose h <;> rfl
        · exact map_zero _
      · simp [encodeRows, Encode.rowCoeff]
      · simp [encodeRows, Encode.rowCoeff]
      · simp [encodeRows, Encode.rowCoeff]
    | inr t =>
      obtain ⟨j, side⟩ := t
      simp [encodeRows]
  · funext e
    cases e <;> simp [encodeRows, Row.eval]

theorem encodeRows_bounded (pl : Encode.Placement ninp M w nw nq nt)
    {lin : Fin nlin → Row σ F ninp M} {d : ℕ} (hlin : ∀ e, (lin e).Bounded d)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M)) :
    StatementBounded (encodeRows pl lin tri) d := by
  constructor
  · intro e b row i
    cases e with
    | inl e =>
      cases b
      · simp only [encodeRows]
        split_ifs with h
        · cases Classical.choose h with
          | inl j => exact (hlin e).1 j
          | inr j => exact (hlin e).2.1 j
        · simp
      · simp [encodeRows]
      · simp [encodeRows]
      · simp [encodeRows]
    | inr t =>
      obtain ⟨j, side⟩ := t
      exact degree_const _ _
  · intro e
    cases e with
    | inl e => exact (hlin e).2.2
    | inr _ => simp [encodeRows]

end Place

section Interpolate

open MultiplicativeCode

/-- Expand the codeword with zero random prefix into the images of the witness basis. -/
theorem encode_zero_eq_sum (code : MultiplicativeCode F r w n) (v : Fin w → F) :
    code.encode 0 v =
      ∑ i : Fin w, v i • code.encode 0 (fun j => if j = i then 1 else 0) := by
  apply code.base_unique (code.encode_mem _ _) (Submodule.sum_mem _
    fun _ _ => Submodule.smul_mem _ _ (code.encode_mem _ _)) (messagePositions r w n)
    (by simp [code.k_eq])
  intro i hi
  cases i with
  | inl msg =>
    cases msg with
    | inl j =>
      change code.encode 0 v (randomPosition j) =
        (∑ i : Fin w, v i • code.encode 0 (fun j => if j = i then 1 else 0)) (randomPosition j)
      simp only [Finset.sum_apply, Pi.smul_apply, encode_random, Pi.zero_apply, smul_eq_mul,
        mul_zero, Finset.sum_const_zero]
    | inr j =>
      change code.encode 0 v (witnessPosition j) =
        (∑ i : Fin w, v i • code.encode 0 (fun j => if j = i then 1 else 0)) (witnessPosition j)
      simp only [Finset.sum_apply, Pi.smul_apply, encode_witness, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  | inr j => simp [messagePositions] at hi

noncomputable def encodePoly (code : MultiplicativeCode F r w n)
    (v : Fin w → Poly σ F) (pos : Position r w n) : Poly σ F :=
  ∑ i : Fin w, v i * C (code.encode 0 (fun j => if j = i then 1 else 0) pos)

theorem eval_encodePoly (x : σ → F) (code : MultiplicativeCode F r w n)
    (v : Fin w → Poly σ F) (pos : Position r w n) :
    eval x (encodePoly code v pos) = code.encode 0 (fun i => eval x (v i)) pos := by
  rw [encodePoly, map_sum, encode_zero_eq_sum, Finset.sum_apply]
  simp [Pi.smul_apply, smul_eq_mul]

theorem degree_encodePoly (code : MultiplicativeCode F r w n)
    {v : Fin w → Poly σ F} {d : ℕ} (hv : ∀ i, (v i).totalDegree ≤ d) (pos : Position r w n) :
    (encodePoly code v pos).totalDegree ≤ d :=
  totalDegree_finsetSum_le fun i _ => degree_scale _ (hv i)

end Interpolate

section Dot

variable [Fintype E] {CheckedMask DirectMask : Type} [Fintype CheckedMask]
variable {repetitions : ℕ}

/-- Fixed Ligero challenges, responses, opened values, and linear masks leave only the
combined target and coefficient rows dependent on replayed field challenges. -/
noncomputable def linearResidual (code : MultiplicativeCode F r w n)
    (scheme : MaskScheme F CheckedMask DirectMask r w n)
    (S : ConstraintSystem (Poly σ F) nw nq w E) (weights : E → F)
    (response : EvaluationRow F r w n) (query : QuerySet n r)
    (opening : SchemeOpening F CheckedMask DirectMask nw nq repetitions n r query)
    (h : Fin repetitions) : Unit ⊕ ↥query.coordinates → Poly σ F
  | .inl _ => (∑ e, C (weights e) * S.target e) - C (∑ i : Fin w, response (witnessPosition i))
  | .inr j =>
    let pos := codePosition j.1
    (∑ b : CoreBlock, ∑ row : Fin (b.rowCount nw nq),
      encodePoly code (fun i => ∑ e, C (weights e) * S.coefficient e b row i) pos *
        C ((opening j).core b row)) +
      C (scheme.linearAt pos ((opening j).checkedMask h) ((opening j).directMask h)) -
      C (response pos)

omit [Fintype CheckedMask] in
theorem eval_linearResidual_eq_zero (x : σ → F) (code : MultiplicativeCode F r w n)
    (scheme : MaskScheme F CheckedMask DirectMask r w n)
    (S : ConstraintSystem (Poly σ F) nw nq w E) (weights : E → F)
    (response : EvaluationRow F r w n) (query : QuerySet n r)
    (opening : SchemeOpening F CheckedMask DirectMask nw nq repetitions n r query)
    (h : Fin repetitions) :
    SchemeVerifier.LinearAccepts code scheme (evalStatement x S) weights response query opening h ↔
      response ∈ code.response ∧
        ∀ i, eval x (linearResidual code scheme S weights response query opening h i) = 0 := by
  have ht :
      eval x (linearResidual code scheme S weights response query opening h (.inl ())) = 0 ↔
        (∑ i : Fin w, response (witnessPosition i)) =
          (evalStatement x S).combinedTarget weights := by
    simp [linearResidual, evalStatement, ConstraintSystem.combinedTarget, map_sum, sub_eq_zero]
    exact eq_comm
  have hd (j : ↥query.coordinates) :
      eval x (linearResidual code scheme S weights response query opening h (.inr j)) = 0 ↔
        response (codePosition j.1) =
          (∑ b : CoreBlock, ∑ row : Fin (b.rowCount nw nq),
            Verifier.coefficientRow code (evalStatement x S) weights b row (codePosition j.1) *
              (opening j).core b row) +
          scheme.linearAt (codePosition j.1) ((opening j).checkedMask h)
            ((opening j).directMask h) := by
    simp [linearResidual, eval_encodePoly, Verifier.coefficientRow,
      evalStatement, map_sum, sub_eq_zero]
    exact eq_comm
  rw [SchemeVerifier.LinearAccepts]
  constructor
  · rintro ⟨hmem, htarget, hopen⟩
    refine ⟨hmem, ?_⟩
    intro i
    cases i with
    | inl u => cases u; exact ht.mpr htarget
    | inr j => exact (hd j).mpr (hopen j)
  · rintro ⟨hmem, hzero⟩
    exact ⟨hmem, ht.mp (hzero (.inl ())), fun j => (hd j).mp (hzero (.inr j))⟩

omit [Fintype CheckedMask] in
theorem degree_linearResidual (code : MultiplicativeCode F r w n)
    (scheme : MaskScheme F CheckedMask DirectMask r w n)
    {S : ConstraintSystem (Poly σ F) nw nq w E} {d : ℕ} (hS : StatementBounded S d)
    (weights : E → F) (response : EvaluationRow F r w n) (query : QuerySet n r)
    (opening : SchemeOpening F CheckedMask DirectMask nw nq repetitions n r query)
    (h : Fin repetitions) (i : Unit ⊕ ↥query.coordinates) :
    (linearResidual code scheme S weights response query opening h i).totalDegree ≤ d := by
  cases i with
  | inl _ =>
    exact degree_sub
      (totalDegree_finsetSum_le fun e _ => degree_const_mul _ (hS.2 e))
      (degree_const _ _)
  | inr j =>
    refine degree_sub (degree_add ?_ (degree_const _ _)) (degree_const _ _)
    apply totalDegree_finsetSum_le
    intro b _
    apply totalDegree_finsetSum_le
    intro row _
    apply degree_scale
    apply degree_encodePoly
    intro k
    exact totalDegree_finsetSum_le fun e _ => degree_const_mul _ (hS.1 e b row k)

end Dot

section FixedOpening

variable {ninp M nt nlin : ℕ}
variable {CheckedMask DirectMask : Type} [Fintype CheckedMask] {repetitions : ℕ}

abbrev Equations (nlin nt : ℕ) := Fin nlin ⊕ (Fin nt × Encode.QSide)

noncomputable def encodeReplay (pl : Encode.Placement ninp M w nw nq nt) (nlin : ℕ)
    (S : System σ F ninp M) : ConstraintSystem (Poly σ F) nw nq w (Equations nlin nt) :=
  encodeRows pl (fun e : Fin nlin => S.rowAt e.val) (fun j => S.quad[j.val]?)

theorem eval_encodeReplay (pl : Encode.Placement ninp M w nw nq nt) (nlin : ℕ)
    (S : System σ F ninp M) (x : σ → F) :
    evalStatement x (encodeReplay pl nlin S) = Encode.encodeLig pl nlin (S.eval x) := by
  rw [encodeReplay, eval_encodeRows, Encode.encodeLig]
  congr 1
  funext e
  simp only [System.eval, Encode.presentLin, List.getElem?_map, System.rowAt]
  cases S.linear[e.val]? <;> simp [Row.zero, Row.eval, Encode.zeroRow]

theorem encodeReplay_bounded (pl : Encode.Placement ninp M w nw nq nt) (nlin : ℕ)
    {S : System σ F ninp M} {d : ℕ} (hS : S.Bounded d) :
    StatementBounded (encodeReplay pl nlin S) d :=
  encodeRows_bounded pl (fun e => System.rowAt_bounded hS e.val) _

/-- The rows independent of the replay variables, including the code-membership check of the
linear response, must be true on any accepting replay. -/
def fixedChecks (code : MultiplicativeCode F r w n)
    (scheme : MaskScheme F CheckedMask DirectMask r w n) (S : System σ F ninp M)
    (challenge : SchemeChallenge F CheckedMask nw nq repetitions (Equations nlin nt))
    (response : Response F r w n repetitions) (query : QuerySet n r)
    (opening : SchemeOpening F CheckedMask DirectMask nw nq repetitions n r query)
    (pad : Fin M → F) : Prop :=
  (∀ t ∈ S.quad, pad t.2.2 = pad t.1 * pad t.2.1) ∧
  ∀ h : Fin repetitions,
    response.linear h ∈ code.response ∧
    SchemeVerifier.ProximityAccepts code (challenge h).proximity (response.proximity h)
      query opening h ∧
    SchemeVerifier.QuadraticAccepts code scheme (challenge h).quadratic (response.quadratic h)
      query opening h

abbrev ReplayRows {n r : ℕ} (query : QuerySet n r) (repetitions : ℕ) :=
  ℕ ⊕ (Fin repetitions × (Unit ⊕ ↥query.coordinates))

omit [Fintype CheckedMask] in
/-- Field residuals for one selected assignment, followed by literal verifier residuals. -/
noncomputable def jointResidual (code : MultiplicativeCode F r w n)
    (scheme : MaskScheme F CheckedMask DirectMask r w n)
    (pl : Encode.Placement ninp M w nw nq nt) (S : System σ F ninp M)
    (challenge : SchemeChallenge F CheckedMask nw nq repetitions (Equations nlin nt))
    (response : Response F r w n repetitions) (query : QuerySet n r)
    (opening : SchemeOpening F CheckedMask DirectMask nw nq repetitions n r query)
    (wcol : Fin ninp → F) (pad : Fin M → F) : ReplayRows query repetitions → Poly σ F
  | .inl i => (S.rowAt i).residual wcol pad
  | .inr (h, i) =>
    linearResidual code scheme (encodeReplay pl nlin S) (challenge h).linear (response.linear h)
      query opening h i

omit [Fintype CheckedMask] in
theorem degree_jointResidual (code : MultiplicativeCode F r w n)
    (scheme : MaskScheme F CheckedMask DirectMask r w n)
    (pl : Encode.Placement ninp M w nw nq nt) {S : System σ F ninp M} {d : ℕ} (hS : S.Bounded d)
    (challenge : SchemeChallenge F CheckedMask nw nq repetitions (Equations nlin nt))
    (response : Response F r w n repetitions) (query : QuerySet n r)
    (opening : SchemeOpening F CheckedMask DirectMask nw nq repetitions n r query)
    (wcol : Fin ninp → F) (pad : Fin M → F) (i : ReplayRows query repetitions) :
    (jointResidual code scheme pl S challenge response query opening wcol pad i).totalDegree ≤ d := by
  cases i with
  | inl i => exact Row.degree_residual (S.rowAt_bounded hS i) wcol pad
  | inr p =>
    obtain ⟨h, i⟩ := p
    exact degree_linearResidual code scheme (encodeReplay_bounded pl nlin hS) _ _ _ _ h i

/-- Fixed checks and polynomial zeroes exactly characterize the actual two replay tests. -/
theorem eval_jointResidual_eq_zero (x : σ → F) (code : MultiplicativeCode F r w n)
    (scheme : MaskScheme F CheckedMask DirectMask r w n)
    (pl : Encode.Placement ninp M w nw nq nt) (S : System σ F ninp M)
    (challenge : SchemeChallenge F CheckedMask nw nq repetitions (Equations nlin nt))
    (response : Response F r w n repetitions) (query : QuerySet n r)
    (opening : SchemeOpening F CheckedMask DirectMask nw nq repetitions n r query)
    (wcol : Fin ninp → F) (pad : Fin M → F) :
    ((S.eval x).Sat wcol pad ∧ SchemeVerifier.Accepts code scheme
      (Encode.encodeLig pl nlin (S.eval x)) challenge response query opening) ↔
    fixedChecks code scheme S challenge response query opening pad ∧
      ∀ i, eval x (jointResidual code scheme pl S challenge response query opening wcol pad i) = 0 := by
  rw [S.eval_sat_iff, SchemeVerifier.Accepts, ← eval_encodeReplay pl nlin S x]
  constructor
  · rintro ⟨⟨hquad, hrows⟩, hlig⟩
    have hlin := fun h => (eval_linearResidual_eq_zero x code scheme _
      (challenge h).linear (response.linear h) query opening h).mp (hlig h).2.1
    refine ⟨⟨hquad, fun h => ⟨(hlin h).1, (hlig h).1, (hlig h).2.2⟩⟩, ?_⟩
    intro i
    cases i with
    | inl j => exact hrows j
    | inr j => obtain ⟨h, j⟩ := j; exact (hlin h).2 j
  · rintro ⟨⟨hquad, hfixed⟩, hzero⟩
    refine ⟨⟨hquad, fun i => hzero (.inl i)⟩, fun h => ⟨(hfixed h).2.1, ?_, (hfixed h).2.2⟩⟩
    exact (eval_linearResidual_eq_zero x code scheme _ (challenge h).linear (response.linear h)
      query opening h).mpr ⟨(hfixed h).1, fun i => hzero (.inr ⟨h, i⟩)⟩

open Classical in
/-- At fixed messages, openings, batching weights and assignment, the verifier and selected
assignment tests either hold identically whenever the fixed checks pass, or have replay
density at most one row degree over the field size. -/
theorem fixed_opening_split {k d : ℕ} [Fintype F] (code : MultiplicativeCode F r w n)
    (scheme : MaskScheme F CheckedMask DirectMask r w n)
    (pl : Encode.Placement ninp M w nw nq nt) {S : System (Fin k) F ninp M}
    (hS : S.Bounded d)
    (challenge : SchemeChallenge F CheckedMask nw nq repetitions (Equations nlin nt))
    (response : Response F r w n repetitions) (query : QuerySet n r)
    (opening : SchemeOpening F CheckedMask DirectMask nw nq repetitions n r query)
    (wcol : Fin ninp → F) (pad : Fin M → F) :
    let p := jointResidual code scheme pl S challenge response query opening wcol pad
    let accepts := fun x : Fin k → F => (S.eval x).Sat wcol pad ∧
      SchemeVerifier.Accepts code scheme (Encode.encodeLig pl nlin (S.eval x))
        challenge response query opening
    ((∀ i, p i = 0) ∧
      (∀ x, accepts x ↔ fixedChecks code scheme S challenge response query opening pad)) ∨
    ((∃ i, p i ≠ 0) ∧
      ((Finset.univ.filter accepts).card : ℚ≥0) / (Fintype.card F ^ k : ℚ≥0) ≤
        (d : ℚ≥0) / Fintype.card F) := by
  dsimp only
  let p := jointResidual code scheme pl S challenge response query opening wcol pad
  have he (x : Fin k → F) :=
    eval_jointResidual_eq_zero x code scheme pl S challenge response query opening wcol pad
  by_cases hz : ∀ i, p i = 0
  · refine Or.inl ⟨hz, fun x => (he x).trans ?_⟩
    exact ⟨And.left, fun h => ⟨h, identity_accepts p hz x⟩⟩
  · have hnz := not_forall.mp hz
    refine Or.inr ⟨hnz, ?_⟩
    calc
      _ ≤ ((Finset.univ.filter fun x : Fin k → F => ∀ i, eval x (p i) = 0).card : ℚ≥0) /
            (Fintype.card F ^ k : ℚ≥0) := by
        gcongr with x
        exact fun hx => ((he x).mp hx).2
      _ ≤ _ := nonidentity_bound p (degree_jointResidual code scheme pl hS challenge response
        query opening wcol pad) hnz

end FixedOpening

section View

open LfzkV1.ReplayView125 LfzkV1.ReplayDecode125 LfzkV1.TwoFieldV1Rows
open Merkle.RandomOracle
open scoped Classical

variable {Point Answer Out I : Type} {fuel k : ℕ} [Fintype Point] [Fintype Answer] [Fintype I]
variable [Fintype F] [DecidableEq F] {width : I → ℕ}
variable {tree : Tree Point Answer Out fuel} {lookups : Out → List Point} {H : Point → Answer}
variable {CheckedMask DirectMask : Type} [Fintype CheckedMask]
variable {ninp M nt nlin repetitions : ℕ}

/-- For one selected lift, the fixed-opening residual alternative applies
to actual oracle-table counts, with no factor for the number of lifts. -/
theorem fixed_opening_view_split
    (address : I ↪ Unseen tree lookups H) (d : ∀ i, ExactDecoder Answer (Fin (width i) → F))
    (index : (Σ i, Fin (width i)) ≃ Fin k)
    (code : MultiplicativeCode F r w n) (scheme : MaskScheme F CheckedMask DirectMask r w n)
    (pl : Encode.Placement ninp M w nw nq nt) {S : System (Fin k) F ninp M} (hS : S.Bounded 81)
    (challenge : SchemeChallenge F CheckedMask nw nq repetitions (Equations nlin nt))
    (response : Response F r w n repetitions) (query : QuerySet n r)
    (opening : SchemeOpening F CheckedMask DirectMask nw nq repetitions n r query)
    (wcol : Fin ninp → F) (pad : Fin M → F) :
    let p := jointResidual code scheme pl S challenge response query opening wcol pad
    let projected := fun U : Point → Answer => flatten index fun i => (d i).decode (U (address i).val)
    let passes := fun U : Point → Answer => (S.eval (projected U)).Sat wcol pad ∧
      SchemeVerifier.Accepts code scheme (Encode.encodeLig pl nlin (S.eval (projected U)))
        challenge response query opening
    ((∀ i, p i = 0) ∧ (∀ U, passes U ↔ fixedChecks code scheme S challenge response query opening pad)) ∨
      ((Finset.univ.filter fun U : Point → Answer =>
        view tree lookups U = view tree lookups H ∧ passes U).card : ℚ) ≤
        (81 / Fintype.card F) *
          ((Finset.univ.filter fun U : Point → Answer =>
            view tree lookups U = view tree lookups H).card : ℚ) := by
  dsimp only
  let p := jointResidual code scheme pl S challenge response query opening wcol pad
  let projected (U : Point → Answer) := flatten index fun i => (d i).decode (U (address i).val)
  let passes (U : Point → Answer) := (S.eval (projected U)).Sat wcol pad ∧
    SchemeVerifier.Accepts code scheme (Encode.encodeLig pl nlin (S.eval (projected U)))
      challenge response query opening
  have he (U : Point → Answer) := eval_jointResidual_eq_zero (projected U) code scheme pl S
    challenge response query opening wcol pad
  by_cases hid : ∀ i, p i = 0
  · left
    exact ⟨hid, fun U => (he U).trans ⟨And.left, fun h => ⟨h, identity_accepts p hid _⟩⟩⟩
  · right
    simpa only [passes, projected, Nat.cast_ofNat] using view_nonidentity_count_le address d index p
      (degree_jointResidual code scheme pl hS challenge response query opening wcol pad)
      (not_forall.mp hid) passes (fun U h => ((he U.val).mp h).2)

end View

end LfzkV1.ResidualReplay125
