import polygero.Local.FullConsistency
import polygero.Reduction.ChildInstance
import polygero.Local.WireReuse

/-! Concrete algebra behind the parent-envelope grinding obstruction.
The parent payload is canonical and the child witness is its actual packed
coefficient vector. The pair of contradictory linear equations has distinct
exception lines as the decoded witness value varies. -/

namespace RecursivePolygero.ProfileAnalysis.GrindingAlgebra
open Polynomial Finset Codes LigeroFamily Local Local.Polygero
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def primaryPolynomial {m k s : ℕ} (hk : 1 ≤ k)
    (B : Challenge F m s) (f : Fin m → DegreeLT F k) : DegreeLT F (k+s) :=
  ⟨∑ i, (B i : F[X]) * (f i : F[X]), by
    apply (degreeLT F (k+s)).sum_mem
    intro i _
    have h := mul_mem_degreeLT_add_sub_one (by omega : 1 ≤ s+1) hk (B i).2 (f i).2
    convert h using 1
    congr 1
    omega⟩

noncomputable def canonicalPayload (I : Instance F) (hk : 1 ≤ I.r+I.w)
    (σ : I.layer.Statement) (coin : I.layer.Coin)
    (f : Fin (rowCount I.nw I.nq) → DegreeLT F (I.r+I.w)) : I.layer.Payload :=
  ⟨primaryPolynomial hk coin.2 f,
    (responseSemantics I.domain (by have := I.primary_le; omega)
      I.primary_le I.layout σ coin.1).canonical 0 f⟩

/-- The actual global test for this payload is precisely the decoded
arithmetic exception equation; this implication also gives completeness. -/
theorem canonicalPayload_global (I : Instance F) (hk : 1 ≤ I.r+I.w)
    (σ : I.layer.Statement) (coin : I.layer.Coin)
    (f : Fin (rowCount I.nw I.nq) → DegreeLT F (I.r+I.w))
    (he : finiteDot coin.1
      (PolynomialDirect.decodedLinearResidual I.domain I.layout σ (extendRows f)) =
      -PolynomialDirect.decodedZRMaskSum I.domain I.layout (extendRows f)) :
    globalCheck I.domain I.layout σ coin.1 (canonicalPayload I hk σ coin f) := by
  change (∑ i : Fin I.q, (((PolynomialDirect.responseSemantics I.domain
      (by have := I.primary_le; omega) I.primary_le I.layout σ coin.1).canonical
        0 (extendRows f)) : F[X]).eval
      (I.domain.point (logicalWitnessPosition I.layout i))) = _
  rw [PolynomialDirect.responseCanonical_logical_sum]
  rw [he]
  ring

/-- A piecewise oracle need only agree with the selected polynomial tableau
on the sampled set. All three verifier relations hold there. -/
theorem canonicalPayload_accepts (I : Instance F) (hk : 1 ≤ I.r+I.w)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (f : Fin (rowCount I.nw I.nq) → DegreeLT F (I.r+I.w)) (Q : I.layer.Query)
    (he : finiteDot coin.1
      (PolynomialDirect.decodedLinearResidual I.domain I.layout σ (extendRows f)) =
      -PolynomialDirect.decodedZRMaskSum I.domain I.layout (extendRows f))
    (hmask : ∀ j ∈ Q.coordinates, W.proximityMask j = 0)
    (hagrees : ∀ i j, j ∈ Q.coordinates → oracleWords W.ordinary i j =
      (f i : F[X]).eval ((primaryCode I.domain I.primary_le).node j))
    (hprod : ∀ g : Fin I.nq, (f (leftIndex g) : F[X]) * (f (rightIndex g) : F[X]) =
      (f (outputIndex g) : F[X])) :
    I.layer.verify σ W coin (canonicalPayload I hk σ coin f) Q := by
  apply (verify_openOracle_iff I.domain (by have := I.primary_le; omega)
    I.primary_le I.layout σ W coin _ Q).mpr
  refine ⟨canonicalPayload_global I hk σ coin f he, ?_⟩
  intro j hj
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_, ?_, ?_⟩
  · simp only [canonicalPayload, primaryPolynomial, eval_finsetSum, eval_mul,
      response, hmask j hj, add_zero]
    exact sum_congr rfl (fun i _ => by rw [hagrees i j hj]; rfl)
  · change (((responseSemantics I.domain _ I.primary_le I.layout σ coin.1).canonical
      0 f) : F[X]).eval ((primaryCode I.domain I.primary_le).node j) = _
    calc
      _ = linearPointwise I.domain (by have := I.primary_le; omega) I.layout σ coin.1 j
          (fun i => (f i : F[X]).eval ((primaryCode I.domain I.primary_le).node j)) :=
        (responseSemantics I.domain (by have := I.primary_le; omega) I.primary_le
          I.layout σ coin.1).canonical_eval 0 f j
      _ = _ := by
        congr 1
        funext i
        exact (hagrees i j hj).symm
  · intro g
    have hp := congrArg (fun p : F[X] => p.eval ((primaryCode I.domain I.primary_le).node j)) (hprod g)
    have hl := hagrees (leftIndex g) j hj
    have hr := hagrees (rightIndex g) j hj
    have ho := hagrees (outputIndex g) j hj
    simp only [leftIndex, rightIndex, outputIndex, oracleWords_core] at hl hr ho
    rw [hl, hr, ho]
    exact (by simpa only [eval_mul, leftIndex, rightIndex, outputIndex] using hp)

/-- The child coefficient witness is fixed before the parent query: it is
the same packed payload for every query on which the parent accepts. -/
theorem packed_child_satisfies {I : Instance F} (child : Child I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (u : I.layer.Payload) (Q : I.layer.Query)
    (hv : I.layer.verify σ W coin u Q) :
    child.instance.layer.satisfies (child.link.statement σ W coin Q)
      (unflatten (pack child.packing u)) := by
  exact (packed_response_satisfies I.domain (by have := I.primary_le; omega) I.layout σ
    child.packing coin Q (openOracle W Q) u hv).2

/-- The same public linear form is asserted to have values zero and one. -/
noncomputable def contradictoryStatement {d slots : ℕ} (j : Slots d slots) :
    ConstraintSystem F d 0 slots Bool :=
  linearStatement (fun _ => LinearMap.proj j) (fun e => if e then 1 else 0)

omit [Fintype F] [DecidableEq F] in
theorem contradictoryStatement_false {d slots : ℕ} (j : Slots d slots) :
    ¬ (contradictoryStatement (F := F) j).Language := by
  rintro ⟨w, hw⟩
  have h := (linearStatement_satisfies (fun _ => LinearMap.proj j)
    (fun e : Bool => if e then 1 else 0) w).mp hw
  have h0 := h false
  have h1 := h true
  simp only [Bool.false_eq_true, ↓reduceIte, LinearMap.proj_apply] at h0 h1
  exact zero_ne_one (h0.symm.trans h1)

omit [Fintype F] [DecidableEq F] in
/-- Its residual pair is exactly `(a,a-1)`, for the actual decoded value `a`. -/
theorem contradictoryStatement_residual {q r w n d : ℕ}
    (D : ReedSolomon.Domain F r w n) (layout : ConstraintLayout F q w)
    (j : Slots d q) (f : Fin (rowCount d 0) → DegreeLT F (r+w)) (e : Bool) :
    PolynomialDirect.decodedLinearResidual D layout (contradictoryStatement j)
      (extendRows f) e =
      (f (coreIndex .linear j.1) : F[X]).eval
        (D.point (logicalWitnessPosition layout j.2)) - (if e then 1 else 0) := by
  unfold PolynomialDirect.decodedLinearResidual contradictoryStatement
  rw [linearStatement_value]
  simp only [linearStatement, flatten, LinearMap.proj_apply,
    PolynomialDirect.decodedMessages, extendRows_core]

omit [Fintype F] [DecidableEq F] in
/-- Two different decoded values cannot share a nonzero exceptional weight
pair. Hence their arithmetic exception lines are genuinely distinct. -/
theorem exception_lines_intersect_only_zero (a b x y : F) (hab : a ≠ b)
    (ha : x*a + y*(a-1) = 0) (hb : x*b + y*(b-1) = 0) :
    x = 0 ∧ y = 0 := by
  have hs : (a-b)*(x+y) = 0 := by linear_combination ha-hb
  have hxy : x+y = 0 := (mul_eq_zero.mp hs).resolve_left (sub_ne_zero.mpr hab)
  have hy : y = 0 := by linear_combination a*hxy-ha
  constructor
  · simpa [hy] using hxy
  · exact hy

omit [Fintype F] [DecidableEq F] in
/-- A normalized common-root polynomial supplies distinct candidate rows
that agree on any prescribed set of fewer than `k` code coordinates. -/
theorem exists_normalized_common_roots (T : Finset F) (y : F) (hy : y ∉ T)
    (k : ℕ) (hk : T.card < k) :
    ∃ g : DegreeLT F k, (g : F[X]).eval y = 1 ∧ ∀ x ∈ T, (g : F[X]).eval x = 0 := by
  let p : F[X] := ∏ x ∈ T, (X-C x)
  have hp0 : p ≠ 0 := (monic_prod_X_sub_C id T).ne_zero
  have hpdeg : p ∈ degreeLT F k := by
    rw [mem_degreeLT, degree_eq_natDegree hp0]
    simpa only [p, natDegree_finsetProd_X_sub_C_eq_card, Nat.cast_lt] using hk
  have hpy : p.eval y ≠ 0 := by
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact prod_ne_zero_iff.mpr (fun x hx => sub_ne_zero.mpr (fun he => hy (he ▸ hx)))
  refine ⟨⟨(p.eval y)⁻¹ • p, (degreeLT F k).smul_mem _ hpdeg⟩, ?_, ?_⟩
  · simp only [eval_smul, smul_eq_mul, inv_mul_cancel₀ hpy]
  · intro x hx
    have hpx : p.eval x = 0 := by
      simp only [p, eval_prod, eval_sub, eval_X, eval_C]
      exact prod_eq_zero hx (by simp)
    simp only [eval_smul, hpx, smul_zero]

/-- Populate the actual physical row coordinates from arbitrary words. -/
noncomputable def physicalOracle {nw nq n : ℕ}
    (v : Fin (rowCount nw nq) → Fin n → F) : Oracle F nw nq n :=
  ⟨⟨fun b r => v (coreIndex b r), fun kind => v (maskIndex kind)⟩, 0⟩

omit [Fintype F] [DecidableEq F] in
theorem physicalOracle_words {nw nq n : ℕ}
    (v : Fin (rowCount nw nq) → Fin n → F) (i : Fin (rowCount nw nq)) (j : Fin n) :
    oracleWords (physicalOracle v).ordinary i j = v i j := by
  have he := congrArg (fun i => v i j) ((rowEquiv nw nq).symm_apply_apply i)
  cases hi : rowEquiv nw nq i with
  | inl core => simpa only [hi, physicalOracle, oracleWords, coreIndex, indexOf] using he
  | inr kind => simpa only [hi, physicalOracle, oracleWords, maskIndex, indexOf] using he

noncomputable def candidateRows {d k : ℕ} (row : Fin d) (g : DegreeLT F k) (a : F) :
    Fin (rowCount d 0) → DegreeLT F k :=
  fun i => if i = coreIndex .linear row then a • g else 0

noncomputable def mixtureOracle {d r w n : ℕ} (D : ReedSolomon.Domain F r w n)
    (row : Fin d) (g : DegreeLT F (r+w)) (label : Fin n → F) : Oracle F d 0 n :=
  physicalOracle (fun i j => if i = coreIndex .linear row then
    label j * (g : F[X]).eval (D.point (codePosition j)) else 0)

omit [Fintype F] [DecidableEq F] in
/-- Each block may choose its own scalar tableau. The common zero columns
agree with all candidates, independently of the block label. -/
theorem mixtureOracle_agrees {d r w n : ℕ} (D : ReedSolomon.Domain F r w n)
    (row : Fin d) (g : DegreeLT F (r+w)) (label : Fin n → F) (a : F)
    (j : Fin n) (hj : label j = a ∨ (g : F[X]).eval (D.point (codePosition j)) = 0)
    (i : Fin (rowCount d 0)) :
    oracleWords (mixtureOracle D row g label).ordinary i j =
      (candidateRows row g a i : F[X]).eval (D.point (codePosition j)) := by
  rw [mixtureOracle, physicalOracle_words]
  by_cases hi : i = coreIndex .linear row
  · simp only [hi, candidateRows, ite_true, Submodule.coe_smul_of_tower,
      eval_smul, smul_eq_mul]
    rcases hj with hj | hj
    · rw [hj]
    · rw [hj, mul_zero, mul_zero]
  · simp only [hi, if_false, candidateRows, ZeroMemClass.coe_zero, eval_zero]

omit [Fintype F] [DecidableEq F] in
theorem candidateRows_residual {q r w n d : ℕ} (D : ReedSolomon.Domain F r w n)
    (layout : ConstraintLayout F q w) (j : Slots d q) (g : DegreeLT F (r+w))
    (hg : (g : F[X]).eval (D.point (logicalWitnessPosition layout j.2)) = 1)
    (a : F) (e : Bool) :
    PolynomialDirect.decodedLinearResidual D layout (contradictoryStatement j)
      (extendRows (candidateRows j.1 g a)) e = a - (if e then 1 else 0) := by
  rw [contradictoryStatement_residual]
  simp only [candidateRows, ite_true, Submodule.coe_smul_of_tower, eval_smul,
    hg, smul_eq_mul, mul_one]

omit [Fintype F] [DecidableEq F] in
theorem candidateRows_mask {d k : ℕ} (row : Fin d) (g : DegreeLT F k) (a : F)
    (kind : LinearConstraintMask) : candidateRows row g a (maskIndex kind) = 0 := by
  apply if_neg
  intro h
  have he := congrArg (rowEquiv d 0) h
  simp only [maskIndex, coreIndex, indexOf, Equiv.apply_symm_apply] at he
  cases he

omit [Fintype F] [DecidableEq F] in
theorem mixtureOracle_checkedMask {d r w n : ℕ} (D : ReedSolomon.Domain F r w n)
    (row : Fin d) (g : DegreeLT F (r+w)) (label : Fin n → F) :
    (mixtureOracle D row g label).ordinary.checkedMask = 0 := by
  funext kind col
  apply if_neg
  intro h
  have he := congrArg (rowEquiv d 0) h
  simp only [maskIndex, coreIndex, indexOf, Equiv.apply_symm_apply] at he
  cases he

omit [Fintype F] [DecidableEq F] in
theorem candidateRows_ZRMaskSum {q r w n d : ℕ} (D : ReedSolomon.Domain F r w n)
    (layout : ConstraintLayout F q w) (row : Fin d) (g : DegreeLT F (r+w)) (a : F) :
    PolynomialDirect.decodedZRMaskSum D layout (extendRows (candidateRows row g a)) = 0 := by
  simp only [PolynomialDirect.decodedZRMaskSum, extendRows_mask, candidateRows_mask,
    ZeroMemClass.coe_zero, eval_zero, sum_const_zero]

omit [Fintype F] [DecidableEq F] in
/-- The concrete verifier's exception equation is the claimed line in its
two linear-weight coordinates; no abstract exception oracle is assumed. -/
theorem candidateRows_exception {q r w n d : ℕ} (D : ReedSolomon.Domain F r w n)
    (layout : ConstraintLayout F q w) (j : Slots d q) (g : DegreeLT F (r+w))
    (hg : (g : F[X]).eval (D.point (logicalWitnessPosition layout j.2)) = 1)
    (a : F) (weights : Bool → F)
    (he : weights false * a + weights true * (a-1) = 0) :
    finiteDot weights (PolynomialDirect.decodedLinearResidual D layout
      (contradictoryStatement j) (extendRows (candidateRows j.1 g a))) =
      -PolynomialDirect.decodedZRMaskSum D layout (extendRows (candidateRows j.1 g a)) := by
  rw [candidateRows_ZRMaskSum, neg_zero]
  simpa only [finiteDot, Fintype.sum_bool, candidateRows_residual D layout j g hg,
    Bool.false_eq_true, ↓reduceIte, sub_zero, add_comm] using he

/-- The concrete parent parameters needed by the construction. They leave
the code domain, slot layout, and row/query dimensions unrestricted. -/
noncomputable def linearInstance {q r w n : ℕ} (D : ReedSolomon.Domain F r w n)
    (layout : ConstraintLayout F q w) (d s t : ℕ)
    (hprimary : r+w+s ≤ n) (hquery : t ≤ n) : Instance F where
  q := q
  r := r
  w := w
  n := n
  nw := d
  nq := 0
  s := s
  t := t
  Equations := Bool
  equationsFinite := inferInstance
  equationsDecidable := inferInstance
  domain := D
  layout := layout
  primary_le := hprimary
  query_le := hquery

omit [Fintype F] [DecidableEq F] in
/-- This construction is already in Polygero's core-only unmasked wire
format; the optional masks supply no commitment entropy. -/
theorem mixtureOracle_wire {q r w n : ℕ} (D : ReedSolomon.Domain F r w n)
    (layout : ConstraintLayout F q w) (d s t : ℕ) (hprimary : r+w+s ≤ n)
    (hquery : t ≤ n) (row : Fin d) (g : DegreeLT F (r+w)) (label : Fin n → F) :
    let I := linearInstance D layout d s t hprimary hquery
    I.expandWireOracle false (I.compressWireOracle false (mixtureOracle D row g label)) =
      mixtureOracle D row g label := by
  apply Instance.expand_compress
  intro _
  exact ⟨mixtureOracle_checkedMask D row g label, rfl⟩

/-- Direct actual-verifier realization of the mixture construction. The
parent coin may be chosen first; the one canonical payload then works on
every parent query contained in that candidate's common-root/block set. -/
theorem mixture_accepts {q r w n : ℕ} (D : ReedSolomon.Domain F r w n)
    (layout : ConstraintLayout F q w) (d s t : ℕ) (hprimary : r+w+s ≤ n)
    (hquery : t ≤ n) (hk : 1 ≤ r+w) (j : Slots d q)
    (g : DegreeLT F (r+w))
    (hg : (g : F[X]).eval (D.point (logicalWitnessPosition layout j.2)) = 1)
    (label : Fin n → F) (a : F)
    (coin : (linearInstance D layout d s t hprimary hquery).layer.Coin)
    (he : coin.1 false * a + coin.1 true * (a-1) = 0)
    (Q : QuerySet n t)
    (hQ : ∀ col ∈ Q.coordinates,
      label col = a ∨ (g : F[X]).eval (D.point (codePosition col)) = 0) :
    (linearInstance D layout d s t hprimary hquery).layer.verify
      (contradictoryStatement j) (mixtureOracle D j.1 g label) coin
      (canonicalPayload (linearInstance D layout d s t hprimary hquery) hk
        (contradictoryStatement j) coin (candidateRows j.1 g a)) Q := by
  apply canonicalPayload_accepts
  · exact candidateRows_exception D layout j g hg a coin.1 he
  · intro col _
    rfl
  · intro i col hc
    exact mixtureOracle_agrees D j.1 g label a col (hQ col hc) i
  · intro g
    exact g.elim0

omit [Fintype F] [DecidableEq F] in
/-- In the actual disjoint code/message domain, every prescribed set of
`k-1` code columns can be the common zero set while a logical slot is one. -/
theorem exists_domain_common_roots {q r w n : ℕ} (D : ReedSolomon.Domain F r w n)
    (layout : ConstraintLayout F q w) (slot : Fin q) (A : Finset (Fin n))
    (hA : A.card < r+w) :
    ∃ g : DegreeLT F (r+w),
      (g : F[X]).eval (D.point (logicalWitnessPosition layout slot)) = 1 ∧
      ∀ col ∈ A, (g : F[X]).eval (D.point (codePosition col)) = 0 := by
  let T := A.image (fun col => D.point (codePosition col))
  have hT : T.card < r+w := (card_image_le).trans_lt hA
  have hy : D.point (logicalWitnessPosition layout slot) ∉ T := by
    intro hy
    obtain ⟨col, _, he⟩ := mem_image.mp hy
    have h := D.injective he
    simp only [codePosition, logicalWitnessPosition, witnessPosition] at h
    cases h
  obtain ⟨g, hg, hroots⟩ := exists_normalized_common_roots T _ hy (r+w) hT
  exact ⟨g, hg, fun col hc => hroots _ (mem_image.mpr ⟨col, hc, rfl⟩)⟩

noncomputable def exceptionLine (a : F) : Finset (F × F) :=
  univ.filter (fun xy => xy.1*a + xy.2*(a-1) = 0)

noncomputable def exceptionLineEquiv (a : F) : F ≃ ↥(exceptionLine a) where
  toFun t := ⟨((1-a)*t, a*t), mem_filter.mpr ⟨mem_univ _, by ring⟩⟩
  invFun xy := xy.1.1 + xy.1.2
  left_inv t := by dsimp; ring
  right_inv xy := by
    apply Subtype.ext
    have h := (mem_filter.mp xy.2).2
    apply Prod.ext
    · dsimp
      linear_combination -h
    · dsimp
      linear_combination h

theorem exceptionLine_card (a : F) : (exceptionLine a).card = Fintype.card F := by
  exact (Fintype.card_coe (exceptionLine a)).symm.trans
    (Fintype.card_congr (exceptionLineEquiv a).symm)

theorem exceptionLine_inter (a b : F) (hab : a ≠ b) :
    exceptionLine a ∩ exceptionLine b = {(0,0)} := by
  ext xy
  simp only [mem_inter, exceptionLine, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨ha,hb⟩
    obtain ⟨hx,hy⟩ := exception_lines_intersect_only_zero a b xy.1 xy.2 hab ha hb
    exact Prod.ext hx hy
  · rintro rfl
    simp

/-- Three distinct decoded values give exactly `3|F|-2` favorable parent
weight pairs, even in characteristic two. -/
theorem three_exceptionLines_card (a b c : F) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ((exceptionLine a ∪ exceptionLine b) ∪ exceptionLine c).card + 2 = 3 * Fintype.card F := by
  have h1 := card_union_add_card_inter (exceptionLine a) (exceptionLine b)
  have h2 := card_union_add_card_inter (exceptionLine a ∪ exceptionLine b) (exceptionLine c)
  have h3 : (exceptionLine a ∪ exceptionLine b) ∩ exceptionLine c = {(0,0)} := by
    rw [union_inter_distrib_right, exceptionLine_inter a c hac, exceptionLine_inter b c hbc,
      union_self]
  rw [exceptionLine_card a, exceptionLine_card b, exceptionLine_inter a b hab, card_singleton] at h1
  rw [h3, card_singleton, exceptionLine_card c] at h2
  omega

theorem three_exceptionLines_mean (a b c : F) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    mean (fun xy : F × F => indicator
      (xy ∈ (exceptionLine a ∪ exceptionLine b) ∪ exceptionLine c)) =
      3 / (Fintype.card F : ℚ) - 2 / (Fintype.card F : ℚ)^2 := by
  have hm : mean (fun xy : F × F => indicator
      (xy ∈ (exceptionLine a ∪ exceptionLine b) ∪ exceptionLine c)) =
      (((exceptionLine a ∪ exceptionLine b) ∪ exceptionLine c).card : ℚ) /
        Fintype.card (F × F) := by
    rw [mean_indicator]
    congr 1
    congr 1
    congr 1
    ext xy
    simp
  rw [hm, Fintype.card_prod]
  have hcq : ((((exceptionLine a ∪ exceptionLine b) ∪ exceptionLine c).card : ℚ) + 2) =
      3 * (Fintype.card F : ℚ) := by
    exact_mod_cast three_exceptionLines_card a b c hab hac hbc
  have hq : (Fintype.card F : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  push_cast
  field_simp
  nlinarith [hcq]

/-- The corresponding probability for the verifier's actual Boolean-indexed
linear weight vector. The ordering is `(false,true)`. -/
theorem three_weight_exceptions_mean (a b c : F) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    mean (fun weights : Bool → F => indicator
      ((weights false, weights true) ∈ (exceptionLine a ∪ exceptionLine b) ∪ exceptionLine c)) =
      3 / (Fintype.card F : ℚ) - 2 / (Fintype.card F : ℚ)^2 := by
  let e := Equiv.boolArrowEquivProd F
  let f : F × F → ℚ := fun xy => indicator
    (xy ∈ (exceptionLine a ∪ exceptionLine b) ∪ exceptionLine c)
  have he : mean (fun weights => f (e weights)) = mean f := by
    unfold mean
    rw [Fintype.card_congr e, Fintype.sum_equiv e _ f (fun _ => rfl)]
  exact he.trans (three_exceptionLines_mean a b c hab hac hbc)

theorem three_coin_exceptions_mean (d s : ℕ) (a b c : F)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    mean (fun coin : Coin F Bool d 0 s => indicator
      ((coin.1 false, coin.1 true) ∈ (exceptionLine a ∪ exceptionLine b) ∪ exceptionLine c)) =
      3 / (Fintype.card F : ℚ) - 2 / (Fintype.card F : ℚ)^2 := by
  rw [mean_prod]
  simp only [mean_const]
  exact three_weight_exceptions_mean a b c hab hac hbc

end RecursivePolygero.ProfileAnalysis.GrindingAlgebra
