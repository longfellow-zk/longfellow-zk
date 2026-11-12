import LfzkV2.Current.BackendBody
import LfzkV2.Current.StatementCompiler

/-! The runtime's batching coin representation. Each field first samples
one scalar per affine equation, then `s+1` evaluations for each physical row
in order `u, m, witness`. Interpolation and an explicit row reindexing supply
the algebraic coin; neither monomial coefficients nor an arbitrary physical
row enumeration are used. Both participants draw from one boundary answer. -/
noncomputable section
namespace LfzkV2.Current.BackendChallenges
open Application RecursivePolygero RecursivePolygero.Local RecursivePolygero.Local.Polygero
open LigeroFamily
open scoped Classical

/-- The two arithmetic masks have their actual physical order. -/
def masks : Fin 2 ≃ LinearConstraintMask where
  toFun i := if i = 0 then .vCoefficient else .zRCoefficient
  invFun | .vCoefficient => 0 | .zRCoefficient => 1
  left_inv i := by fin_cases i <;> rfl
  right_inv kind := by cases kind <;> rfl

/-- The linear-only participant has one ordinary core block. -/
def core (nw : ℕ) : Fin nw ≃ CoreRow nw 0 where
  toFun i := ⟨.linear,i⟩
  invFun row := match row with
    | ⟨.linear,i⟩ => i
    | ⟨.left,i⟩ | ⟨.right,i⟩ | ⟨.output,i⟩ => Fin.elim0 i
  left_inv _ := rfl
  right_inv row := by
    rcases row with ⟨block,i⟩
    cases block with
    | linear => rfl
    | left | right | output => exact Fin.elim0 i

/-- Physical row zero is `u`, one is `m`, and `i+2` is witness row `i`.
The final proximity row receives coefficient one and is absent here. -/
def physicalRows (nw nq : ℕ) (linear : nq = 0) : Fin (nw+2) ≃ BatchedRow nw nq :=
  (((finCongr (by omega) : Fin (nw+2) ≃ Fin (2+nw)).trans finSumFinEquiv.symm).trans
    ((masks.sumCongr (core nw)).trans (Equiv.sumComm _ _))).trans
    (Equiv.cast (by rw [linear]))

/-- The retained algebraic row enumeration stays internal. Only this
explicit reindexing determines where a transcript sample is consumed. -/
def rowOrder (nw nq : ℕ) (linear : nq = 0) : Fin (rowCount nw nq) ≃ Fin (nw+2) :=
  (rowEquiv nw nq).trans (physicalRows nw nq linear).symm

@[simp] theorem rowOrder_u (nw nq : ℕ) (linear : nq = 0) :
    (rowOrder nw nq linear (maskIndex .vCoefficient)).val = 0 := by
  subst nq
  simp [rowOrder,maskIndex,physicalRows,masks]

@[simp] theorem rowOrder_m (nw nq : ℕ) (linear : nq = 0) :
    (rowOrder nw nq linear (maskIndex .zRCoefficient)).val = 1 := by
  subst nq
  simp [rowOrder,maskIndex,physicalRows,masks]

@[simp] theorem rowOrder_witness (nw nq : ℕ) (linear : nq = 0) (i : Fin nw) :
    (rowOrder nw nq linear (coreIndex .linear i)).val = i.val+2 := by
  subst nq
  simp [rowOrder,coreIndex,physicalRows,core]

/-- Sample coordinates within one field, before conversion to polynomials. -/
abbrev Samples (F : Type) (count rows degree : ℕ) :=
  (Fin count → F) × (Fin (rows+2) → Fin (degree+1) → F)

def size (count rows degree : ℕ) := count+(rows+2)*(degree+1)

/-- Affine scalars precede row-major polynomial evaluations. -/
def coordinate (count rows degree : ℕ) :
    (Fin count ⊕ (Fin (rows+2) × Fin (degree+1))) ≃ Fin (size count rows degree) :=
  ((Equiv.refl (Fin count)).sumCongr finProdFinEquiv).trans finSumFinEquiv

@[simp] theorem coordinate_affine (count rows degree : ℕ) (i : Fin count) :
    (coordinate count rows degree (.inl i)).val = i.val := rfl

@[simp] theorem coordinate_polynomial (count rows degree : ℕ)
    (row : Fin (rows+2)) (i : Fin (degree+1)) :
    (coordinate count rows degree (.inr (row,i))).val = count+row.val*(degree+1)+i.val := by
  change count+(i.val+(degree+1)*row.val) = count+row.val*(degree+1)+i.val
  ring

/-- A bijective flattening fixes the exact sample order without imposing
fixed byte offsets on a rejection sampler. -/
def unflatten (F : Type) (count rows degree : ℕ) :
    (Fin (size count rows degree) → F) ≃ Samples F count rows degree :=
  (Equiv.arrowCongr (coordinate count rows degree).symm (Equiv.refl F)).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).trans
      ((Equiv.refl _).prodCongr (Equiv.curry _ _ _)))

/-- Convert an explicit physical array of evaluation samples to the
retained challenge coordinates. This bijection also preserves uniformity. -/
def polynomialsEquiv {F : Type} [Field F] [DecidableEq F]
    (nw nq : ℕ) (linear : nq = 0) {d : ℕ} (nodes : Fin d → F)
    (injective : Function.Injective nodes) :
    (Fin (nw+2) → Fin d → F) ≃ (Fin (rowCount nw nq) → Polynomial.degreeLT F d) where
  toFun samples row := (Response.evaluationEquiv F nodes injective).symm
    (samples (rowOrder nw nq linear row))
  invFun coin row := Response.evaluationEquiv F nodes injective
    (coin ((rowOrder nw nq linear).symm row))
  left_inv samples := by
    funext row
    simp only [Equiv.apply_symm_apply]
  right_inv coin := by
    funext row
    simp only [Equiv.symm_apply_apply]

theorem polynomialsEquiv_eval {F : Type} [Field F] [DecidableEq F]
    (nw nq : ℕ) (linear : nq = 0) {d : ℕ} (nodes : Fin d → F)
    (injective : Function.Injective nodes) (samples : Fin (nw+2) → Fin d → F)
    (row : Fin (rowCount nw nq)) (i : Fin d) :
    ((polynomialsEquiv nw nq linear nodes injective samples row).val).eval (nodes i) =
      samples (rowOrder nw nq linear row) i :=
  Response.evaluationEquiv_eval F nodes injective _ i

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {k s n t : ℕ}
variable (P : FieldBackend F k s n t)

include P in
omit [Fintype F] [DecidableEq F] in
/-- A nonempty ordinary row dimension leaves enough oracle nodes for the
batching polynomial. This is an existing geometry check. -/
theorem prefixFits (positive : 0 < k) : P.backend.s+1 ≤ P.backend.n := by
  have hp := P.backend.primary_le
  have hk := P.dimension
  omega

def node (positive : 0 < k) (i : Fin (P.backend.s+1)) : F :=
  P.backend.domain.point (codePosition ⟨i.val,lt_of_lt_of_le i.isLt (prefixFits P positive)⟩)

omit [Fintype F] [DecidableEq F] in
theorem node_injective (positive : 0 < k) : Function.Injective (node P positive) := by
  intro i j h
  have he := P.backend.domain.injective h
  exact Fin.ext (congrArg (fun z : Position P.backend.r P.backend.w P.backend.n =>
    match z with | .inl _ => 0 | .inr i => i.val) he)

/-- Invertible sample-to-coin conversion. Affine coordinates already have
the canonical `Fin count` equation order constructed by StatementCompiler. -/
def samplesEquiv (count : ℕ) (positive : 0 < k) :
    Samples F count P.backend.nw P.backend.s ≃ (P.indexed count).participant.Coin :=
  (Equiv.refl _).prodCongr
    (polynomialsEquiv P.backend.nw P.backend.nq P.linearOnly
      (node P positive) (node_injective P positive))

def fieldEquiv (count : ℕ) (positive : 0 < k) :
    (Fin (size count P.backend.nw P.backend.s) → F) ≃ (P.indexed count).participant.Coin :=
  (unflatten F count P.backend.nw P.backend.s).trans (samplesEquiv P count positive)

/-- All field draws belong to one uninterrupted reading phase. `start` and
the returned end cursor count field draws, whose byte consumption can vary. -/
def read (count : ℕ) (positive : 0 < k) (sample : ℕ → F) (start : ℕ) :
    (P.indexed count).participant.Coin × ℕ :=
  (fieldEquiv P count positive (fun i => sample (start+i.val)),
    start+size count P.backend.nw P.backend.s)

@[simp] theorem read_affine (count : ℕ) (positive : 0 < k) (sample : ℕ → F)
    (start : ℕ) (i : Fin count) :
    (read P count positive sample start).1.1 i = sample (start+i.val) := rfl

theorem read_polynomial_eval (count : ℕ) (positive : 0 < k) (sample : ℕ → F)
    (start : ℕ) (row : Fin (rowCount P.backend.nw P.backend.nq))
    (i : Fin (P.backend.s+1)) :
    ((read P count positive sample start).1.2 row).val.eval
      (node P positive i) = sample (start+count+
        (rowOrder P.backend.nw P.backend.nq P.linearOnly row).val*(P.backend.s+1)+i.val) := by
  change ((Response.evaluationEquiv F (node P positive) (node_injective P positive)).symm
    (fun j => sample (start+(coordinate count P.backend.nw P.backend.s
      (.inr (rowOrder P.backend.nw P.backend.nq P.linearOnly row,j))).val))).val.eval _ = _
  rw [Response.evaluationEquiv_eval]
  congr 1
  rw [coordinate_polynomial]
  omega

theorem read_u_eval (count : ℕ) (positive : 0 < k) (sample : ℕ → F)
    (start : ℕ) (i : Fin (P.backend.s+1)) :
    ((read P count positive sample start).1.2 (maskIndex (nw := P.backend.nw) (nq := P.backend.nq) .vCoefficient)).val.eval
      (node P positive i) = sample (start+count+i.val) := by
  rw [read_polynomial_eval,rowOrder_u,Nat.zero_mul,Nat.add_zero]

theorem read_m_eval (count : ℕ) (positive : 0 < k) (sample : ℕ → F)
    (start : ℕ) (i : Fin (P.backend.s+1)) :
    ((read P count positive sample start).1.2 (maskIndex (nw := P.backend.nw) (nq := P.backend.nq) .zRCoefficient)).val.eval
      (node P positive i) = sample (start+count+(P.backend.s+1)+i.val) := by
  rw [read_polynomial_eval,rowOrder_m,Nat.one_mul]

theorem read_witness_eval (count : ℕ) (positive : 0 < k) (sample : ℕ → F)
    (start : ℕ) (row : Fin P.backend.nw) (i : Fin (P.backend.s+1)) :
    ((read P count positive sample start).1.2 (coreIndex (nw := P.backend.nw) (nq := P.backend.nq) .linear row)).val.eval
      (node P positive i) = sample (start+count+(row.val+2)*(P.backend.s+1)+i.val) := by
  rw [read_polynomial_eval,rowOrder_witness]

section Joint
variable {N : Type} [Field N] [Fintype N] [DecidableEq N]
variable (R : FieldBackend N k s n t)

/-- Both full field blocks are bijective encodings of the one joint coin.
The raw blocks remain typed; fields are never converted through each other. -/
def pairEquiv (countB countN : ℕ) (positive : 0 < k) :
    ((Fin (size countB P.backend.nw P.backend.s) → F) ×
      (Fin (size countN R.backend.nw R.backend.s) → N)) ≃
      JointResponse.Coin (P.indexed countB).participant (R.indexed countN).participant :=
  (fieldEquiv P countB positive).prodCongr (fieldEquiv R countN positive)

/-- Uniform raw evaluation vectors give uniform formal coins. The
interpolation/physical-order adapter introduces no sampling correction. -/
def decoder {C : Type} [Fintype C] (countB countN : ℕ) (positive : 0 < k)
    (raw : BalancedDecoder C
      ((Fin (size countB P.backend.nw P.backend.s) → F) ×
        (Fin (size countN R.backend.nw R.backend.s) → N))) :
    BalancedDecoder C (JointResponse.Coin (P.indexed countB).participant (R.indexed countN).participant) where
  decode answer := pairEquiv P R countB countN positive (raw.decode answer)
  fiber := raw.fiber
  fiber_bound coin := by
    convert raw.fiber_bound ((pairEquiv P R countB countN positive).symm coin) using 1
    congr 1
    ext answer
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Equiv.apply_eq_iff_eq_symm_apply]
  balanced := by
    rw [← Fintype.card_congr (pairEquiv P R countB countN positive)]
    exact raw.balanced

/-- `joint.rs` finishes the first field before starting the second. Cursors
count typed field draws; there is no assumption that these have equal byte
widths or that rejection consumes a fixed number of bytes. -/
def jointRead (countB countN : ℕ) (positive : 0 < k)
    (sampleB : ℕ → F) (sampleN : ℕ → N) (start : ℕ) :
    JointResponse.Coin (P.indexed countB).participant (R.indexed countN).participant × ℕ :=
  let first := read P countB positive sampleB start
  let second := read R countN positive sampleN first.2
  ((first.1,second.1),second.2)

@[simp] theorem jointRead_end (countB countN : ℕ) (positive : 0 < k)
    (sampleB : ℕ → F) (sampleN : ℕ → N) (start : ℕ) :
    (jointRead P R countB countN positive sampleB sampleN start).2 =
      start+size countB P.backend.nw P.backend.s+size countN R.backend.nw R.backend.s := rfl

@[simp] theorem jointRead_binary_affine (countB countN : ℕ) (positive : 0 < k)
    (sampleB : ℕ → F) (sampleN : ℕ → N) (start : ℕ) (i : Fin countB) :
    (jointRead P R countB countN positive sampleB sampleN start).1.1.1 i = sampleB (start+i.val) := rfl

@[simp] theorem jointRead_prime_affine (countB countN : ℕ) (positive : 0 < k)
    (sampleB : ℕ → F) (sampleN : ℕ → N) (start : ℕ) (i : Fin countN) :
    (jointRead P R countB countN positive sampleB sampleN start).1.2.1 i =
      sampleN (start+size countB P.backend.nw P.backend.s+i.val) := rfl

/-- The cursor reader and the typed raw-block codec are the same coin
construction. This records binary-before-prime consumption explicitly. -/
theorem jointRead_coin (countB countN : ℕ) (positive : 0 < k)
    (sampleB : ℕ → F) (sampleN : ℕ → N) (start : ℕ) :
    (jointRead P R countB countN positive sampleB sampleN start).1 =
      pairEquiv P R countB countN positive
        (fun i => sampleB (start+i.val),
          fun i => sampleN (start+size countB P.backend.nw P.backend.s+i.val)) := rfl

end Joint

end LfzkV2.Current.BackendChallenges
